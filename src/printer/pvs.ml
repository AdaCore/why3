(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(** PVS printer *)

(*
QUESTIONS FOR THE PVS TEAM
--------------------------
  * tuples (there are native tuples in Why3)

    - in Why3, we have 0-tuples as well, i.e. a type "()" with a single
      value also written "()"

      currently, I'm using

         tuple0: DATATYPE BEGIN Tuple0: Tuple0? END tuple0

    - it looks like PVS does not allow me to perform pattern-matching (CASES)
      on tuples i.e something like

        CASES x1 OF
         (x2, x3): ...
        ENDCASES

      so I'm doing that instead:

        LET x2 = x1`1, x3 = x1`2 IN ...

  * pattern-matching

    - By mistake, I used _ as a catch-all in a CASES expressions
      (as in ML and in Why3) and it made PVS go wild!

  * I intend to use the script "proveit" to replay PVS proofs (when they exist).
    What is the canonical way to check that all proofs have indeed been
    successfully replayed? (exit code, grep on proveit's output, etc.)

TODO
----
  * driver
    - maps: const

*)

open Format
open Pp
open Util
open Ident
open Ty
open Term
open Decl
open Printer

let black_list =
  [ "and"; "conjecture"; "fact"; "let"; "table";
    "andthen"; "containing"; "false"; "library"; "then";
    "array"; "conversion"; "forall"; "macro"; "theorem";
    "assuming"; "conversion+"; "formula"; "measure"; "theory";
    "assumption"; "conversion-"; "from"; "nonempty"; "type"; "true";
    "auto"; "rewrite"; "corollary"; "function"; "not"; "type";
    "auto"; "rewrite+";" datatype"; "has"; "type"; "o"; "type+";
    "auto"; "rewrite-"; "else"; "if"; "obligation"; "var";
    "axiom"; "elsif"; "iff"; "of"; "when";
    "begin"; "end"; "implies"; "or"; "where";
    "but"; "endassuming"; "importing"; "orelse"; "with";
    "by"; "endcases"; "in"; "postulate"; "xor";
    "cases"; "endcond"; "inductive"; "proposition";
    "challenge"; "endif"; "judgement"; "recursive";
    "claim"; "endtable"; "lambda"; "sublemma";
    "closure"; "exists"; "law"; "subtypes";
    "cond"; "exporting"; "lemma"; "subtype"; "of";
    (* PVS prelude *)
    "even";
    (* introduced by Why3 *)
    "tuple0"; ]

let fresh_printer () =
  let isanitize = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer black_list ~sanitizer:isanitize

let iprinter =
  let isanitize = sanitizer char_to_lalpha char_to_lalnumus in
  create_ident_printer black_list ~sanitizer:isanitize

let forget_all () = forget_all iprinter

let tv_set = ref Sid.empty

(* type variables *)

let print_tv fmt tv =
  let n = id_unique iprinter tv.tv_name in
  fprintf fmt "%s" n

let print_tv_binder fmt tv =
  tv_set := Sid.add tv.tv_name !tv_set;
  let n = id_unique iprinter tv.tv_name in
  fprintf fmt "%s:TYPE" n

let print_params_list fmt = function
  | [] -> ()
  | tvl -> fprintf fmt "[%a]" (print_list comma print_tv_binder) tvl

let print_params fmt stv =
  print_params_list fmt (Stv.elements stv)

let forget_tvs () =
  Sid.iter (forget_id iprinter) !tv_set;
  tv_set := Sid.empty

(* logic variables *)
let print_vs fmt vs =
  let n = id_unique iprinter vs.vs_name in
  fprintf fmt "%s" n

let forget_var vs = forget_id iprinter vs.vs_name

let print_ts fmt ts =
  fprintf fmt "%s" (id_unique iprinter ts.ts_name)

let print_ls fmt ls =
  fprintf fmt "%s" (id_unique iprinter ls.ls_name)

let print_pr fmt pr =
  fprintf fmt "%s" (id_unique iprinter pr.pr_name)

let print_name fmt id =
  fprintf fmt "%% Why3 %s@\n" (id_unique iprinter id)

(* info *)

type info = {
  info_syn : syntax_map;
  symbol_printers : (string * Theory.theory * ident_printer) Mid.t;
  realization : bool;
}

let print_path = print_list (constant_string ".") string

let print_id fmt id = string fmt (id_unique iprinter id)

let print_id_real info fmt id =
        try let path,th,ipr = Mid.find id info.symbol_printers in
        fprintf fmt "%s.%s.%s"
          path
          th.Theory.th_name.id_string
          (id_unique ipr id)
        with Not_found -> print_id fmt id

let print_ls_real info fmt ls = print_id_real info fmt ls.ls_name
let print_ts_real info fmt ts = print_id_real info fmt ts.ts_name
let print_pr_real info fmt pr = print_id_real info fmt pr.pr_name

(** Types *)

let rec print_ty info fmt ty = match ty.ty_node with
  | Tyvar v -> print_tv fmt v
  | Tyapp (ts, tl) when is_ts_tuple ts ->
      begin match tl with
        | []  -> fprintf fmt "tuple0"
        | [ty] -> print_ty info fmt ty
        | _   -> fprintf fmt "[%a]" (print_list comma (print_ty info)) tl
      end
  | Tyapp (ts, tl) ->
      begin match query_syntax info.info_syn ts.ts_name with
        | Some s -> syntax_arguments s (print_ty info) fmt tl
        | None -> begin
          match tl with
            | []  -> (print_ts_real info) fmt ts
            | l   -> fprintf fmt "%a[%a]" (print_ts_real info) ts
                       (print_list comma (print_ty info)) l
        end
      end

(* can the type of a value be derived from the type of the arguments? *)
let unambig_fs fs =
  let rec lookup v ty = match ty.ty_node with
    | Tyvar u when tv_equal u v -> true
    | _ -> ty_any (lookup v) ty
  in
  let lookup v = List.exists (lookup v) fs.ls_args in
  let rec inspect ty = match ty.ty_node with
    | Tyvar u when not (lookup u) -> false
    | _ -> ty_all inspect ty
  in
  inspect (of_option fs.ls_value)

(** Patterns, terms, and formulas *)

let lparen_l fmt () = fprintf fmt "@ ("
let lparen_r fmt () = fprintf fmt "(@,"
let print_paren_l fmt x =
  print_list_delim ~start:lparen_l ~stop:rparen ~sep:comma fmt x
let print_paren_r fmt x =
  print_list_delim ~start:lparen_r ~stop:rparen ~sep:comma fmt x

let arrow fmt () = fprintf fmt "@ -> "
let print_arrow_list fmt x = print_list arrow fmt x
let print_space_list fmt x = print_list space fmt x
let print_comma_list fmt x = print_list comma fmt x
let print_or_list fmt x = print_list (fun fmt () -> fprintf fmt " OR@\n") fmt x
let comma_newline fmt () = fprintf fmt ",@\n"

let rec print_pat info fmt p = match p.pat_node with
  | Pvar v ->
      print_vs fmt v
  | Papp (cs, _) when is_fs_tuple cs ->
      assert false (* is handled earlier in print_term/fmla *)
  | Papp (cs, pl) ->
      begin match query_syntax info.info_syn cs.ls_name with
        | Some s -> syntax_arguments s (print_pat info) fmt pl
        | _ when pl = [] -> (print_ls_real info) fmt cs
        | _ -> fprintf fmt "%a(%a)"
          (print_ls_real info) cs (print_list comma (print_pat info)) pl
      end
  | Pas _ | Por _ ->
      assert false (* compile_match must have taken care of that *)
  | Pwild ->
      assert false (* is handled in print_branches *)

let print_vsty_nopar info fmt v =
  fprintf fmt "%a:%a" print_vs v (print_ty info) v.vs_ty

let print_vsty info fmt v =
  fprintf fmt "(%a)" (print_vsty_nopar info) v

let is_tuple0_ty = function
  | Some { ty_node = Tyapp (ts, _) } -> ts_equal ts (ts_tuple 0)
  | Some _ | None -> false

let is_tuple_ty = function
  | Some { ty_node = Tyapp (ts, _) } -> is_ts_tuple ts
  | Some _ | None -> false

let print_binop fmt = function
  | Tand -> fprintf fmt "AND"
  | Tor -> fprintf fmt "OR"
  | Timplies -> fprintf fmt "=>"
  | Tiff -> fprintf fmt "<=>"

(* TODO: labels are lost, but we could print them as "% label \n",
   it would result in an ugly output, though *)
let print_label _fmt (_l,_) = () (*fprintf fmt "(*%s*)" l*)

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

let rec print_term info fmt t = print_lrterm false false info fmt t
and     print_fmla info fmt f = print_lrfmla false false info fmt f
and print_opl_term info fmt t = print_lrterm true  false info fmt t
and print_opl_fmla info fmt f = print_lrfmla true  false info fmt f
and print_opr_term info fmt t = print_lrterm false true  info fmt t
and print_opr_fmla info fmt f = print_lrfmla false true  info fmt f

and print_lrterm opl opr info fmt t = match t.t_label with
  | _ -> print_tnode opl opr info fmt t

and print_lrfmla opl opr info fmt f = match f.t_label with
  | _ -> print_fnode opl opr info fmt f

and print_tnode opl opr info fmt t = match t.t_node with
  | Tvar v ->
      print_vs fmt v
  | Tconst c ->
      let number_format = {
          Print_number.long_int_support = true;
          Print_number.dec_int_support = Print_number.Number_custom "%s";
          Print_number.hex_int_support = Print_number.Number_unsupported;
          Print_number.oct_int_support = Print_number.Number_unsupported;
          Print_number.bin_int_support = Print_number.Number_unsupported;
          Print_number.def_int_support = Print_number.Number_unsupported;
          Print_number.dec_real_support = Print_number.Number_unsupported;
          Print_number.hex_real_support = Print_number.Number_unsupported;
          Print_number.frac_real_support = Print_number.Number_custom
            (Print_number.PrintFracReal
               ("%s", "(%s * %s)", "(%s / %s)"));
          Print_number.def_real_support = Print_number.Number_unsupported;
        }
      in
      Print_number.print number_format fmt c
  | Tif (f, t1, t2) ->
      fprintf fmt "IF %a@ THEN %a@ ELSE %a ENDIF"
        (print_fmla info) f (print_term info) t1 (print_opl_term info) t2
  | Tlet (t1, tb) ->
      let v,t2 = t_open_bound tb in
      fprintf fmt (protect_on opr "LET %a =@ %a IN@ %a")
        print_vs v (print_opl_term info) t1 (print_opl_term info) t2;
      forget_var v
  | Tcase (t, [b]) when is_tuple0_ty t.t_ty ->
      let _,t = t_open_branch b in
      print_term info fmt t
  | Tcase (t, [b]) when is_tuple_ty t.t_ty ->
      let p,t1 = t_open_branch b in
      fprintf fmt "@[<hov 4>LET %a IN@ %a@]"
        (print_tuple_pat info t) p (print_term info) t1;
      Svs.iter forget_var p.pat_vars
  | Tcase (t, bl) ->
      fprintf fmt "CASES %a OF@\n@[<hov>%a@]@\nENDCASES"
        (print_term info) t (print_branches print_term info) bl
  | Teps fb ->
      let v,f = t_open_bound fb in
      fprintf fmt (protect_on opr "epsilon(LAMBDA (%a):@ %a)")
        (print_vsty_nopar info) v (print_opl_fmla info) f;
      forget_var v
  | Tapp (fs, []) when is_fs_tuple fs ->
      fprintf fmt "Tuple0"
  | Tapp (fs, pl) when is_fs_tuple fs ->
      fprintf fmt "%a" (print_paren_r (print_term info)) pl
  | Tapp (fs, tl) ->
    begin match query_syntax info.info_syn fs.ls_name with
      | Some s ->
          syntax_arguments s (print_term info) fmt tl
      | _ ->
          let no_cast = unambig_fs fs in
          begin match tl with
            | [] when no_cast ->
              fprintf fmt "%a" (print_ls_real info) fs
            | [] ->
              fprintf fmt "(%a :: %a)"
                (print_ls_real info) fs (print_ty info) (t_type t)
            | _ when no_cast ->
              fprintf fmt "%a(%a)" (print_ls_real info) fs
                (print_comma_list (print_term info)) tl
            |_ ->
              fprintf fmt (protect_on opl "(%a(%a) :: %a)")
                (print_ls_real info) fs
                (print_comma_list (print_term info)) tl
                (print_ty info) (t_type t)
          end
    end
  | Tquant _ | Tbinop _ | Tnot _ | Ttrue | Tfalse ->
      raise (TermExpected t)

and print_fnode opl opr info fmt f = match f.t_node with
  | Tquant (Tforall, fq) ->
      let vl,_tl,f = t_open_quant fq in
      fprintf fmt (protect_on opr "FORALL (%a):@ %a")
        (print_comma_list (print_vsty_nopar info)) vl
        (* (print_tl info) tl *) (print_fmla info) f;
      List.iter forget_var vl
  | Tquant (Texists,fq) ->
      let vl,_tl,f = t_open_quant fq in
      let rec aux fmt vl = match vl with
        | [] ->
          print_fmla info fmt f
        | v :: vr ->
          fprintf fmt (protect_on opr "EXISTS (%a):@ %a")
            (print_vsty_nopar info) v aux vr
      in
      aux fmt vl;
      List.iter forget_var vl
  | Ttrue ->
      fprintf fmt "TRUE"
  | Tfalse ->
      fprintf fmt "FALSE"
  | Tbinop (b, f1, f2) ->
      fprintf fmt (protect_on (opl || opr) "%a %a@ %a")
        (print_opr_fmla info) f1 print_binop b (print_opl_fmla info) f2
  | Tnot f ->
      fprintf fmt (protect_on opr "NOT %a") (print_opl_fmla info) f
  | Tlet (t, f) ->
      let v,f = t_open_bound f in
      fprintf fmt (protect_on opr "LET %a =@ %a IN@ %a")
        print_vs v (print_opl_term info) t (print_opl_fmla info) f;
      forget_var v
  | Tcase (t, [b]) when is_tuple0_ty t.t_ty ->
      let _,f = t_open_branch b in
      print_fmla info fmt f
  | Tcase (t, [b]) when is_tuple_ty t.t_ty ->
      let p,f = t_open_branch b in
      fprintf fmt "@[<hov 4>LET %a IN@ %a@]"
        (print_tuple_pat info t) p (print_fmla info) f;
      Svs.iter forget_var p.pat_vars
  | Tcase (t, bl) ->
      fprintf fmt "CASES %a OF@\n@[<hov>%a@]@\nENDCASES"
        (print_term info) t (print_branches print_fmla info) bl
  | Tif (f1, f2, f3) ->
      fprintf fmt (protect_on opr "IF %a@ THEN %a@ ELSE %a ENDIF")
        (print_fmla info) f1 (print_fmla info) f2 (print_opl_fmla info) f3
  | Tapp (ps, tl) ->
    begin match query_syntax info.info_syn ps.ls_name with
      | Some s ->
          syntax_arguments s (print_term info) fmt tl
      | None when tl = [] ->
          fprintf fmt "%a" (print_ls_real info) ps
      | None ->
          fprintf fmt "%a(%a)" (print_ls_real info) ps
            (print_comma_list (print_term info)) tl
    end
  | Tvar _ | Tconst _ | Teps _ ->
      raise (FmlaExpected f)

and print_tuple_pat info t fmt p =
  let unvar p = match p.pat_node with
    | Pvar vs -> vs
    | _ -> assert false (*TODO?*)
  in
  let l = match p.pat_node with
    | Papp (_, pl) -> List.map unvar pl | _ -> assert false
  in
  let i = ref 0 in
  let print fmt vs =
    incr i;
    fprintf fmt "%a = %a`%d"
      (print_vsty_nopar info) vs (print_term info) t !i
  in
  print_comma_list print fmt l

and print_branch print info fmt br =
  let p,t = t_open_branch br in
  fprintf fmt "@[<hov 4> %a:@ %a@]"
    (print_pat info) p (print info) t;
  Svs.iter forget_var p.pat_vars

and print_branches ?(first=true) print info fmt = function
  | [] ->
      ()
  | br :: bl ->
      let p, t = t_open_branch br in
      begin match p.pat_node with
        | Pwild ->
            assert (bl = []);
            if not first then fprintf fmt "@\n";
            fprintf fmt "@[<hov 4>ELSE@ %a@]" (print info) t
        | _ ->
            if not first then fprintf fmt ",@\n";
            fprintf fmt "@[<hov 4> %a:@ %a@]"
              (print_pat info) p (print info) t;
            Svs.iter forget_var p.pat_vars;
            print_branches ~first:false print info fmt bl
      end

let print_expr info fmt =
  TermTF.t_select (print_term info fmt) (print_fmla info fmt)

(** Declarations *)

let print_constr info _ts fmt (cs,_) =
  match cs.ls_args with
    | [] ->
        fprintf fmt "@[<hov 4>%a: %a?@]" print_ls cs print_ls cs
    | l ->
        let sid = ref Sid.empty in
        let print fmt ty =
	  let n = id_register (id_fresh "x") in
	  sid := Sid.add n !sid;
	  fprintf fmt "%s:%a" (id_unique iprinter n) (print_ty info) ty
	in
        fprintf fmt "@[<hov 4>%a(%a): %a?@]" print_ls cs
          (print_comma_list print) l print_ls cs;
        Sid.iter (forget_id iprinter) !sid

let ls_ty_vars ls =
  let ty_vars_args = List.fold_left Ty.ty_freevars Stv.empty ls.ls_args in
  let ty_vars_value = option_fold Ty.ty_freevars Stv.empty ls.ls_value in
  (ty_vars_args, ty_vars_value, Stv.union ty_vars_args ty_vars_value)

(*

  copy of old user scripts

*)

let clean_line s =
  let n = String.length s in
  if n >= 2 && s.[0] = ' ' && s.[1] = ' ' then String.sub s 2 (n - 2) else s

(***
let copy_user_script begin_string end_string ch fmt =
  fprintf fmt "%s@\n" begin_string;
  try
    while true do
      let s = input_line ch in
      let s = clean_line s in
      fprintf fmt "%s@\n" s;
      if s = end_string then raise Exit
    done
  with
    | Exit -> fprintf fmt "@\n"
    | End_of_file -> fprintf fmt "%s@\n@\n" end_string

let proof_begin = "% YOU MAY EDIT THE PROOF BELOW"
let proof_end = "% DO NOT EDIT BELOW"
let context_begin = "% YOU MAY EDIT THE CONTEXT BELOW"
let context_end = "% DO NOT EDIT BELOW"

(* current kind of script in an old file *)
type old_file_state = InContext | InProof | NoWhere

let copy_proof s ch fmt =
  copy_user_script proof_begin proof_end ch fmt;
  s := NoWhere

let copy_context s ch fmt =
  copy_user_script context_begin context_end ch fmt;
  s := NoWhere

let lookup_context_or_proof old_state old_channel =
  match !old_state with
    | InProof | InContext -> ()
    | NoWhere ->
        let rec loop () =
          let s = input_line old_channel in
	  let s = clean_line s in
          if s = proof_begin then old_state := InProof
	  else if s = context_begin then old_state := InContext
	  else loop ()
        in
        try loop ()
        with End_of_file -> ()

let read_old_script _ch =
  []
 ****)

type chunk =
  | Edition of string * string (* name and contents *)
  | Other of string            (* contents *)

let re_theory = Str.regexp "[^ :]+: THEORY"
let re_begin = Str.regexp " BEGIN"
let re_why3 = Str.regexp "% Why3 \\([^ ]+\\)"

let read_old_script ch =
  let chunks = ref [] in
  let buffer = Buffer.create 1024 in
  let rec read_line () =
    let s = input_line ch in
    let s = clean_line s in
    if Str.string_match re_theory s 0 || Str.string_match re_begin s 0
    then read_line () else s
  in
  let rec read ?name () =
    let s = read_line () in
    if s = "" then begin
      new_chunk ?name (); read ()
    end else if Str.string_match re_why3 s 0 then begin
      new_chunk ?name ();
      let name = Str.matched_group 1 s in
      read ~name ()
    end else begin
      if Buffer.length buffer > 0 then Buffer.add_string buffer "\n  ";
      Buffer.add_string buffer s;
      read ?name ()
    end
  and new_chunk ?name () =
    let s = Buffer.contents buffer in
    Buffer.clear buffer;
    match s, name with
      | "", _ | _, Some "tuple0" -> ()
      | _, None -> chunks := Other s :: !chunks
      | _, Some n -> chunks := Edition (n, s) :: !chunks
  in
  try read () with End_of_file -> List.rev !chunks
  (* note: the very last chunk is purposely ignored, as it is "END th" *)

(* Output all the Other entries of the script that occur before the
   location of name. Modify the script by removing the name entry and all
   these outputs. Return the user content. *)
let output_till_statement fmt script name =
  let print i =
    let rec aux acc = function
      | h :: l when h == i ->
          let l = match l with Other "" :: l -> l | _ -> l in
          script := List.rev_append acc l
      | Other o :: l -> fprintf fmt "%s@\n@\n" o; aux acc l
      | h :: l -> aux (h :: acc) l
      | [] -> assert false
    in
    aux [] !script
  in
  let rec find = function
    | Edition (n,_) as o :: _ when n = name -> print o; Some o
    | [] -> None
    | _ :: t -> find t
  in
  find !script

let comment_out s =
  Str.global_replace (Str.regexp "\n") "\n  % " s

let output_remaining fmt cl =
  let print = function
    | Edition (n, c) ->
        fprintf fmt "%% Obsolete chunk %s@\n%% %s@\n" n (comment_out c)
    | Other c ->
        fprintf fmt "%% %s@\n" (comment_out c)
  in
  List.iter print cl

let print_type_decl ~prev info fmt ts = ignore (prev);
  if not (is_ts_tuple ts) then begin
    print_name fmt ts.ts_name;
    match ts.ts_def with
    | None ->
        fprintf fmt "@[<hov 2>%a%a: TYPE@]@\n@\n"
          print_ts ts print_params_list ts.ts_args
          (* (realization ~old ~def:true) info.realization *)
    | Some ty ->
        fprintf fmt "@[<hov 2>%a%a: TYPE =@ %a@]@\n@\n"
          print_ts ts print_params_list ts.ts_args
          (print_ty info) ty
  end

let print_type_decl ~prev info fmt ts =
  if not (Mid.mem ts.ts_name info.info_syn) then begin
    print_type_decl ~prev info fmt ts;
    forget_tvs ()
  end

let print_data_decl info fmt (ts,csl) =
  if not (is_ts_tuple ts) then begin
    print_name fmt ts.ts_name;
    fprintf fmt
      "@[<hov 1>%a%a: DATATYPE@\n@[<hov 1>BEGIN@\n%a@]@\nEND %a@]@\n@\n"
      print_ts ts print_params_list ts.ts_args
      (print_list newline (print_constr info ts)) csl print_ts ts
  end

let print_data_decl info fmt d =
  if not (Mid.mem (fst d).ts_name info.info_syn) then begin
    print_data_decl info fmt d;
    forget_tvs ()
  end

let print_ls_type info fmt = function
  | None -> fprintf fmt "bool"
  | Some ty -> print_ty info fmt ty

let print_param_decl ~prev info fmt ls =
  ignore prev;
  let _ty_vars_args, _ty_vars_value, all_ty_params = ls_ty_vars ls in
  print_name fmt ls.ls_name;
  match ls.ls_args with
    | [] ->
        fprintf fmt "@[<hov 2>%a%a: %a@]@\n@\n"
          print_ls ls print_params all_ty_params
          (print_ls_type info) ls.ls_value
    | _ ->
        fprintf fmt "@[<hov 2>%a%a: [%a -> %a]@]@\n@\n"
          print_ls ls print_params all_ty_params
          (print_comma_list (print_ty info)) ls.ls_args
          (print_ls_type info) ls.ls_value
          (* (realization ~old ~def:true) info.realization *)

let print_param_decl ~prev info fmt ls =
  if not (Mid.mem ls.ls_name info.info_syn) then
    (print_param_decl ~prev info fmt ls; forget_tvs ())

let print_logic_decl ~prev info fmt (ls,ld) =
  ignore prev;
  let _ty_vars_args, _ty_vars_value, all_ty_params = ls_ty_vars ls in
  let vl,e = open_ls_defn ld in
  print_name fmt ls.ls_name;
  fprintf fmt "@[<hov 2>%a%a(%a): %a =@ %a@]@\n@\n"
    print_ls ls print_params all_ty_params
    (print_comma_list (print_vsty_nopar info)) vl
    (print_ls_type info) ls.ls_value
    (print_expr info) e;
  List.iter forget_var vl

let print_logic_decl ~prev info fmt d =
  if not (Mid.mem (fst d).ls_name info.info_syn) then
    (print_logic_decl ~prev info fmt d; forget_tvs ())

let print_recursive_decl info fmt (ls,ld) =
  let _, _, all_ty_params = ls_ty_vars ls in
  let i = match Decl.ls_defn_decrease ld with
    | [i] -> i | _ -> assert false in
  let vl,e = open_ls_defn ld in
  print_name fmt ls.ls_name;
  fprintf fmt "@[<hov 2>%a%a(%a): RECURSIVE %a =@ %a@\n"
    print_ls ls print_params all_ty_params
    (print_comma_list (print_vsty_nopar info)) vl
    (print_ls_type info) ls.ls_value
    (print_expr info) e;
  fprintf fmt "MEASURE %a BY <<@\n@]"
    print_vs (List.nth vl i);
  List.iter forget_var vl

let print_recursive_decl info fmt dl =
  let d, dl = match dl with
    | [d] -> d, []
    | d :: dl -> d, dl (* PVS does not support mutual recursion *)
    | [] -> assert false
  in
  fprintf fmt "@[<hov 2>";
  print_recursive_decl info fmt d; forget_tvs ();
  List.iter (print_recursive_decl info fmt) dl;
  fprintf fmt "@]@\n"

let print_ind info fmt (pr,f) =
  fprintf fmt "@[%% %a:@\n(%a)@]" print_pr pr (print_fmla info) f

let print_ind_decl info fmt (ps,al) =
  let _ty_vars_args, _ty_vars_value, all_ty_params = ls_ty_vars ps in
  let vl = List.map (create_vsymbol (id_fresh "z")) ps.ls_args in
  let tl = List.map t_var vl in
  let dj = Util.map_join_left (Eliminate_inductive.exi tl) t_or al in
  print_name fmt ps.ls_name;
  fprintf fmt "@[<hov 2>%a%a(%a): INDUCTIVE bool =@ @[<hov>%a@]@]@\n"
    print_ls ps print_params all_ty_params
    (print_comma_list (print_vsty_nopar info)) vl
    (print_fmla info) dj;
  fprintf fmt "@\n"

let print_ind_decl info fmt d =
  if not (Mid.mem (fst d).ls_name info.info_syn) then
    (print_ind_decl info fmt d; forget_tvs ())

let print_pkind info fmt = function
  | Paxiom when info.realization -> fprintf fmt "LEMMA"
  | Paxiom -> fprintf fmt "AXIOM"
  | Plemma -> fprintf fmt "LEMMA"
  | Pgoal  -> fprintf fmt "THEOREM"
  | Pskip  -> assert false (* impossible *)

let print_prop_decl info fmt (k,pr,f) =
  let params = t_ty_freevars Stv.empty f in
  let stt = match k with
    | Paxiom when info.realization -> "LEMMA"
    | Paxiom -> ""
    | Plemma -> "LEMMA"
    | Pgoal -> "THEOREM"
    | Pskip -> assert false (* impossible *) in
  print_name fmt pr.pr_name;
  if stt <> "" then
    fprintf fmt "@[<hov 2>%a%a: %s %a@]@\n@\n"
      print_pr pr print_params params stt
      (print_fmla info) f
  else
    fprintf fmt "@[<hov 2>%a%a: %a %a@]@\n@\n"
      print_pr pr print_params params (print_pkind info) k
      (print_fmla info) f;
  forget_tvs ()

let print_decl ~old info fmt d =
  let name = match d.d_node with
    | Dtype ts
    | Ddata ((ts, _) :: _) -> id_unique iprinter ts.ts_name
    | Dparam ls
    | Dlogic ((ls, _) :: _)
    | Dind (_, (ls,_) :: _) -> id_unique iprinter ls.ls_name
    | Dprop (_, pr, _) -> id_unique iprinter pr.pr_name
    | Ddata []
    | Dlogic []
    | Dind (_, []) -> assert false in
  let prev = output_till_statement fmt old name in
  match d.d_node with
  | Dtype ts ->
      print_type_decl ~prev info fmt ts
  | Ddata tl ->
      print_list nothing (print_data_decl info) fmt tl
  | Dparam ls ->
      print_param_decl ~prev info fmt ls
  | Dlogic [s, _ as ld] when not (Sid.mem s.ls_name d.d_syms) ->
      print_logic_decl ~prev info fmt ld
  | Dlogic ll ->
      print_recursive_decl info fmt ll
  | Dind (Ind, il) ->
      print_list nothing (print_ind_decl info) fmt il
  | Dind (Coind, _) ->
      unsupportedDecl d "PVS: coinductive definitions are not supported"
  | Dprop (_, pr, _) when Mid.mem pr.pr_name info.info_syn ->
      ()
  | Dprop pr ->
      print_prop_decl info fmt pr

let print_decls ~old info fmt dl =
  fprintf fmt "@[<hov>%a@]" (print_list nothing (print_decl ~old info)) dl

let init_printer th =
  let isanitize = sanitizer char_to_alpha char_to_alnumus in
  let pr = create_ident_printer black_list ~sanitizer:isanitize in
  Sid.iter (fun id -> ignore (id_unique pr id)) th.Theory.th_local;
  pr

let print_task env pr thpr realize ?old fmt task =
  forget_all ();
  print_prelude fmt pr;
  print_th_prelude task fmt thpr;
  (* find theories that are both used and realized from metas *)
  let realized_theories =
    Task.on_meta meta_realized (fun mid args ->
      match args with
      | [Theory.MAstr s1; Theory.MAstr s2] ->
        let f,id =
          let l = split_string_rev s1 '.' in List.rev (List.tl l),List.hd l in
        let th = Env.find_theory env f id in
        Mid.add th.Theory.th_name (th, if s2 = "" then s1 else s2) mid
      | _ -> assert false
    ) Mid.empty task in
  (* 2 cases: goal is clone T with [] or goal is a real goal *)
  let realized_theories =
    match task with
    | None -> assert false
    | Some { Task.task_decl = { Theory.td_node = Theory.Clone (th,_) }} ->
      Sid.iter (fun id -> ignore (id_unique iprinter id)) th.Theory.th_local;
      Mid.remove th.Theory.th_name realized_theories
    | _ -> realized_theories in
  let realized_theories' =
    Mid.map (fun (th,s) -> fprintf fmt "IMPORTING %a.%s@\n"
               print_path th.Theory.th_path s; th)
      realized_theories in
  let realized_symbols = Task.used_symbols realized_theories' in
  let local_decls = Task.local_decls task realized_symbols in
  (* associate a special printer to each symbol in a realized theory *)
  let symbol_printers =
    let printers =
      Mid.map (fun th ->
        let pr = fresh_printer () in
        Sid.iter (fun id -> ignore (id_unique pr id)) th.Theory.th_local;
        pr
      ) realized_theories' in
    Mid.map (fun th ->
      (snd (Mid.find th.Theory.th_name realized_theories), th,
       Mid.find th.Theory.th_name printers)
    ) realized_symbols in
  let info = {
    info_syn = get_syntax_map task;
    symbol_printers = symbol_printers;
    realization = realize;
  }
  in
  let old = ref (match old with
    | None -> []
    | Some ch -> read_old_script ch)
  in
  fprintf fmt "@[<hov 1>goal: THEORY@\n@[<hov 1>BEGIN@\n@\n";
  fprintf fmt "%% Why3 tuple0@\n";
  fprintf fmt "tuple0: DATATYPE BEGIN Tuple0: Tuple0? END tuple0@\n@\n";
  print_decls ~old info fmt local_decls;
  output_remaining fmt !old;
  fprintf fmt "@]@\nEND goal@\n@]"

let print_task_full env pr thpr ?old fmt task =
  print_task env pr thpr false ?old fmt task

let print_task_real env pr thpr ?old fmt task =
  print_task env pr thpr true  ?old fmt task

let () = register_printer "pvs" print_task_full
let () = register_printer "pvs-realize" print_task_real

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. "
End:
*)
