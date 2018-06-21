(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

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

      better: LET (x2, x3) = x1 IN ...

TODO
----
  * driver
    - maps: const

  * use proveit (same path as PVS) to replay a proof

*)

open Format
open Pp
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
    "boolean"; "bool";
    "pred"; "setof"; "exists1";
    "list"; "length"; "member"; "nth"; "append"; "reverse";
    "domain"; "range"; "graph"; "preserves"; "inverts"; "transpose";
    "restrict"; "extend"; "identity"; "eq";
    "epsilon";
    "set"; "member"; "emptyset"; "nonempty_set"; "fullset";
    "union"; "intersection"; "complement"; "difference";
    "symmetric_difference"; "every"; "some"; "singleton"; "add"; "remove";
    "choose"; "the"; "singleton_elt"; "rest"; "setofsets"; "powerset";
    "rinverse"; "rcomplement"; "runion"; "rintersection"; "image";
    "preimage"; "postcondition"; "converse";
    "number"; "number_field"; "numfield"; "nonzero_number"; "nznum";
    "real"; "nonzero_real"; "nzreal";
    "nonneg_real"; "nonpos_real"; "posreal"; "negreal"; "nnreal"; "npreal";
    "rational"; "rat"; "nonzero_rational"; "nzrat";
    "nonneg_rat"; "nonpos_rat"; "posrat"; "negrat"; "nnrat"; "nprat";
    "integer"; "int"; "nonzero_integer"; "nzint";
    "nonneg_int"; "nonpos_int"; "posint"; "negint"; "nnint"; "npint";
    "subrange"; "even_int"; "odd_int";
    "naturalnumber"; "nat"; "upto"; "below"; "succ"; "pred";
    "min"; "max"; "sgn"; "abs";
    "mod"; "divides"; "rem"; "ndiv";
    "upfrom"; "above";
    "even";
    ]

let fresh_printer () =
  let isanitize = sanitizer char_to_lalpha char_to_lalnumus in
  create_ident_printer black_list ~sanitizer:isanitize

let iprinter =
  let isanitize = sanitizer char_to_lalpha char_to_lalnumus in
  create_ident_printer black_list ~sanitizer:isanitize

let forget_all () = forget_all iprinter

let tv_set = ref Sid.empty

let thprinter =
  let isanitize = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer black_list ~sanitizer:isanitize

(* type variables *)

let print_tv fmt tv =
  let n = id_unique iprinter tv.tv_name in
  fprintf fmt "%s" n

let print_tv_binder fmt tv =
  tv_set := Sid.add tv.tv_name !tv_set;
  let n = id_unique iprinter tv.tv_name in
  fprintf fmt "%s:TYPE+" n

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

let get_th_name id =
  let s = id_unique thprinter id in
  Ident.forget_all thprinter;
  s

(* info *)

type info = {
  info_syn : syntax_map;
  symbol_printers : (string * Theory.theory * ident_printer) Mid.t;
  realization : bool;
}

let print_path = print_list (constant_string ".") string

let print_id fmt id = string fmt (id_unique iprinter id)

let print_id_real info fmt id =
  try
    let path, th, ipr = Mid.find id info.symbol_printers in
    let th = get_th_name th.Theory.th_name in
    let id = id_unique ipr id in
    if path = "" then fprintf fmt "%s.%s" th id
    else fprintf fmt "%s@@%s.%s" path th id
  with Not_found ->
    print_id fmt id

let print_ls_real info fmt ls = print_id_real info fmt ls.ls_name
let print_ts_real info fmt ts = print_id_real info fmt ts.ts_name
let print_pr_real info fmt pr = print_id_real info fmt pr.pr_name

(** Types *)

let rec print_ty info fmt ty = match ty.ty_node with
  | Tyvar v -> print_tv fmt v
  | Tyapp (ts, tl) when is_ts_tuple ts ->
      begin match tl with
        | []  -> fprintf fmt "[]"
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
  inspect (Opt.get fs.ls_value)

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
let print_attr _fmt (_l,_) = () (*fprintf fmt "(*%s*)" l*)

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

let rec print_term info fmt t = print_lrterm false false info fmt t
and     print_fmla info fmt f = print_lrfmla false false info fmt f
and print_opl_term info fmt t = print_lrterm true  false info fmt t
and print_opl_fmla info fmt f = print_lrfmla true  false info fmt f
and print_opr_term info fmt t = print_lrterm false true  info fmt t
and print_opr_fmla info fmt f = print_lrfmla false true  info fmt f

and print_lrterm opl opr info fmt t = match t.t_attrs with
  | _ -> print_tnode opl opr info fmt t

and print_lrfmla opl opr info fmt f = match f.t_attrs with
  | _ -> print_fnode opl opr info fmt f

and print_tnode opl opr info fmt t = match t.t_node with
  | Tvar v ->
      print_vs fmt v
  | Tconst c ->
      let number_format = {
          Number.long_int_support = true;
          Number.extra_leading_zeros_support = true;
          Number.negative_int_support = Number.Number_default;
          Number.dec_int_support = Number.Number_custom "%s";
          Number.hex_int_support = Number.Number_unsupported;
          Number.oct_int_support = Number.Number_unsupported;
          Number.bin_int_support = Number.Number_unsupported;
          Number.def_int_support = Number.Number_unsupported;
          Number.negative_real_support = Number.Number_default;
          Number.dec_real_support = Number.Number_unsupported;
          Number.hex_real_support = Number.Number_unsupported;
          Number.frac_real_support = Number.Number_custom
            (Number.PrintFracReal
               ("%s", "(%s * %s)", "(%s / %s)"));
          Number.def_real_support = Number.Number_unsupported;
        }
      in
      Number.print number_format fmt c
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
      fprintf fmt "()"
  | Tapp (fs, pl) when is_fs_tuple fs ->
      fprintf fmt "%a" (print_paren_r (print_term info)) pl
  | Tapp (fs, tl) ->
    begin match query_syntax info.info_syn fs.ls_name with
      | Some s ->
          syntax_arguments_typed s (print_term info) (print_ty info) t fmt tl
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
  let ty_vars_value = Opt.fold Ty.ty_freevars Stv.empty ls.ls_value in
  (ty_vars_args, ty_vars_value, Stv.union ty_vars_args ty_vars_value)

(*

  copy of old user scripts

*)

let clean_line s =
  let n = String.length s in
  if n >= 2 && s.[0] = ' ' && s.[1] = ' ' then String.sub s 2 (n - 2) else s

type contents = string list

type chunk =
  | Edition of string * contents (* name contents *)
  | Other of contents            (* contents *)

let re_blank = Str.regexp "[ ]*$"
let re_why3 = Str.regexp "% Why3 \\([^ ]+\\)"

(* Reads an old version of the file, as a list of chunks.
   Each chunk is either identified as a Why3 symbol (Edition)
   or as something else (Other).
   Note: the very last chunk is purposely ignored, as it is "END th" *)
let read_old_script ch =
  let chunks = ref [] in
  let contents = ref [] in
  let read_line () =
    let s = input_line ch in
    clean_line s
  in
  (* skip first lines, until we find a blank line *)
  begin try while true do
    let s = read_line () in if Str.string_match re_blank s 0 then raise Exit
  done with End_of_file | Exit -> () end;
  (* then read chunks *)
  let rec read ?name () =
    let s = read_line () in
    if s = "" then begin
      new_chunk ?name (); read ()
    end else if Str.string_match re_why3 s 0 then begin
      new_chunk ?name ();
      let name = Str.matched_group 1 s in
      read ~name ()
    end else begin
      contents := s :: !contents;
      read ?name ()
    end
  and new_chunk ?name () =
    let s = List.rev !contents in
    contents := [];
    match s, name with
      | ([] | [""]), _ -> ()
      | _, None -> chunks := Other s :: !chunks
      | _, Some n -> chunks := Edition (n, s) :: !chunks
  in
  try read () with End_of_file -> List.rev !chunks

(* DEBUG
let read_old_script ch =
  let cl = read_old_script ch in
  let dump = function
    | Edition (n, s) ->
        eprintf "/edited %s = @[%a@]" n (print_list newline pp_print_string) s
    | Other _s -> eprintf "/other"
  in
  List.iter dump cl; eprintf "@.";
  cl
*)

let print_contents fmt c = print_list newline pp_print_string fmt c

(* Output all the Other entries of the script that occur before the
   location of name. Modify the script by removing the name entry and all
   these outputs. Return the user content, if any. *)
let output_till_statement fmt script name =
  let print i =
    let rec aux acc = function
      | h :: l when h == i ->
          let l = match l with Other [""] :: l -> l | _ -> l in
          script := List.rev_append acc l
      | Other o :: l -> fprintf fmt "%a@\n@\n" print_contents o; aux acc l
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

let print_contents_in_comment fmt c =
  let print fmt s =
    if s = "" || s.[0] <> '%' then fprintf fmt "%% "; fprintf fmt "%s" s in
  print_list newline print fmt c

let output_remaining fmt cl =
  let print fmt = function
    | Edition (n, c) ->
        fprintf fmt "%% Obsolete chunk %s@\n%a@\n" n print_contents_in_comment c
    | Other c ->
        fprintf fmt "%a@\n" print_contents_in_comment c
  in
  print_list newline print fmt cl

(* Extracts and prints a definition from a user-edited chunk, if any;
   otherwise, prints nothing *)
let print_user_def fmt c =
  let rec scan_string _stack i s =
    let n = String.length s in
    if i = n then None else match s.[i] with
      | '=' -> Some (String.sub s i (n - i))
      | _ -> scan_string _stack (i+1) s
  in
  let rec scan_chunck _stack = function
    | [] -> ()
    | s :: c ->
        begin match scan_string _stack 0 s with
          | Some s -> fprintf fmt " %s" s; print_contents fmt c
          | None -> scan_chunck _stack c
        end
  in
  scan_chunck [] c

let realization fmt info = function
  | Some (Edition (_, c)) when info.realization -> print_user_def fmt c
  | _ -> ()

let print_type_decl ~prev info fmt ts = ignore (prev);
  if not (is_ts_tuple ts) then begin
    print_name fmt ts.ts_name;
    match ts.ts_def with
    | NoDef | Range _ | Float _ ->
        fprintf fmt "@[<hov 2>%a%a: TYPE+"
          print_ts ts print_params_list ts.ts_args;
        realization fmt info prev;
        fprintf fmt "@]@\n@\n"
    | Alias ty ->
        fprintf fmt "@[<hov 2>%a%a: TYPE+ =@ %a@]@\n@\n"
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

let create_argument ty = create_vsymbol (id_fresh "x") ty

let print_arguments info fmt = function
  | [] -> ()
  | vl -> fprintf fmt "(%a)" (print_comma_list (print_vsty_nopar info)) vl

let re_macro = Str.regexp "\\bMACRO\\b"
let has_macro s =
  try let _ = Str.search_forward re_macro s 0 in true with Not_found -> false
let is_macro info fmt = function
  | Some (Edition (_, c)) when info.realization && List.exists has_macro c ->
      fprintf fmt "MACRO "
  | _ -> ()

let print_param_decl ~prev info fmt ls =
  ignore prev;
  let _, _, all_ty_params = ls_ty_vars ls in
  let vl = List.map create_argument ls.ls_args in
  print_name fmt ls.ls_name;
  fprintf fmt "@[<hov 2>%a%a%a: %a%a"
    print_ls ls print_params all_ty_params (print_arguments info) vl
    (is_macro info) prev (print_ls_type info) ls.ls_value;
  realization fmt info prev;
  List.iter forget_var vl;
  fprintf fmt "@]@\n@\n"

let print_param_decl ~prev info fmt ls =
  if not (Mid.mem ls.ls_name info.info_syn) then begin
    print_param_decl ~prev info fmt ls;
    forget_tvs ()
  end

let print_logic_decl ~prev info fmt (ls,ld) =
  ignore prev;
  let _, _, all_ty_params = ls_ty_vars ls in
  let vl,e = open_ls_defn ld in
  print_name fmt ls.ls_name;
  fprintf fmt "@[<hov 2>%a%a%a: %a =@ %a@]@\n@\n"
    print_ls ls print_params all_ty_params
    (print_arguments info) vl (print_ls_type info) ls.ls_value
    (print_expr info) e;
  List.iter forget_var vl

let print_logic_decl ~prev info fmt d =
  if not (Mid.mem (fst d).ls_name info.info_syn) then begin
    print_logic_decl ~prev info fmt d;
    forget_tvs ()
  end

let print_recursive_decl info fmt (ls,ld) =
  let _, _, all_ty_params = ls_ty_vars ls in
  let i = match Decl.ls_defn_decrease ld with
    | [i] -> i | _ -> assert false in
  let vl,e = open_ls_defn ld in
  print_name fmt ls.ls_name;
  fprintf fmt "@[<hov 2>%a%a%a: RECURSIVE %a =@ %a@\n"
    print_ls ls print_params all_ty_params (print_arguments info) vl
    (print_ls_type info) ls.ls_value
    (print_expr info) e;
  fprintf fmt "MEASURE %a BY <<@\n@]@\n"
    print_vs (List.nth vl i);
  List.iter forget_var vl

let print_recursive_decl info fmt d =
  if not (Mid.mem (fst d).ls_name info.info_syn) then begin
    print_recursive_decl info fmt d;
    forget_tvs ()
  end

let print_ind info fmt (pr,f) =
  fprintf fmt "@[%% %a:@\n(%a)@]" print_pr pr (print_fmla info) f

let print_ind_decl info fmt (ps,al) =
  let _, _, all_ty_params = ls_ty_vars ps in
  let vl = List.map (create_vsymbol (id_fresh "z")) ps.ls_args in
  let tl = List.map t_var vl in
  let dj = Lists.map_join_left (Eliminate_inductive.exi tl) t_or al in
  print_name fmt ps.ls_name;
  fprintf fmt "@[<hov 2>%a%a%a: INDUCTIVE bool =@ @[<hov>%a@]@]@\n"
    print_ls ps print_params all_ty_params (print_arguments info) vl
    (print_fmla info) dj;
  fprintf fmt "@\n"

let print_ind_decl info fmt d =
  if not (Mid.mem (fst d).ls_name info.info_syn) then begin
    print_ind_decl info fmt d;
    forget_tvs ()
  end

let re_lemma = Str.regexp "\\(\\bLEMMA\\b\\|\\bTHEOREM\\b\\)"
let rec find_lemma = function
  | [] -> "AXIOM"
  | s :: sl ->
      (try let _ = Str.search_forward re_lemma s 0 in Str.matched_group 1 s
       with Not_found -> find_lemma sl)
let axiom_or_lemma = function
  | Some (Edition (_, c)) -> find_lemma c
  | _ -> "AXIOM"

let print_prop_decl ~prev info fmt (k,pr,f) =
  ignore (prev);
  let params = t_ty_freevars Stv.empty f in
  let kind = match k with
    | Paxiom when info.realization -> "LEMMA" (* axiom_or_lemma prev *)
    | Paxiom -> "AXIOM"
    | Plemma -> "LEMMA"
    | Pgoal -> "THEOREM" in
  print_name fmt pr.pr_name;
  fprintf fmt "@[<hov 2>%a%a: %s %a@]@\n@\n"
    print_pr pr print_params params kind (print_fmla info) f;
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
  | Dlogic [d] ->
      print_recursive_decl info fmt d
  | Dlogic _ ->
      unsupportedDecl d "PVS does not support mutually recursive definitions"
  | Dind (Ind, il) ->
      print_list nothing (print_ind_decl info) fmt il
  | Dind (Coind, _) ->
      unsupportedDecl d "PVS: coinductive definitions are not supported"
  | Dprop (_, pr, _) when Mid.mem pr.pr_name info.info_syn ->
      ()
  | Dprop pr ->
      print_prop_decl ~prev info fmt pr

let print_decls ~old info fmt dl =
  fprintf fmt "@[<hov>%a@]" (print_list nothing (print_decl ~old info)) dl

let init_printer th =
  let isanitize = sanitizer char_to_alpha char_to_alnumus in
  let pr = create_ident_printer black_list ~sanitizer:isanitize in
  Sid.iter (fun id -> ignore (id_unique pr id)) th.Theory.th_local;
  pr

let print_task printer_args realize ?old fmt task =
  forget_all ();
  print_prelude fmt printer_args.prelude;
  print_th_prelude task fmt printer_args.th_prelude;
  (* find theories that are both used and realized from metas *)
  let realized_theories =
    Task.on_meta meta_realized_theory (fun mid args ->
      match args with
      | [Theory.MAstr s1; Theory.MAstr s2] ->
        let f,id =
          let l = Strings.rev_split '.' s1 in
          List.rev (List.tl l), List.hd l in
        let th = Env.read_theory printer_args.env f id in
        Mid.add th.Theory.th_name
          (th, (f, if s2 = "" then String.concat "." f else s2)) mid
      | _ -> assert false
    ) Mid.empty task in
  (* two cases: task is use T or task is a real goal *)
    let rec upd_realized_theories = function
    | Some { Task.task_decl = { Theory.td_node =
               Theory.Decl { Decl.d_node = Decl.Dprop (Decl.Pgoal, pr, _) }}} ->
        get_th_name pr.pr_name, [], realized_theories
    | Some { Task.task_decl = { Theory.td_node = Theory.Use th }} ->
        Sid.iter (fun id -> ignore (id_unique iprinter id)) th.Theory.th_local;
       let id = th.Theory.th_name in
       get_th_name id,
       th.Theory.th_path,
       Mid.remove id realized_theories
    | Some { Task.task_decl = { Theory.td_node = Theory.Meta _ };
             Task.task_prev = task } ->
        upd_realized_theories task
    | _ -> assert false in
  let thname, thpath, realized_theories = upd_realized_theories task in
  (* make names as stable as possible by first printing all identifiers *)
  let realized_theories' = Mid.map fst realized_theories in
  let realized_symbols = Task.used_symbols realized_theories' in
  let local_decls = Task.local_decls task realized_symbols in
  let symbol_printers =
    let printers =
      Mid.map (fun th ->
        let pr = fresh_printer () in
        Sid.iter (fun id -> ignore (id_unique pr id)) th.Theory.th_local;
        pr)
        realized_theories' in
    Mid.map (fun th ->
               let _, (p, s) = Mid.find th.Theory.th_name realized_theories in
               let s = if p = thpath then "" else s in
               (s, th, Mid.find th.Theory.th_name printers))
      realized_symbols in
  let info = {
    info_syn = get_syntax_map task;
    symbol_printers = symbol_printers;
    realization = realize;
  }
  in
  (* (\* build IMPORTING declarations *\) *)
  (* let libraries = Hashtbl.create 17 in (\* path -> library name *\) *)
  (* let importing = Hashtbl.create 17 in (\* library name -> theory name *\) *)
  (* let add _ (th, (path, _)) = *)
  (*   if not (Hashtbl.mem libraries path) then begin *)
  (*     let libname = String.concat "_" ("why3" :: path) in *)
  (*     Hashtbl.add libraries path libname *)
  (*   end; *)
  (*   let libname = Hashtbl.find libraries path in *)
  (*   Hashtbl.add importing libname th.Theory.th_name.id_string *)
  (* in *)
  (* Mid.iter add realized_theories; *)
  (* finally, read the old file, if any, and generate the new one *)
  let old = ref (match old with
    | None -> []
    | Some ch -> read_old_script ch)
  in
  fprintf fmt "@[<hov 1>%s: THEORY@\n@[<hov 1>BEGIN@\n" thname;
  Mid.iter
    (fun _ (th, (path, _)) ->
       let lib = if path = thpath then "" else String.concat "." path ^ "@" in
       fprintf fmt "IMPORTING %s%s@\n" lib (get_th_name th.Theory.th_name))
    realized_theories;
  fprintf fmt "%% do not edit above this line@\n";
  fprintf fmt
    "%% surround new declarations you insert below with blank lines@\n@\n";
  print_decls ~old info fmt local_decls;
  output_remaining fmt !old;
  fprintf fmt "@]@\nEND %s@\n@]" thname

let print_task_full args ?old fmt task =
  print_task args false ?old fmt task

let print_task_real args ?old fmt task =
  print_task args true  ?old fmt task

let () = register_printer "pvs" print_task_full
  ~desc:"Printer@ for@ the@ PVS@ proof@ assistant@ \
         (without@ realization@ capabilities)."

let () = register_printer "pvs-realize" print_task_real
  ~desc:"Printer@ for@ the@ PVS@ proof@ assistant@ \
         (with@ realization@ capabilities)."


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. "
End:
*)
