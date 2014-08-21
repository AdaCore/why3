(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Coq printer *)

open Format
open Pp
open Ident
open Ty
open Term
open Decl
open Printer

let black_list =
  [ "at"; "cofix"; "exists2"; "fix"; "IF"; "left"; "mod"; "Prop";
    "return"; "right"; "Set"; "Type"; "using"; "where"; ]

(* wrong: ' not allowed as first character in Coq identifiers
let char_to_alpha c =
  match c with
    | '\'' -> String.make 1 c
    | _ -> Ident.char_to_alpha c
*)

let char_to_alnumus c =
  match c with
    | '\'' -> String.make 1 c
    | _ -> Ident.char_to_alnumus c

let fresh_printer () =
  let isanitize = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer black_list ~sanitizer:isanitize

let iprinter = fresh_printer ()

let forget_all () = forget_all iprinter

let tv_set = ref Sid.empty

(* type variables *)

let print_tv ?(whytypes=false) fmt tv =
  let n = id_unique iprinter tv.tv_name in
  fprintf fmt "%s" n;
  if whytypes then fprintf fmt " %s_WT" n

let print_tv_binder ?(whytypes=false) ?(implicit=false) fmt tv =
  tv_set := Sid.add tv.tv_name !tv_set;
  let n = id_unique iprinter tv.tv_name in
  if implicit then fprintf fmt "{%s:Type}" n else fprintf fmt "(%s:Type)" n;
  if whytypes then fprintf fmt " {%s_WT:WhyType %s}" n n

let print_tv_binders ?(whytypes=false) ?(implicit=false) fmt stv =
  Stv.iter (fprintf fmt "@ %a" (print_tv_binder ~whytypes ~implicit)) stv

let print_tv_binders_list ?(whytypes=false) ?(implicit=false) fmt ltv =
  List.iter (fprintf fmt "@ %a" (print_tv_binder ~whytypes ~implicit)) ltv

let print_params ?(whytypes=false) fmt stv =
  if Stv.is_empty stv then () else
    fprintf fmt "forall%a,@ " (print_tv_binders ~whytypes ~implicit:true) stv

let print_params_list ?(whytypes=false) fmt ltv =
  match ltv with
  | [] -> ()
  | _ -> fprintf fmt "forall%a,@ " (print_tv_binders_list ~whytypes ~implicit:false) ltv

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

(* info *)

type info = {
  info_syn : syntax_map;
  symbol_printers : (string * ident_printer) Mid.t;
  realization : bool;
}

let ls_ty_vars ls =
  let ty_vars_args = List.fold_left Ty.ty_freevars Stv.empty ls.ls_args in
  let ty_vars_value = Opt.fold Ty.ty_freevars Stv.empty ls.ls_value in
  (ty_vars_args, ty_vars_value, Stv.union ty_vars_args ty_vars_value)


(* unused printing function
let print_path = print_list (constant_string ".") string
*)

let print_id fmt id = string fmt (id_unique iprinter id)

let print_id_real info fmt id =
  try
    let path,ipr = Mid.find id info.symbol_printers in
    fprintf fmt "%s.%s" path (id_unique ipr id)
  with Not_found -> print_id fmt id

let print_ls_real info fmt ls =
  print_id_real info fmt ls.ls_name

let print_ts_real info fmt ts = print_id_real info fmt ts.ts_name
(* unused printing function
let print_pr_real info fmt pr = print_id_real info fmt pr.pr_name
*)

(** Types *)

let print_ts_tv fmt ts =
  match ts.ts_args with
  | [] -> fprintf fmt "%a" print_ts ts
  | _ -> fprintf fmt "(%a %a)" print_ts ts
    (print_list space print_tv) ts.ts_args

let rec print_ty info fmt ty =
  begin match ty.ty_node with
  | Tyvar v -> print_tv fmt v
  | Tyapp (ts, tl) when is_ts_tuple ts ->
      begin
        match tl with
          | []  -> fprintf fmt "unit"
          | [ty] -> print_ty info fmt ty
          | _   -> fprintf fmt "(%a)%%type" (print_list star (print_ty info)) tl
      end
  | Tyapp (ts, tl) ->
    begin match query_syntax info.info_syn ts.ts_name with
      | Some s -> syntax_arguments s (print_ty info) fmt tl
      | None ->
        begin
          match tl with
            | []  -> (print_ts_real info) fmt ts
            | l   -> fprintf fmt "(%a@ %a)" (print_ts_real info) ts
              (print_list space (print_ty info)) l
        end
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

(* unused
let lparen_l fmt () = fprintf fmt "@ ("
*)
let lparen_r fmt () = fprintf fmt "(@,"
(* unused
let print_paren_l fmt x =
  print_list_delim ~start:lparen_l ~stop:rparen ~sep:comma fmt x
*)
let print_paren_r fmt x =
  print_list_delim ~start:lparen_r ~stop:rparen ~sep:comma fmt x

let arrow fmt () = fprintf fmt " ->@ "
let print_arrow_list fmt x = print_list_suf arrow fmt x

let rec print_pat info fmt p = match p.pat_node with
  | Pwild -> fprintf fmt "_"
  | Pvar v -> print_vs fmt v
  | Pas (p,v) ->
      fprintf fmt "(%a as %a)" (print_pat info) p print_vs v
  | Por (p,q) ->
      fprintf fmt "(%a|%a)" (print_pat info) p (print_pat info) q
  | Papp (cs,pl) when is_fs_tuple cs ->
      fprintf fmt "%a" (print_paren_r (print_pat info)) pl
  | Papp (cs,pl) ->
      begin match query_syntax info.info_syn cs.ls_name with
        | Some s -> syntax_arguments s (print_pat info) fmt pl
        | _ when pl = [] -> (print_ls_real info) fmt cs
        | _ -> fprintf fmt "(%a %a)"
          (print_ls_real info) cs (print_list space (print_pat info)) pl
      end

let print_vsty_nopar info fmt v =
  fprintf fmt "%a:%a" print_vs v (print_ty info) v.vs_ty

let print_vsty info fmt v =
  fprintf fmt "(%a)" (print_vsty_nopar info) v

let print_binop fmt = function
  | Tand -> fprintf fmt "/\\"
  | Tor -> fprintf fmt "\\/"
  | Timplies -> fprintf fmt "->"
  | Tiff -> fprintf fmt "<->"

(* unused
let print_label fmt (l,_) = fprintf fmt "(*%s*)" l
*)

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

let rec print_term info fmt t = print_lrterm false false info fmt t
and     print_fmla info fmt f = print_lrfmla false false info fmt f
and print_opl_term info fmt t = print_lrterm true  false info fmt t
and print_opl_fmla info fmt f = print_lrfmla true  false info fmt f
and print_opr_term info fmt t = print_lrterm false true  info fmt t
and print_opr_fmla info fmt f = print_lrfmla false true  info fmt f

and print_lrterm opl opr info fmt t = match t.t_label with
  | _ -> print_tnode opl opr info fmt t
(*
  | [] -> print_tnode opl opr info fmt t
  | ll -> fprintf fmt "(%a %a)"
      (print_list space print_label) ll (print_tnode false false info) t
*)

and print_lrfmla opl opr info fmt f = match f.t_label with
  | _ -> print_fnode opl opr info fmt f
(*
  | [] -> print_fnode opl opr info fmt f
  | ll -> fprintf fmt "(%a %a)"
      (print_list space print_label) ll (print_fnode false false info) f
*)

and print_tnode _opl opr info fmt t = match t.t_node with
  | Tvar v ->
      print_vs fmt v
  | Tconst c ->
      let number_format = {
          Number.long_int_support = true;
          Number.extra_leading_zeros_support = true;
          Number.dec_int_support = Number.Number_custom "%s%%Z";
          Number.hex_int_support = Number.Number_unsupported;
          Number.oct_int_support = Number.Number_unsupported;
          Number.bin_int_support = Number.Number_unsupported;
          Number.def_int_support = Number.Number_unsupported;
          Number.dec_real_support = Number.Number_unsupported;
          Number.hex_real_support = Number.Number_unsupported;
          Number.frac_real_support = Number.Number_custom
            (Number.PrintFracReal ("%s%%R", "(%s * %s)%%R", "(%s / %s)%%R"));
          Number.def_real_support = Number.Number_unsupported;
        } in
      Number.print number_format fmt c
  | Tif (f,t1,t2) ->
      fprintf fmt (protect_on opr "if %a@ then %a@ else %a")
        (print_fmla info) f (print_term info) t1 (print_opl_term info) t2
  | Tlet (t1,tb) ->
      let v,t2 = t_open_bound tb in
      fprintf fmt (protect_on opr "let %a :=@ %a in@ %a")
        print_vs v (print_term info) t1 (print_opl_term info) t2;
      forget_var v
  | Tcase (t,bl) ->
      fprintf fmt "match %a with@\n@[<hov>%a@]@\nend"
        (print_term info) t
        (print_list newline (print_tbranch info)) bl
  | Teps fb ->
      let v,f = t_open_bound fb in
      fprintf fmt (protect_on opr "epsilon %a.@ %a")
        (print_vsty info) v (print_opl_fmla info) f;
      forget_var v
  | Tapp (fs,[]) when is_fs_tuple fs ->
      fprintf fmt "tt"
  | Tapp (fs,pl) when is_fs_tuple fs ->
      fprintf fmt "%a" (print_paren_r (print_term info)) pl
  | Tapp (fs, tl) ->
    begin match query_syntax info.info_syn fs.ls_name with
      | Some s ->
          syntax_arguments s (print_term info) fmt tl
      | _ -> if unambig_fs fs
          then
            if tl = [] then fprintf fmt "%a" (print_ls_real info) fs
            else fprintf fmt "(%a %a)" (print_ls_real info) fs
              (print_list space (print_opr_term info)) tl
          else fprintf fmt "(%a %a: %a)"
            (print_ls_real info) fs (print_list space (print_opr_term info)) tl
            (print_ty info) (t_type t)
    end
  | Tquant _ | Tbinop _ | Tnot _ | Ttrue | Tfalse -> raise (TermExpected t)

and print_fnode opl opr info fmt f = match f.t_node with
  | Tquant (Tforall,fq) ->
      let vl,_tl,f = t_open_quant fq in
      fprintf fmt (protect_on opr "forall %a,@ %a")
        (print_list space (print_vsty info)) vl
        (* (print_tl info) tl *) (print_fmla info) f;
      List.iter forget_var vl
  | Tquant (Texists,fq) ->
      let vl,_tl,f = t_open_quant fq in
      let rec aux fmt vl =
        match vl with
          | [] -> print_fmla info fmt f
          | v::vr ->
              fprintf fmt (protect_on opr "exists %a,@ %a")
                (print_vsty_nopar info) v
                aux vr
      in
      aux fmt vl;
      List.iter forget_var vl
  | Ttrue ->
      fprintf fmt "True"
  | Tfalse ->
      fprintf fmt "False"
  | Tbinop (b,f1,f2) ->
      fprintf fmt (protect_on (opl || opr) "%a %a@ %a")
        (print_opr_fmla info) f1 print_binop b (print_opl_fmla info) f2
  | Tnot f ->
      fprintf fmt (protect_on opr "~ %a") (print_opl_fmla info) f
  | Tlet (t,f) ->
      let v,f = t_open_bound f in
      fprintf fmt (protect_on opr "let %a :=@ %a in@ %a")
        print_vs v (print_term info) t (print_opl_fmla info) f;
      forget_var v
  | Tcase (t,bl) ->
      fprintf fmt "match %a with@\n@[<hov>%a@]@\nend"
        (print_term info) t
        (print_list newline (print_fbranch info)) bl
  | Tif (f1,f2,f3) ->
      fprintf fmt (protect_on opr "if %a@ then %a@ else %a")
        (print_fmla info) f1 (print_fmla info) f2 (print_opl_fmla info) f3
  | Tapp (ps, tl) ->
    begin match query_syntax info.info_syn ps.ls_name with
      | Some s -> syntax_arguments s (print_term info) fmt tl
      | _ -> fprintf fmt "(%a%a)" (print_ls_real info) ps
          (print_list_pre space (print_opr_term info)) tl
    end
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)

and print_tbranch info fmt br =
  let p,t = t_open_branch br in
  fprintf fmt "@[<hov 4>| %a =>@ %a@]"
    (print_pat info) p (print_term info) t;
  Svs.iter forget_var p.pat_vars

and print_fbranch info fmt br =
  let p,f = t_open_branch br in
  fprintf fmt "@[<hov 4>| %a =>@ %a@]"
    (print_pat info) p (print_fmla info) f;
  Svs.iter forget_var p.pat_vars

let print_expr info fmt =
  TermTF.t_select (print_term info fmt) (print_fmla info fmt)

(** Declarations *)

let print_constr info ts fmt (cs,_) =
  fprintf fmt "@[<hov 4>| %a : %a%a%a@]" print_ls cs
    (print_arrow_list (print_ty info)) cs.ls_args
    print_ts ts (print_list_pre space print_tv) ts.ts_args

(*

  copy of old user scripts

*)

type content_type =
  Notation | (*Gallina |*) Vernacular

type statement =
  | Info  of string  (* name *)
  | Axiom of string (* name *)
  | Query of string * content_type * string (* name and content *)
  | Other of string (* content *)

exception StringValue of string

let read_generated_name =
  let def = Str.regexp "\\(Definition\\|Fixpoint\\|Inductive\\|CoInductive\\)[ ]+\\([^ :(.]+\\)" in
  fun ch ->
  try
    while true do
      let s = input_line ch in
      if Str.string_match def s 0 then
        raise (StringValue (Str.matched_group 2 s))
    done;
    assert false
  with StringValue name -> name

(** no nested comment *)
let read_comment =
  let start_comment = Str.regexp "(\\*[ ]+\\([^ :]+\\)" in
  let end_comment = Str.regexp ".*\\*)" in
  fun ch ->
    let line = ref "" in
    (** look for "( * name" *)
    let name =
      try
        while true do
          let s = input_line ch in
          if Str.string_match start_comment s 0 then begin
            line := s;
            raise (StringValue (Str.matched_group 1 s))
          end
        done;
        assert false
      with StringValue name -> name in
    (** look for end of comment *)
    while not (Str.string_match end_comment (!line) 0) do
      line := input_line ch
    done;
    name

let read_until re s i ch =
  if not (Str.string_match re s i) then
    while not (Str.string_match re (input_line ch) 0) do () done

let read_until_or_eof re s i ch =
  try
    read_until re s i ch
  with
  | End_of_file -> ()

let read_old_proof =
  let def = Str.regexp "\\(Definition\\|Notation\\|Lemma\\|Theorem\\|Variable\\|Hypothesis\\)[ ]+\\([^ :(.]+\\)" in
  let def_end = Str.regexp ".*[.]$" in
  let old_intros = Str.regexp "^ *([*] Why3 intros " in
  let old_end = Str.regexp ".*[*])" in
  let qed = Str.regexp "\\(Qed\\|Defined\\|Save\\|Admitted\\)[.]" in
  fun ch ->
  try
    let start = ref (pos_in ch) in
    let s = input_line ch in
    if not (Str.string_match def s 0) then raise (StringValue s);
    let kind = Str.matched_group 1 s in
    let name = Str.matched_group 2 s in
    read_until def_end s (Str.match_end ()) ch;
    match kind with
    | "Variable" | "Hypothesis" -> Axiom name
    | _  ->
      let k =
        if kind = "Notation" then Notation
        else begin
          start := pos_in ch;
          let s = input_line ch in
          if Str.string_match old_intros s 0 then begin
            read_until old_end s (Str.match_end ()) ch;
            start := pos_in ch;
            read_until_or_eof qed (input_line ch) 0 ch
          end else
            read_until_or_eof qed s 0 ch;
          Vernacular
        end in
      let len = pos_in ch - !start in
      let s = String.create len in
      seek_in ch !start;
      really_input ch s 0 len;
      Query (name, k, s)
  with StringValue s -> Other s

(* Load old-style proofs where users were confined to a few sections. *)
let read_deprecated_script ch in_context =
  let sc = ref [] in
  let context = ref in_context in
  try
    while true do
      let pos = pos_in ch in
      let s = input_line ch in
      if !context then
        if s = "(* DO NOT EDIT BELOW *)" then context := false else
        sc := Other s :: !sc
      else if s <> "" then begin
        seek_in ch pos;
        sc := read_old_proof ch :: Other "" :: !sc;
        raise End_of_file
      end
    done;
    assert false
  with
  | End_of_file -> !sc

let read_old_script =
  let axm = Str.regexp "\\(Axiom\\|Parameter\\)[ ]+\\([^ :(.]+\\)" in
  fun ch ->
  let skip_to_empty = ref true in
  let last_empty_line = ref 0 in
  let sc = ref [] in
  try
    while true do
      let s = input_line ch in
      if s = "" then last_empty_line := pos_in ch;
      if !skip_to_empty then (if s = "" then skip_to_empty := false) else
      if s = "(* Why3 comment *)" then
        (let name = read_comment ch in sc := Info name :: !sc;
         skip_to_empty := true) else
      if s = "(* Why3 assumption *)" then
        (let name = read_generated_name ch in sc := Axiom name :: !sc;
        skip_to_empty := true) else
      if Str.string_match axm s 0 then
        (let name = Str.matched_group 2 s in sc := Axiom name :: !sc;
        skip_to_empty := true) else
      if s = "(* Why3 goal *)" then
        (sc := read_old_proof ch :: !sc; skip_to_empty := true) else
      if s = "(* YOU MAY EDIT THE CONTEXT BELOW *)" then
        (sc := read_deprecated_script ch true; raise End_of_file) else
      if s = "(* YOU MAY EDIT THE PROOF BELOW *)" then
        (seek_in ch !last_empty_line;
        sc := read_deprecated_script ch false;
        raise End_of_file) else
      sc := Other s :: !sc
    done;
    assert false
  with
  | End_of_file ->
    let rec rmv = function
      | Other "" :: t -> rmv t
      | l -> l in
    List.rev (rmv !sc)

(* Output all the Other entries of the script that occur before the
   location of name. Modify the script by removing the name entry and all
   these outputs. Return the user content. *)
let output_till_statement fmt script name =
  let print i =
    let rec aux acc = function
      | h :: l when h == i ->
        let l = match l with
          | Other "" :: l -> l
          | _ -> l in
        script := List.rev_append acc l
      | Other o :: l -> fprintf fmt "%s@\n" o; aux acc l
      | h :: l -> aux (h :: acc) l
      | [] -> assert false in
    aux [] !script in
  let rec find = function
    | Info n as o :: _ when n = name -> print o; Some o
    | Axiom n as o :: _ when n = name -> print o; Some o
    | Query (n,_,_) as o :: _ when n = name -> print o; Some o
    | [] -> None
    | _ :: t -> find t in
  find !script

let output_remaining fmt script =
  List.iter (function
    | Info _ | Axiom _ -> ()
    | Query (n,_,c) -> fprintf fmt "(* Unused content named %s@\n%s *)@\n" n c
    | Other c -> fprintf fmt "%s@\n" c) script

let rec intros_hyp n fmt f =
  match f.t_node with
    | Tbinop(Tand,f1,f2) ->
      fprintf fmt "(";
      let m = intros_hyp n fmt f1 in
      fprintf fmt ",";
      let k = intros_hyp m fmt f2 in
      fprintf fmt ")";
      k
    | Tquant(Texists,fq) ->
      let vsl,_trl,f = t_open_quant fq in
      let rec aux n vsl =
        match vsl with
          | [] -> intros_hyp n fmt f
          | v::l ->
            fprintf fmt "(%a," print_vs v;
            let m = aux n l in
            fprintf fmt ")";
            m
      in
      let m = aux n vsl in
      List.iter forget_var vsl;
      m
    | _ ->
      fprintf fmt "h%d" n;
      n+1

let rec do_intros n fmt fmla =
  match fmla.t_node with
    | Tlet(_,fb) ->
      let vs,f = t_open_bound fb in
      fprintf fmt "@ %a" print_vs vs;
      do_intros n fmt f;
      forget_var vs
    | Tquant(Tforall,fq) ->
      let vsl,_trl,f = t_open_quant fq in
      List.iter
        (fun v -> fprintf fmt "@ %a" print_vs v) vsl;
      do_intros n fmt f;
      List.iter forget_var vsl
    | Tbinop(Timplies, f1, f2) ->
      fprintf fmt "@ ";
      let m = intros_hyp n fmt f1 in
      do_intros m fmt f2
    | _ -> ()

let intros_params fmt params =
  Stv.iter
    (fun tv ->
      let n = id_unique iprinter tv.tv_name in
      fprintf fmt "@ %s %s_WT" n n)
    params

let need_intros params fmla =
  not (Stv.is_empty params) ||
  match fmla.t_node with
  | Tlet _
  | Tquant(Tforall,_)
  | Tbinop(Timplies, _, _) -> true
  | _ -> false

let intros fmt params fmla =
  fprintf fmt "@[intros%a%a.@]" intros_params params (do_intros 1) fmla

let print_empty_proof fmt def =
  match def with
    | Some (params,fmla) ->
      if need_intros params fmla then intros fmt params fmla;
      fprintf fmt "@\n@\n";
      fprintf fmt "Qed.@\n"
    | None ->
      fprintf fmt "@\n";
      fprintf fmt "Defined.@\n"

let print_previous_proof def info fmt previous =
  match previous with
  | None ->
    print_empty_proof fmt def
  | Some (Query (_,Vernacular,c)) ->
    begin match def with
    | Some (p, f) when not info.realization && need_intros p f ->
        fprintf fmt "@[(* Why3 %a *)@]@\n" (fun fmt f -> intros fmt p f) f
    | _ -> ()
    end;
    fprintf fmt "%s" c
  | Some (Query (_,Notation,_))
  | Some (Axiom _) | Some (Other _) | Some (Info _) ->
    assert false

let print_type_decl ~prev info fmt ts =
  if is_ts_tuple ts then () else
  match ts.ts_def with
    | None ->
      if info.realization then
        match prev with
        | Some (Query (_,Notation,c)) ->
          fprintf fmt "(* Why3 goal *)@\n%s@\n" c
        | Some (Axiom _) ->
          fprintf fmt "(* Why3 goal *)@\n@[<hov 2>Variable %a : %aType.@]@\n@[<hov 2>Hypothesis %a_WhyType : %aWhyType %a.@]@\nExisting Instance %a_WhyType.@\n@\n"
            print_ts ts (print_params_list ~whytypes:false) ts.ts_args
            print_ts ts (print_params_list ~whytypes:true) ts.ts_args print_ts_tv ts
            print_ts ts
        | _ ->
          fprintf fmt "(* Why3 goal *)@\n@[<hov 2>Definition %a : %aType.@]@\n%a@\n"
            print_ts ts (print_params_list ~whytypes:false) ts.ts_args
            (print_previous_proof None info) prev
      else
        fprintf fmt "@[<hov 2>Axiom %a : %aType.@]@\n@[<hov 2>Parameter %a_WhyType : %aWhyType %a.@]@\nExisting Instance %a_WhyType.@\n@\n"
          print_ts ts (print_params_list ~whytypes:false) ts.ts_args
          print_ts ts (print_params_list ~whytypes:true) ts.ts_args print_ts_tv ts
          print_ts ts
    | Some ty ->
      fprintf fmt "(* Why3 assumption *)@\n@[<hov 2>Definition %a%a :=@ %a.@]@\n@\n"
        print_ts ts (print_list_pre space print_tv_binder) ts.ts_args
        (print_ty info) ty

let print_type_decl ~prev info fmt ts =
  if not (Mid.mem ts.ts_name info.info_syn) then
    (print_type_decl ~prev info fmt ts; forget_tvs ())

let print_data_decl ~first info fmt ts csl =
  let name = id_unique iprinter ts.ts_name in
  if first then
    fprintf fmt "(* Why3 assumption *)@\n@[<hov 2>Inductive"
  else fprintf fmt "@\nwith";
  fprintf fmt " %s%a :=@\n@[<hov>%a@]"
    name (print_list_pre space print_tv_binder) ts.ts_args
    (print_list newline (print_constr info ts)) csl;
  name

let print_data_whytype_and_implicits fmt (name,ts,csl) =
  fprintf fmt "@[<hov 2>Axiom %s_WhyType : %aWhyType %a.@]@\nExisting Instance %s_WhyType.@\n"
    name (print_params_list ~whytypes:true) ts.ts_args print_ts_tv ts name;
  List.iter
    (fun (cs,_) ->
      let _, _, all_ty_params = ls_ty_vars cs in
      if not (Stv.is_empty all_ty_params) then
        let print fmt tv = fprintf fmt "[%a]" (print_tv ~whytypes:false) tv in
        fprintf fmt "@[<hov 2>Implicit Arguments %a@ [%a].@]@\n"
          print_ls cs
          (print_list space print) ts.ts_args)
    csl;
  fprintf fmt "@\n"

let print_data_decls info fmt tl =
  let none,d =
    List.fold_left
      (fun ((first,l) as acc) (ts,csl) ->
        if is_ts_tuple ts || Mid.mem ts.ts_name info.info_syn
        then acc else
        let name = print_data_decl info ~first fmt ts csl in
        forget_tvs ();
        (false,(name,ts,csl)::l))
      (true,[]) tl
  in
  if none then () else
    begin
      fprintf fmt ".@]@\n";
      List.iter (print_data_whytype_and_implicits fmt) d
    end

let print_ls_type info fmt = function
  | None -> fprintf fmt "Prop"
  | Some ty -> print_ty info fmt ty

let print_param_decl ~prev info fmt ls =
  let _, _, all_ty_params = ls_ty_vars ls in
  if info.realization then
    match prev with
    | Some (Query (_,Notation,c)) ->
      fprintf fmt "(* Why3 goal *)@\n%s@\n" c
    | Some (Axiom _) ->
      fprintf fmt "(* Why3 goal *)@\n@[<hov 2>Variable %a: %a%a%a.@]@\n@\n"
        print_ls ls (print_params ~whytypes:true) all_ty_params
        (print_arrow_list (print_ty info)) ls.ls_args
        (print_ls_type info) ls.ls_value
    | (* Some Info *) _ when Mid.mem ls.ls_name info.info_syn ->
      let vl =
        List.map (fun ty -> create_vsymbol (id_fresh "x") ty) ls.ls_args in
      let e = Term.t_app ls (List.map Term.t_var vl) ls.ls_value in
      fprintf fmt
        "(* Why3 comment *)@\n\
         (* %a is replaced with %a by the coq driver *)@\n@\n"
        print_ls ls
        (print_expr info) e;
      List.iter forget_var vl
    | _ ->
      fprintf fmt "(* Why3 goal *)@\n@[<hov 2>Definition %a: %a%a%a.@]@\n%a@\n"
        print_ls ls (print_params ~whytypes:true) all_ty_params
        (print_arrow_list (print_ty info)) ls.ls_args
        (print_ls_type info) ls.ls_value
        (print_previous_proof None info) prev
  else
    fprintf fmt "@[<hov 2>Parameter %a: %a%a%a.@]@\n@\n"
      print_ls ls (print_params ~whytypes:true) all_ty_params
      (print_arrow_list (print_ty info)) ls.ls_args
      (print_ls_type info) ls.ls_value

let print_param_decl ~prev info fmt ls =
  if info.realization || not (Mid.mem ls.ls_name info.info_syn) then
    (print_param_decl ~prev info fmt ls; forget_tvs ())

let print_logic_decl info fmt (ls,ld) =
  let _, _, all_ty_params = ls_ty_vars ls in
  let vl,e = open_ls_defn ld in
  fprintf fmt "(* Why3 assumption *)@\n@[<hov 2>Definition %a%a%a: %a :=@ %a.@]@\n"
    print_ls ls
    (print_tv_binders ~whytypes:true ~implicit:true) all_ty_params
    (print_list_pre space (print_vsty info)) vl
    (print_ls_type info) ls.ls_value
    (print_expr info) e;
  List.iter forget_var vl;
  fprintf fmt "@\n"

let print_equivalence_lemma ~prev info fmt name (ls,ld) =
  let _, _, all_ty_params = ls_ty_vars ls in
  let def_formula = ls_defn_axiom ld in
  fprintf fmt
    "(* Why3 goal *)@\n@[<hov 2>Lemma %s :@ %a%a.@]@\n"
    name
    (print_params ~whytypes:true) all_ty_params
    (print_expr info) def_formula;
  fprintf fmt "%a@\n"
    (print_previous_proof (Some (all_ty_params,def_formula)) info) prev

let print_equivalence_lemma ~old info fmt ((ls,_) as d) =
  if info.realization && (Mid.mem ls.ls_name info.info_syn) then
    let name = Ident.string_unique iprinter
      ((id_unique iprinter ls.ls_name)^"_def") in
    let prev = output_till_statement fmt old name in
    (print_equivalence_lemma ~prev info fmt name d; forget_tvs ())

let print_logic_decl ~old info fmt d =
  (** During realization the definition of a "builtin" symbol is
      printed and an equivalence lemma with associated coq function is
      requested *)
  if not (Mid.mem (fst d).ls_name info.info_syn) then
    (print_logic_decl info fmt d; forget_tvs ())
  else if info.realization then
    print_equivalence_lemma ~old info fmt d

let print_recursive_decl info fmt (ls,ld) =
  let _, _, all_ty_params = ls_ty_vars ls in
  let i = match Decl.ls_defn_decrease ld with
    | [i] -> i | _ -> assert false in
  let vl,e = open_ls_defn ld in
  fprintf fmt "%a%a%a {struct %a}: %a :=@ %a@]"
    print_ls ls
    (print_tv_binders ~whytypes:true ~implicit:true) all_ty_params
    (print_list_pre space (print_vsty info)) vl
    print_vs (List.nth vl i)
    (print_ls_type info) ls.ls_value
    (print_expr info) e;
  List.iter forget_var vl

let print_recursive_decl ~old info fmt dl =
  let dl_syn, dl_no_syn =
    List.partition (fun (ls,_) ->
      info.realization && (Mid.mem ls.ls_name info.info_syn)) dl in
  if dl_no_syn <> [] then begin
    fprintf fmt "(* Why3 assumption *)@\n";
    print_list_delim
      ~start:(fun fmt () -> fprintf fmt "@[<hov 2>Fixpoint ")
      ~stop:(fun fmt () -> fprintf fmt ".@]@\n")
      ~sep:(fun fmt () -> fprintf fmt "@]@\n@[<hov 2>with ")
      (fun fmt d -> print_recursive_decl info fmt d; forget_tvs ())
      fmt dl_no_syn;
    fprintf fmt "@\n";
  end;
  List.iter (print_equivalence_lemma ~old info fmt) dl_syn

let print_ind info fmt (pr,f) =
  fprintf fmt "@[<hov 4>| %a : %a@]" print_pr pr (print_fmla info) f

let print_ind_decl info fmt ps bl =
  let _, _, all_ty_params = ls_ty_vars ps in
  fprintf fmt " %a%a: %aProp :=@ @[<hov>%a@]"
    print_ls ps (print_tv_binders ~whytypes:true ~implicit:true) all_ty_params
    (print_arrow_list (print_ty info)) ps.ls_args
    (print_list newline (print_ind info)) bl

let print_ind_decls info s fmt tl =
  let none =
    List.fold_left (fun first (ps,bl) ->
      if Mid.mem ps.ls_name info.info_syn then first
      else begin
        if first then
          fprintf fmt "(* Why3 assumption *)@\n@[<hov 2>%s"
            (match s with Ind -> "Inductive" | Coind -> "CoInductive")
          else fprintf fmt "@\nwith";
        print_ind_decl info fmt ps bl;
        forget_tvs ();
        false
      end) true tl in
  if not none then fprintf fmt ".@]@\n@\n"

let print_prop_decl ~prev info fmt (k,pr,f) =
  ignore prev;
  let params = t_ty_freevars Stv.empty f in
  let stt = match k with
    | Paxiom when info.realization -> "Lemma"
    | Paxiom -> ""
    | Plemma -> "Lemma"
    | Pgoal -> "Theorem"
    | Pskip -> assert false (* impossible *)
  in
  if stt <> "" then
    match prev with
    | Some (Axiom _) when stt = "Lemma" ->
      fprintf fmt "(* Why3 goal *)@\n@[<hov 2>Hypothesis %a : %a%a.@]@\n@\n"
        print_pr pr (print_params ~whytypes:true) params
        (print_fmla info) f
    | _ ->
      fprintf fmt "(* Why3 goal *)@\n@[<hov 2>%s %a : %a%a.@]@\n%a@\n"
        stt print_pr pr (print_params ~whytypes:true) params
        (print_fmla info) f
        (print_previous_proof (Some (params,f)) info) prev
  else
    fprintf fmt "@[<hov 2>Axiom %a : %a%a.@]@\n@\n"
      print_pr pr (print_params ~whytypes:true) params
      (print_fmla info) f;
  forget_tvs ()

let print_decl ~old info fmt d =
  let name =
    match d.d_node with
    | Dtype ts
    | Ddata ((ts, _)::_) -> id_unique iprinter ts.ts_name
    | Dparam ls
    | Dlogic ((ls,_)::_)
    | Dind (_, (ls,_)::_) -> id_unique iprinter ls.ls_name
    | Dprop (_,pr,_) -> id_unique iprinter pr.pr_name
    | Ddata []
    | Dlogic []
    | Dind (_, []) -> assert false in
  let prev = output_till_statement fmt old name in
  match d.d_node with
  | Dtype ts ->
      print_type_decl ~prev info fmt ts
  | Ddata tl -> print_data_decls info fmt tl
  | Dparam ls ->
      print_param_decl ~prev info fmt ls
  | Dlogic [s,_ as ld] when not (Sid.mem s.ls_name d.d_syms) ->
      print_logic_decl ~old info fmt ld
  | Dlogic ll ->
      print_recursive_decl ~old info fmt ll
  | Dind (s, il) ->
      print_ind_decls info s fmt il
  | Dprop (_,pr,_) when not info.realization && Mid.mem pr.pr_name info.info_syn ->
      ()
  | Dprop pr ->
      print_prop_decl ~prev info fmt pr

let print_decls ~old info fmt dl =
  fprintf fmt "@\n@[<hov>%a@]" (print_list nothing (print_decl ~old info)) dl

let print_task printer_args realize ?old fmt task =
  (* eprintf "Task:%a@.@." Pretty.print_task task; *)
  forget_all ();
  print_prelude fmt printer_args.prelude;
  print_th_prelude task fmt printer_args.th_prelude;
  (* find theories that are both used and realized from metas *)
  let realized_theories =
    Task.on_meta meta_realized_theory (fun mid args ->
      match args with
      | [Theory.MAstr s1; Theory.MAstr s2] ->
        (* TODO: do not split string; in fact, do not even use a string argument *)
        let f,id =
          let l = Strings.rev_split '.' s1 in
          List.rev (List.tl l), List.hd l in
        let th = Env.find_theory printer_args.env f id in
        Mid.add th.Theory.th_name (th, if s2 = "" then s1 else s2) mid
      | _ -> assert false
    ) Mid.empty task in
  (* 2 cases: goal is clone T with [] or goal is a real goal *)
  let rec upd_realized_theories = function
    | Some { Task.task_decl = { Theory.td_node =
               Theory.Decl { Decl.d_node = Decl.Dprop (Decl.Pgoal, _, _) }}} ->
        realized_theories
    | Some { Task.task_decl = { Theory.td_node = Theory.Clone (th,_) }} ->
        Sid.iter (fun id -> ignore (id_unique iprinter id)) th.Theory.th_local;
        Mid.remove th.Theory.th_name realized_theories
    | Some { Task.task_decl = { Theory.td_node = Theory.Meta _ };
             Task.task_prev = task } ->
        upd_realized_theories task
    | _ -> assert false in
  let realized_theories = upd_realized_theories task in
  let realized_theories' =
    Mid.map (fun (th,s) -> fprintf fmt "Require %s.@\n" s; th) realized_theories in
  let realized_symbols = Task.used_symbols realized_theories' in
  let local_decls = Task.local_decls task realized_symbols in
  (* eprintf "local_decls:%i@." (List.length local_decls); *)
  (* associate a special printer to each symbol in a realized theory *)
  let symbol_printers =
    let printers =
      Mid.map (fun th ->
        let pr = fresh_printer () in
        Sid.iter (fun id -> ignore (id_unique pr id)) th.Theory.th_local;
        pr
      ) realized_theories' in
    Mid.map (fun th ->
      (snd (Mid.find th.Theory.th_name realized_theories),
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
    | Some ch -> read_old_script ch) in
  print_decls ~old info fmt local_decls;
  output_remaining fmt !old

let print_task_full args ?old fmt task =
  print_task args false ?old fmt task

let print_task_real args ?old fmt task =
  print_task args true  ?old fmt task

let () = register_printer "coq" print_task_full
  ~desc:"Printer@ for@ the@ Coq@ proof@ assistant@ \
         (without@ realization@ capabilities)."
let () = register_printer "coq-realize" print_task_real
  ~desc:"Printer@ for@ the@ Coq@ proof@ assistant@ \
         (with@ realization@ capabilities)."

(* specific printer for realization of theories *)
(* OBSOLETE

open Theory

let print_tdecl ~old info fmt d = match d.td_node with
  | Decl d ->
      print_decl ~old info fmt d
  | Use t ->
      fprintf fmt "Require %s.@\n@\n"
        (id_unique iprinter t.th_name)
  | Meta _ -> assert false (* TODO ? *)
  | Clone _ -> assert false (* TODO *)

let print_tdecls ~old info fmt dl =
  fprintf fmt "@[<hov>%a@\n@]"
    (print_list nothing (print_tdecl ~old info)) dl

let print_theory _env pr thpr ?old fmt th =
  forget_all ();
  print_prelude fmt pr;
  print_prelude_for_theory th fmt thpr;
  let info = {
    info_syn = (Mid.empty : string Ident.Mid.t)
      (* get_syntax_map_of_theory th*);
    realization = true;
  }
  in
  let old = match old with
    | None -> None
    | Some ch -> Some(ref NoWhere,ch)
  in
  print_tdecls ~old info fmt th.th_decls;
  produce_remaining_contexts_and_proofs ~old fmt

*)

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. "
End:
*)
