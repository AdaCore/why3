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

(** Coq printer *)

open Format
open Pp
open Util
open Ident
open Ty
open Term
open Decl
open Printer

let black_list =
  [ "at"; "cofix"; "exists2"; "fix"; "IF"; "left"; "mod"; "Prop";
    "return"; "right"; "Set"; "Type"; "using"; "where"; ]

let fresh_printer () =
  let isanitize = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer black_list ~sanitizer:isanitize

let iprinter = fresh_printer ()

let forget_all () = forget_all iprinter

let tv_set = ref Sid.empty

(* type variables *)

let print_tv fmt tv =
  let n = id_unique iprinter tv.tv_name in
  fprintf fmt "%s" n

let print_tv_binder fmt tv =
  tv_set := Sid.add tv.tv_name !tv_set;
  let n = id_unique iprinter tv.tv_name in
  fprintf fmt "(%s:Type)" n

let print_implicit_tv_binder fmt tv =
  tv_set := Sid.add tv.tv_name !tv_set;
  let n = id_unique iprinter tv.tv_name in
  fprintf fmt "{%s:Type}" n

let print_ne_params fmt stv =
  Stv.iter
    (fun tv -> fprintf fmt "@ %a" print_tv_binder tv)
    stv

let print_ne_params_list fmt ltv =
  List.iter
    (fun tv -> fprintf fmt "@ %a" print_tv_binder tv)
    ltv

let print_params fmt stv =
  if Stv.is_empty stv then () else
    fprintf fmt "forall%a,@ " print_ne_params stv

let print_implicit_params fmt stv =
  Stv.iter (fun tv -> fprintf fmt "%a@ " print_implicit_tv_binder tv) stv

let print_params_list fmt ltv =
  match ltv with
    | [] -> ()
    | _ -> fprintf fmt "forall%a,@ " print_ne_params_list ltv

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

let print_path = print_list (constant_string ".") string

let print_id fmt id = string fmt (id_unique iprinter id)

let print_id_real info fmt id =
  try
    let path,ipr = Mid.find id info.symbol_printers in
    fprintf fmt "%s.%s" path (id_unique ipr id)
  with Not_found -> print_id fmt id

let print_ls_real info fmt ls = print_id_real info fmt ls.ls_name
let print_ts_real info fmt ts = print_id_real info fmt ts.ts_name
let print_pr_real info fmt pr = print_id_real info fmt pr.pr_name

(** Types *)

let rec print_ty info fmt ty = match ty.ty_node with
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

let print_label fmt (l,_) = fprintf fmt "(*%s*)" l

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

and print_tnode opl opr info fmt t = match t.t_node with
  | Tvar v ->
      print_vs fmt v
  | Tconst c ->
      let number_format = {
          Print_number.long_int_support = true;
          Print_number.dec_int_support = Print_number.Number_custom "%s%%Z";
          Print_number.hex_int_support = Print_number.Number_unsupported;
          Print_number.oct_int_support = Print_number.Number_unsupported;
          Print_number.bin_int_support = Print_number.Number_unsupported;
          Print_number.def_int_support = Print_number.Number_unsupported;
          Print_number.dec_real_support = Print_number.Number_unsupported;
          Print_number.hex_real_support = Print_number.Number_unsupported;
          Print_number.frac_real_support = Print_number.Number_custom
            (Print_number.PrintFracReal ("%s%%R", "(%s * %s)%%R", "(%s / %s)%%R"));
          Print_number.def_real_support = Print_number.Number_unsupported;
        } in
      Print_number.print number_format fmt c
  | Tif (f,t1,t2) ->
      fprintf fmt (protect_on opr "if %a@ then %a@ else %a")
        (print_fmla info) f (print_term info) t1 (print_opl_term info) t2
  | Tlet (t1,tb) ->
      let v,t2 = t_open_bound tb in
      fprintf fmt (protect_on opr "let %a :=@ %a in@ %a")
        print_vs v (print_opl_term info) t1 (print_opl_term info) t2;
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
              (print_space_list (print_term info)) tl
          else fprintf fmt (protect_on opl "(%a %a:%a)") (print_ls_real info) fs
            (print_space_list (print_term info)) tl (print_ty info) (t_type t)
    end
  | Tquant _ | Tbinop _ | Tnot _ | Ttrue | Tfalse -> raise (TermExpected t)

and print_fnode opl opr info fmt f = match f.t_node with
  | Tquant (Tforall,fq) ->
      let vl,_tl,f = t_open_quant fq in
      fprintf fmt (protect_on opr "forall %a,@ %a")
        (print_space_list (print_vsty info)) vl
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
        print_vs v (print_opl_term info) t (print_opl_fmla info) f;
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
      | _ -> fprintf fmt "(%a %a)" (print_ls_real info) ps
          (print_space_list (print_term info)) tl
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
  match cs.ls_args with
    | [] ->
        fprintf fmt "@[<hov 4>| %a : %a %a@]" print_ls cs
          print_ts ts (print_list space print_tv) ts.ts_args
    | l ->
        fprintf fmt "@[<hov 4>| %a : %a -> %a %a@]" print_ls cs
          (print_arrow_list (print_ty info)) l
          print_ts ts (print_list space print_tv) ts.ts_args

let ls_ty_vars ls =
  let ty_vars_args = List.fold_left Ty.ty_freevars Stv.empty ls.ls_args in
  let ty_vars_value = option_fold Ty.ty_freevars Stv.empty ls.ls_value in
  (ty_vars_args, ty_vars_value, Stv.union ty_vars_args ty_vars_value)

let print_implicits fmt ls ty_vars_args ty_vars_value all_ty_params =
  if not (Stv.is_empty all_ty_params) then
    begin
      let need_context = not (Stv.subset ty_vars_value ty_vars_args) in
      if need_context then fprintf fmt "Set Contextual Implicit.@\n";
      fprintf fmt "Implicit Arguments %a.@\n" print_ls ls;
      if need_context then fprintf fmt "Unset Contextual Implicit.@\n"
    end

(*

  copy of old user scripts

*)

type content_type =
  Notation | (*Gallina |*) Vernacular

type statement =
  | Axiom of string (* name *)
  | Query of string * content_type * string (* name and content *)
  | Other of string (* content *)

exception StringValue of string

let read_generated_name =
  let def = Str.regexp "\\(Definition\\|Fixpoint\\|Inductive\\)[ ]+\\([^ :(.]+\\)" in
  fun ch ->
  try
    while true do
      let s = input_line ch in
      if Str.string_match def s 0 then
        raise (StringValue (Str.matched_group 2 s))
    done;
    assert false
  with StringValue name -> name

let read_old_proof =
  let def = Str.regexp "\\(Definition\\|Notation\\|Lemma\\|Theorem\\)[ ]+\\([^ :(.]+\\)" in
  let def_end = Str.regexp ".*[.]$" in
  let qed = Str.regexp "\\(Qed\\|Defined\\|Save\\|Admitted\\)[.]" in
  fun ch ->
  try
    let start = ref (pos_in ch) in
    let s = input_line ch in
    if not (Str.string_match def s 0) then raise (StringValue s);
    let kind = Str.matched_group 1 s in
    let name = Str.matched_group 2 s in
    if not (Str.string_match def_end s (Str.match_end ())) then
      while not (Str.string_match def_end (input_line ch) 0) do () done;
    let k =
      if kind = "Notation" then Notation
      else begin
        start := pos_in ch;
        while not (Str.string_match qed (input_line ch) 0) do () done;
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
    | Axiom n as o :: _ when n = name -> print o; Some o
    | Query (n,_,_) as o :: _ when n = name -> print o; Some o
    | [] -> None
    | _ :: t -> find t in
  find !script

let rec output_remaining fmt ?(in_other=false) script =
  match script with
  | Axiom _ :: t -> output_remaining fmt t
  | Query (n,_,c) :: t ->
    if in_other then fprintf fmt "*)@\n";
    fprintf fmt "(* Unused content named %s@\n%s *)@\n" n c;
    output_remaining fmt t
  | Other c :: t ->
    if not in_other then fprintf fmt "(* ";
    fprintf fmt "%s@\n" c;
    output_remaining fmt ~in_other:true t
  | [] ->
    if in_other then fprintf fmt "*)@\n"

let print_empty_proof fmt def =
  if not def then fprintf fmt "intuition.@\n";
  fprintf fmt "@\n";
  fprintf fmt "%s.@\n" (if def then "Defined" else "Qed")

let print_previous_proof def fmt previous =
  match previous with
  | None | Some (Axiom _) ->
    print_empty_proof fmt def
  | Some (Query (_,Vernacular,c)) ->
    fprintf fmt "%s" c
  | Some (Query (_,Notation,_))
  | Some (Other _) ->
    assert false

let print_type_decl ~prev info fmt ts =
  if is_ts_tuple ts then () else
  match ts.ts_def with
    | None ->
      if info.realization then
        match prev with
        | Some (Query (_,Notation,c)) ->
          fprintf fmt "(* Why3 goal *)@\n%s@\n" c
        | _ ->
          fprintf fmt "(* Why3 goal *)@\n@[<hov 2>Definition %a : %aType.@]@\n%a@\n"
            print_ts ts print_params_list ts.ts_args
            (print_previous_proof true) prev
      else
        fprintf fmt "@[<hov 2>Parameter %a : %aType.@]@\n@\n"
          print_ts ts print_params_list ts.ts_args
    | Some ty ->
      fprintf fmt "(* Why3 assumption *)@\n@[<hov 2>Definition %a %a :=@ %a.@]@\n@\n"
        print_ts ts (print_list space print_tv_binder) ts.ts_args
        (print_ty info) ty

let print_type_decl ~prev info fmt ts =
  if not (Mid.mem ts.ts_name info.info_syn) then
    (print_type_decl ~prev info fmt ts; forget_tvs ())

let print_data_decl info fmt (ts,csl) =
  if is_ts_tuple ts then () else
  let name = id_unique iprinter ts.ts_name in
  fprintf fmt "(* Why3 assumption *)@\n@[<hov 2>Inductive %s %a :=@\n@[<hov>%a@].@]@\n"
    name (print_list space print_tv_binder) ts.ts_args
    (print_list newline (print_constr info ts)) csl;
  List.iter
    (fun (cs,_) ->
      let ty_vars_args, ty_vars_value, all_ty_params = ls_ty_vars cs in
      print_implicits fmt cs ty_vars_args ty_vars_value all_ty_params)
    csl;
  fprintf fmt "@\n"

let print_data_decl info fmt d =
  if not (Mid.mem (fst d).ts_name info.info_syn) then
    (print_data_decl info fmt d; forget_tvs ())

let print_ls_type ?(arrow=false) info fmt ls =
  if arrow then fprintf fmt " ->@ ";
  match ls with
  | None -> fprintf fmt "Prop"
  | Some ty -> print_ty info fmt ty

let print_param_decl ~prev info fmt ls =
  let ty_vars_args, ty_vars_value, all_ty_params = ls_ty_vars ls in
  begin if info.realization then
    match prev with
      | Some (Query (_,Notation,c)) ->
        fprintf fmt "(* Why3 goal *)@\n%s" c
      | _ ->
        fprintf fmt "(* Why3 goal *)@\n@[<hov 2>Definition %a: %a%a%a.@]@\n%a"
          print_ls ls print_params all_ty_params
          (print_arrow_list (print_ty info)) ls.ls_args
          (print_ls_type ~arrow:(ls.ls_args <> []) info) ls.ls_value
          (print_previous_proof true) prev
    else
      fprintf fmt "@[<hov 2>Parameter %a: %a%a%a.@]@\n"
        print_ls ls print_params all_ty_params
        (print_arrow_list (print_ty info)) ls.ls_args
        (print_ls_type ~arrow:(ls.ls_args <> []) info) ls.ls_value
  end;
  print_implicits fmt ls ty_vars_args ty_vars_value all_ty_params;
  fprintf fmt "@\n"

let print_param_decl ~prev info fmt ls =
  if not (Mid.mem ls.ls_name info.info_syn) then
    (print_param_decl ~prev info fmt ls; forget_tvs ())

let print_logic_decl info fmt (ls,ld) =
  let ty_vars_args, ty_vars_value, all_ty_params = ls_ty_vars ls in
  let vl,e = open_ls_defn ld in
  fprintf fmt "(* Why3 assumption *)@\n@[<hov 2>Definition %a%a%a: %a :=@ %a.@]@\n"
    print_ls ls
    print_ne_params all_ty_params
    (print_space_list (print_vsty info)) vl
    (print_ls_type info) ls.ls_value
    (print_expr info) e;
  List.iter forget_var vl;
  print_implicits fmt ls ty_vars_args ty_vars_value all_ty_params;
  fprintf fmt "@\n"

let print_logic_decl info fmt d =
  if not (Mid.mem (fst d).ls_name info.info_syn) then
    (print_logic_decl info fmt d; forget_tvs ())

let print_recursive_decl info fmt (ls,ld) =
  let _, _, all_ty_params = ls_ty_vars ls in
  let i = match Decl.ls_defn_decrease ld with
    | [i] -> i | _ -> assert false in
  let vl,e = open_ls_defn ld in
  fprintf fmt "%a%a%a {struct %a}: %a :=@ %a@]"
    print_ls ls
    print_ne_params all_ty_params
    (print_space_list (print_vsty info)) vl
    print_vs (List.nth vl i)
    (print_ls_type info) ls.ls_value
    (print_expr info) e;
  List.iter forget_var vl

let print_recursive_decl info fmt dl =
  fprintf fmt "(* Why3 assumption *)@\nSet Implicit Arguments.@\n";
  print_list_delim
    ~start:(fun fmt () -> fprintf fmt "@[<hov 2>Fixpoint ")
    ~stop:(fun fmt () -> fprintf fmt ".@\n")
    ~sep:(fun fmt () -> fprintf fmt "@\n@[<hov 2>with ")
    (fun fmt d -> print_recursive_decl info fmt d; forget_tvs ())
    fmt dl;
  fprintf fmt "Unset Implicit Arguments.@\n@\n"

let print_ind info fmt (pr,f) =
  fprintf fmt "@[<hov 4>| %a : %a@]" print_pr pr (print_fmla info) f

let print_ind_decl info fmt (ps,bl) =
  let ty_vars_args, ty_vars_value, all_ty_params = ls_ty_vars ps in
  fprintf fmt "(* Why3 assumption *)@\n@[<hov 2>Inductive %a%a : %a -> Prop :=@ @[<hov>%a@].@]@\n"
     print_ls ps print_implicit_params all_ty_params
    (print_arrow_list (print_ty info)) ps.ls_args
     (print_list newline (print_ind info)) bl;
  print_implicits fmt ps ty_vars_args ty_vars_value all_ty_params;
  fprintf fmt "@\n"

let print_ind_decl info fmt d =
  if not (Mid.mem (fst d).ls_name info.info_syn) then
    (print_ind_decl info fmt d; forget_tvs ())

let print_prop_decl ~prev info fmt (k,pr,f) =
  let params = t_ty_freevars Stv.empty f in
  let stt = match k with
    | Paxiom when info.realization -> "Lemma"
    | Paxiom -> ""
    | Plemma -> "Lemma"
    | Pgoal -> "Theorem"
    | Pskip -> assert false (* impossible *) in
  if stt <> "" then
    fprintf fmt "(* Why3 goal *)@\n@[<hov 2>%s %a : %a%a.@]@\n%a@\n"
      stt print_pr pr print_params params
      (print_fmla info) f
      (print_previous_proof false) prev
  else
    fprintf fmt "@[<hov 2>Axiom %a : %a%a.@]@\n@\n"
      print_pr pr print_params params
      (print_fmla info) f;
  forget_tvs ()

let print_decl ~old info fmt d =
  let name =
    match d.d_node with
    | Dtype ts
    | Ddata ((ts, _)::_) -> id_unique iprinter ts.ts_name
    | Dparam ls
    | Dlogic ((ls,_)::_)
    | Dind ((ls,_)::_) -> id_unique iprinter ls.ls_name
    | Dprop (_,pr,_) -> id_unique iprinter pr.pr_name
    | Ddata []
    | Dlogic []
    | Dind [] -> assert false in
  let prev = output_till_statement fmt old name in
  match d.d_node with
  | Dtype ts ->
      print_type_decl ~prev info fmt ts
  | Ddata tl ->
      print_list nothing (print_data_decl info) fmt tl
  | Dparam ls ->
      print_param_decl ~prev info fmt ls
  | Dlogic [s,_ as ld] when not (Sid.mem s.ls_name d.d_syms) ->
      print_logic_decl info fmt ld
  | Dlogic ll ->
      print_recursive_decl info fmt ll
  | Dind il ->
      print_list nothing (print_ind_decl info) fmt il
  | Dprop (_,pr,_) when Mid.mem pr.pr_name info.info_syn ->
      ()
  | Dprop pr ->
      print_prop_decl ~prev info fmt pr

let print_decls ~old info fmt dl =
  fprintf fmt "@\n@[<hov>%a@\n@]" (print_list nothing (print_decl ~old info)) dl

let print_task env pr thpr realize ?old fmt task =
  forget_all ();
  print_prelude fmt pr;
  print_th_prelude task fmt thpr;
  (* find theories that are both used and realized from metas *)
  let realized_theories =
    Task.on_meta meta_realized (fun mid args ->
      match args with
      | [Theory.MAstr s1; Theory.MAstr s2] ->
        (* TODO: do not split string; in fact, do not even use a string argument *)
        let f,id = let l = split_string_rev s1 '.' in List.rev (List.tl l),List.hd l in
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
    Mid.map (fun (th,s) -> fprintf fmt "Require %s.@\n" s; th) realized_theories in
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

let print_task_full env pr thpr ?old fmt task =
  print_task env pr thpr false ?old fmt task

let print_task_real env pr thpr ?old fmt task =
  print_task env pr thpr true  ?old fmt task

let () = register_printer "coq" print_task_full
let () = register_printer "coq-realize" print_task_real

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
