(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
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

open Format
open Pp
open Util
open Ident
open Ty
open Term
open Theory

let printer () =
  let bl = ["theory"; "type"; "logic"; "inductive";
            "axiom"; "lemma"; "goal"; "use"; "clone";
            "namespace"; "import"; "export"; "end";
            "forall"; "exists"; "and"; "or"; "not";
            "true"; "false"; "if"; "then"; "else";
            "let"; "in"; "match"; "with"; "as"; "epsilon" ]
  in
  let sanitize = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer bl ~sanitizer:sanitize

let printer_debug = printer ()

let print_id ?(printer=printer_debug) fmt id = 
  Format.fprintf fmt "%s" (id_unique printer id)

(* some idents must be put in upper case *)
let print_uc ?(printer=printer_debug) fmt id =
  let sanitize = String.capitalize in
  let n = id_unique printer ~sanitizer:sanitize id in
  fprintf fmt "%s" n

(* and some in lower *)
let print_lc ?(printer=printer_debug) fmt id =
  let sanitize = String.uncapitalize in
  let n = id_unique printer ~sanitizer:sanitize id in
  fprintf fmt "%s" n

let tv_set = ref Sid.empty

let forget_tvs ?(printer=printer_debug) () =
  Sid.iter (forget_id printer) !tv_set;
  tv_set := Sid.empty

(* type variables always start with a quote *)
let print_tv ?(printer=printer_debug) fmt v =
  tv_set := Sid.add v !tv_set;
  let sanitize n = String.concat "" ["'"; n] in
  let n = id_unique printer ~sanitizer:sanitize v in
  fprintf fmt "%s" n

let print_ts ?printer fmt ts = print_lc ?printer fmt ts.ts_name
let print_vs ?printer fmt vs = print_lc ?printer fmt vs.vs_name

let print_ls ?printer fmt ls =
  if ls.ls_constr then print_uc ?printer fmt ls.ls_name
                  else print_lc ?printer fmt ls.ls_name

let forget_var ?(printer=printer_debug) v = forget_id printer v.vs_name

(** Types *)

let rec ns_comma fmt () = fprintf fmt ",@,"

let rec print_ty ?printer fmt ty = match ty.ty_node with
  | Tyvar v -> print_tv ?printer fmt v
  | Tyapp (ts, []) -> print_ts ?printer fmt ts
  | Tyapp (ts, [t]) -> fprintf fmt "%a@ %a" (print_ty ?printer) t (print_ts ?printer) ts
  | Tyapp (ts, l) -> fprintf fmt "(%a)@ %a"
      (print_list ns_comma (print_ty ?printer)) l (print_ts ?printer) ts

let print_const fmt = function
  | ConstInt s -> fprintf fmt "%s" s
  | ConstReal (RConstDecimal (i,f,None)) -> fprintf fmt "%s.%s" i f
  | ConstReal (RConstDecimal (i,f,Some e)) -> fprintf fmt "%s.%se%s" i f e
  | ConstReal (RConstHexa (i,f,e)) -> fprintf fmt "0x%s.%sp%s" i f e

(* can the type of a value be derived from the type of the arguments? *)
let unambig_fs fs =
  let rec lookup v ty = match ty.ty_node with
    | Tyvar u when u == v -> true
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
let print_paren_l fmt x = print_list_delim lparen_l rparen comma fmt x
let print_paren_r fmt x = print_list_delim lparen_r rparen comma fmt x

let rec print_pat ?printer fmt p = match p.pat_node with
  | Pwild -> fprintf fmt "_"
  | Pvar v -> print_vs ?printer fmt v
  | Pas (p,v) -> fprintf fmt "%a as %a" (print_pat ?printer) p (print_vs ?printer) v
  | Papp (cs,pl) -> fprintf fmt "%a%a"
      (print_ls ?printer) cs (print_paren_r (print_pat ?printer)) pl

let print_vsty ?printer fmt v =
  fprintf fmt "%a:@,%a" (print_vs ?printer) v (print_ty ?printer) v.vs_ty

let print_quant fmt = function
  | Fforall -> fprintf fmt "forall"
  | Fexists -> fprintf fmt "exists"

let print_binop fmt = function
  | Fand -> fprintf fmt "and"
  | For -> fprintf fmt "or"
  | Fimplies -> fprintf fmt "->"
  | Fiff -> fprintf fmt "<->"

let print_label fmt l = fprintf fmt "\"%s\"" l

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

let rec print_term ?printer fmt t = print_lrterm ?printer false false fmt t
and     print_fmla ?printer fmt f = print_lrfmla ?printer false false fmt f
and print_opl_term ?printer fmt t = print_lrterm ?printer true  false fmt t
and print_opl_fmla ?printer fmt f = print_lrfmla ?printer true  false fmt f
and print_opr_term ?printer fmt t = print_lrterm ?printer false true  fmt t
and print_opr_fmla ?printer fmt f = print_lrfmla ?printer false true  fmt f

and print_lrterm ?printer opl opr fmt t = match t.t_label with
  | [] -> print_tnode ?printer opl opr fmt t
  | ll -> fprintf fmt "(%a %a)"
      (print_list space print_label) ll (print_tnode ?printer false false) t

and print_lrfmla ?printer opl opr fmt f = match f.f_label with
  | [] -> print_fnode ?printer opl opr fmt f
  | ll -> fprintf fmt "(%a %a)"
      (print_list space print_label) ll (print_fnode ?printer false false) f

and print_tnode ?printer opl opr fmt t = match t.t_node with
  | Tbvar _ ->
      assert false
  | Tvar v ->
      print_vs ?printer fmt v
  | Tconst c ->
      print_const fmt c
  | Tapp (fs, tl) when unambig_fs fs ->
      fprintf fmt "%a%a" (print_ls ?printer) fs (print_paren_r 
                                                   (print_term ?printer)) tl
  | Tapp (fs, tl) ->
      fprintf fmt (protect_on opl "%a%a:%a")
        (print_ls ?printer) fs (print_paren_r (print_term ?printer)) tl 
        (print_ty ?printer) t.t_ty
  | Tlet (t1,tb) ->
      let v,t2 = t_open_bound tb in
      fprintf fmt (protect_on opr "let %a =@ %a in@ %a")
        (print_vs ?printer) v (print_opl_term ?printer) t1 
        (print_opl_term ?printer) t2;
      (forget_var ?printer) v
  | Tcase (t1,bl) ->
      fprintf fmt "match %a with@\n@[<hov>%a@]@\nend"
        (print_term ?printer) t1 (print_list newline (print_tbranch ?printer)) bl
  | Teps fb ->
      let v,f = f_open_bound fb in
      fprintf fmt (protect_on opr "epsilon %a in@ %a")
        (print_vsty ?printer) v (print_opl_fmla ?printer) f;
      (forget_var ?printer) v

and print_fnode ?printer opl opr fmt f = match f.f_node with
  | Fapp (ps,[t1;t2]) when ps = ps_equ ->
      fprintf fmt (protect_on (opl || opr) "%a =@ %a")
        (print_opr_term ?printer) t1 (print_opl_term ?printer) t2
  | Fapp (ps,tl) ->
      fprintf fmt "%a%a" (print_ls ?printer) ps
        (print_paren_r (print_term ?printer)) tl
  | Fquant (q,fq) ->
      let vl,tl,f = f_open_quant fq in
      fprintf fmt (protect_on opr "%a %a%a.@ %a") print_quant q
        (print_list comma (print_vsty ?printer)) vl (print_tl ?printer) tl 
        (print_fmla ?printer) f;
      List.iter (forget_var ?printer) vl
  | Ftrue ->
      fprintf fmt "true"
  | Ffalse ->
      fprintf fmt "false"
  | Fbinop (b,f1,f2) ->
      fprintf fmt (protect_on (opl || opr) "%a %a@ %a")
        (print_opr_fmla ?printer) f1 print_binop b (print_opl_fmla ?printer) f2
  | Fnot f ->
      fprintf fmt (protect_on opr "not %a") (print_opl_fmla ?printer) f
  | Flet (t,f) ->
      let v,f = f_open_bound f in
      fprintf fmt (protect_on opr "let %a =@ %a in@ %a")
        (print_vs ?printer) v (print_opl_term ?printer) t 
        (print_opl_fmla ?printer) f;
      forget_var ?printer v
  | Fcase (t,bl) ->
      fprintf fmt "match %a with@\n@[<hov>%a@]@\nend" (print_term ?printer) t
        (print_list newline (print_fbranch ?printer)) bl
  | Fif (f1,f2,f3) ->
      fprintf fmt (protect_on opr "if %a@ then %a@ else %a")
        (print_fmla ?printer) f1 (print_fmla ?printer) f2 (print_opl_fmla ?printer) f3

and print_tbranch ?printer fmt br =
  let pat,svs,t = t_open_branch br in
  fprintf fmt "@[<hov 4>| %a ->@ %a@]" (print_pat ?printer) pat (print_term ?printer) t;
  Svs.iter (forget_var ?printer) svs

and print_fbranch ?printer fmt br =
  let pat,svs,f = f_open_branch br in
  fprintf fmt "@[<hov 4>| %a ->@ %a@]" (print_pat ?printer) pat (print_fmla ?printer) f;
  Svs.iter (forget_var ?printer) svs

and print_tl ?printer fmt tl =
  if tl = [] then () else fprintf fmt "@ [%a]"
    (print_list alt (print_list comma (print_tr ?printer))) tl

and print_tr  ?printer fmt = function
  | TrTerm t -> print_term ?printer fmt t
  | TrFmla f -> print_fmla ?printer fmt f

(** Declarations *)

let print_constr ?printer fmt cs =
  fprintf fmt "@[<hov 4>| %a%a@]" (print_ls ?printer) cs
    (print_paren_l (print_ty ?printer)) cs.ls_args

let print_ty_args ?printer fmt = function
  | [] -> ()
  | [tv] -> fprintf fmt " %a" (print_tv ?printer) tv
  | l -> fprintf fmt " (%a)" (print_list ns_comma (print_tv ?printer)) l

let print_type_decl ?printer fmt (ts,def) = match def with
  | Tabstract -> begin match ts.ts_def with
      | None ->
          fprintf fmt "@[<hov 2>type%a %a@]"
            (print_ty_args ?printer) ts.ts_args (print_ts ?printer) ts
      | Some ty ->
          fprintf fmt "@[<hov 2>type%a %a =@ %a@]"
            (print_ty_args ?printer) ts.ts_args (print_ts ?printer) ts (print_ty ?printer) ty
      end
  | Talgebraic csl ->
      fprintf fmt "@[<hov 2>type%a %a =@\n@[<hov>%a@]@]"
        (print_ty_args ?printer) ts.ts_args (print_ts ?printer) ts
        (print_list newline (print_constr ?printer)) csl

let print_type_decl ?printer fmt d = print_type_decl ?printer fmt d; 
  forget_tvs  ?printer ()

let print_logic_decl ?printer fmt = function
  | Lfunction (fs,None) ->
      fprintf fmt "@[<hov 2>logic %a%a :@ %a@]"
        (print_ls ?printer) fs (print_paren_l (print_ty ?printer)) fs.ls_args
          (print_ty ?printer)(of_option fs.ls_value)
  | Lpredicate (ps,None) ->
      fprintf fmt "@[<hov 2>logic %a%a@]"
        (print_ls ?printer) ps (print_paren_l (print_ty ?printer)) ps.ls_args
  | Lfunction (fs,Some fd) ->
      let _,vl,t = open_fs_defn fd in
      fprintf fmt "@[<hov 2>logic %a%a :@ %a =@ %a@]"
        (print_ls ?printer) fs (print_paren_l (print_vsty ?printer)) vl
        (print_ty ?printer) t.t_ty (print_term ?printer) t;
      List.iter (forget_var ?printer) vl
  | Lpredicate (ps,Some fd) ->
      let _,vl,f = open_ps_defn fd in
      fprintf fmt "@[<hov 2>logic %a%a =@ %a@]"
        (print_ls ?printer) ps (print_paren_l (print_vsty ?printer)) vl (print_fmla ?printer) f;
      List.iter (forget_var ?printer) vl

let print_logic_decl ?printer fmt d = print_logic_decl ?printer fmt d; 
  forget_tvs ?printer ()

let print_prop ?printer fmt pr =
  fprintf fmt "%a : %a" (print_uc ?printer) pr.pr_name (print_fmla ?printer)
    pr.pr_fmla

let print_ind ?printer fmt pr = 
  fprintf fmt "@[<hov 4>| %a@]" (print_prop ?printer) pr

let print_ind_decl ?printer fmt (ps,bl) =
  fprintf fmt "@[<hov 2>inductive %a%a =@ @[<hov>%a@]@]"
     (print_ls ?printer) ps (print_paren_l (print_ty ?printer)) ps.ls_args
     (print_list newline (print_ind ?printer)) bl;
  forget_tvs ?printer ()

let print_pkind fmt = function
  | Paxiom -> fprintf fmt "axiom"
  | Plemma -> fprintf fmt "lemma"
  | Pgoal  -> fprintf fmt "goal"

let print_inst ?printer fmt (id1,id2) =
  fprintf fmt "%a = %a" (print_id ?printer) id1 (print_id ?printer) id2

let print_th fmt th = fprintf fmt "%s" th.th_name.id_long

let print_decl ?printer fmt d = match d.d_node with
  | Dtype tl  -> print_list newline2 (print_type_decl ?printer) fmt tl
  | Dlogic ll -> print_list newline2 (print_logic_decl ?printer) fmt ll
  | Dind il   -> print_list newline2 (print_ind_decl ?printer) fmt il
  | Dprop (k,pr) ->
      fprintf fmt "@[<hov 2>%a %a@]" print_pkind k (print_prop ?printer) pr;
      forget_tvs ?printer ()
  | Duse th ->
      fprintf fmt "@[<hov 2>(* use %a *)@]" print_th th
  | Dclone (th,inst) ->
      fprintf fmt "@[<hov 2>(* clone %a with %a *)@]"
        print_th th (print_list comma (print_inst ?printer)) inst

let print_decls ?printer fmt dl =
  fprintf fmt "@[<hov>%a@]" (print_list newline2 (print_decl ?printer)) dl

let print_context ?printer fmt ctxt = print_decls ?printer fmt (Context.get_decls ctxt)

let print_theory ?printer fmt th =
  fprintf fmt "@[<hov 2>theory %a@\n%a@]@\nend@\n@."
    print_th th (print_context ?printer) th.th_ctxt

let print_named_context ?printer fmt name ctxt =
  fprintf fmt "@[<hov 2>context %s@\n%a@]@\nend@\n@."
    name (print_context ?printer) ctxt

