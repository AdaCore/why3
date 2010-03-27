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
open Decl
open Theory
open Task

let iprinter,tprinter,lprinter,pprinter =
  let bl = ["theory"; "type"; "logic"; "inductive";
            "axiom"; "lemma"; "goal"; "use"; "clone";
            "namespace"; "import"; "export"; "end";
            "forall"; "exists"; "and"; "or"; "not";
            "true"; "false"; "if"; "then"; "else";
            "let"; "in"; "match"; "with"; "as"; "epsilon" ]
  in
  let isanitize = sanitizer char_to_alpha char_to_alnumus in
  let lsanitize = sanitizer char_to_lalpha char_to_alnumus in
  let usanitize = sanitizer char_to_ualpha char_to_alnumus in
  create_ident_printer bl ~sanitizer:isanitize,
  create_ident_printer bl ~sanitizer:lsanitize,
  create_ident_printer bl ~sanitizer:isanitize,
  create_ident_printer bl ~sanitizer:usanitize

let thash = Hid.create 63
let lhash = Hid.create 63
let phash = Hid.create 63

let forget_all () =
  forget_all iprinter;
  forget_all tprinter;
  forget_all lprinter;
  forget_all pprinter;
  Hid.clear thash;
  Hid.clear lhash;
  Hid.clear phash

let tv_set = ref Sid.empty

(* type variables always start with a quote *)
let print_tv fmt tv =
  tv_set := Sid.add tv.tv_name !tv_set;
  let sanitizer n = "'" ^ n in
  fprintf fmt "%s" (id_unique iprinter ~sanitizer tv.tv_name)

let forget_tvs () =
  Sid.iter (forget_id iprinter) !tv_set;
  tv_set := Sid.empty

(* logic variables always start with a lower case letter *)
let print_vs fmt vs =
  let sanitizer = String.uncapitalize in
  fprintf fmt "%s" (id_unique iprinter ~sanitizer vs.vs_name)

let forget_var vs = forget_id iprinter vs.vs_name

(* theory names always start with an upper case letter *)
let print_th fmt th =
  let sanitizer = String.capitalize in
  fprintf fmt "%s" (id_unique iprinter ~sanitizer th.th_name)

let print_ts fmt ts =
  Hid.replace thash ts.ts_name ts;
  fprintf fmt "%s" (id_unique tprinter ts.ts_name)

let print_ls fmt ls =
  Hid.replace lhash ls.ls_name ls;
  fprintf fmt "%s" (id_unique lprinter ls.ls_name)

let print_cs fmt ls =
  Hid.replace lhash ls.ls_name ls;
  let sanitizer = String.capitalize in
  fprintf fmt "%s" (id_unique lprinter ~sanitizer ls.ls_name)

let print_pr fmt pr =
  Hid.replace phash pr.pr_name pr;
  fprintf fmt "%s" (id_unique pprinter pr.pr_name)

(** Types *)

let rec ns_comma fmt () = fprintf fmt ",@,"

let rec print_ty fmt ty = match ty.ty_node with
  | Tyvar v -> print_tv fmt v
  | Tyapp (ts, []) -> print_ts fmt ts
  | Tyapp (ts, [t]) -> fprintf fmt "%a@ %a" print_ty t print_ts ts
  | Tyapp (ts, l) -> fprintf fmt "(%a)@ %a"
      (print_list ns_comma print_ty) l print_ts ts

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

let rec print_pat fmt p = match p.pat_node with
  | Pwild -> fprintf fmt "_"
  | Pvar v -> print_vs fmt v
  | Pas (p,v) -> fprintf fmt "%a as %a" print_pat p print_vs v
  | Papp (cs,pl) -> fprintf fmt "%a%a"
      print_cs cs (print_paren_r print_pat) pl

let print_vsty fmt v =
  fprintf fmt "%a:@,%a" print_vs v print_ty v.vs_ty

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

let rec print_term fmt t = print_lrterm false false fmt t
and     print_fmla fmt f = print_lrfmla false false fmt f
and print_opl_term fmt t = print_lrterm true  false fmt t
and print_opl_fmla fmt f = print_lrfmla true  false fmt f
and print_opr_term fmt t = print_lrterm false true  fmt t
and print_opr_fmla fmt f = print_lrfmla false true  fmt f

and print_lrterm opl opr fmt t = match t.t_label with
  | [] -> print_tnode opl opr fmt t
  | ll -> fprintf fmt "(%a %a)"
      (print_list space print_label) ll (print_tnode false false) t

and print_lrfmla opl opr fmt f = match f.f_label with
  | [] -> print_fnode opl opr fmt f
  | ll -> fprintf fmt "(%a %a)"
      (print_list space print_label) ll (print_fnode false false) f

and print_tnode opl opr fmt t = match t.t_node with
  | Tbvar _ ->
      assert false
  | Tvar v ->
      print_vs fmt v
  | Tconst c ->
      print_const fmt c
  | Tapp (fs, tl) when unambig_fs fs ->
      fprintf fmt "%a%a" print_ls fs (print_paren_r print_term) tl
  | Tapp (fs, tl) ->
      fprintf fmt (protect_on opl "%a%a:%a")
        print_ls fs (print_paren_r print_term) tl print_ty t.t_ty
  | Tlet (t1,tb) ->
      let v,t2 = t_open_bound tb in
      fprintf fmt (protect_on opr "let %a =@ %a in@ %a")
        print_vs v print_opl_term t1 print_opl_term t2;
      forget_var v
  | Tcase (tl,bl) ->
      fprintf fmt "match %a with@\n@[<hov>%a@]@\nend"
        (print_list comma print_term) tl
        (print_list newline print_tbranch) bl
  | Teps fb ->
      let v,f = f_open_bound fb in
      fprintf fmt (protect_on opr "epsilon %a.@ %a")
        print_vsty v print_opl_fmla f;
      forget_var v

and print_fnode opl opr fmt f = match f.f_node with
  | Fapp (ps,[t1;t2]) when ps = ps_equ ->
      fprintf fmt (protect_on (opl || opr) "%a =@ %a")
        print_opr_term t1 print_opl_term t2
  | Fapp (ps,tl) ->
      fprintf fmt "%a%a" print_ls ps
        (print_paren_r print_term) tl
  | Fquant (q,fq) ->
      let vl,tl,f = f_open_quant fq in
      fprintf fmt (protect_on opr "%a %a%a.@ %a") print_quant q
        (print_list comma print_vsty) vl print_tl tl print_fmla f;
      List.iter forget_var vl
  | Ftrue ->
      fprintf fmt "true"
  | Ffalse ->
      fprintf fmt "false"
  | Fbinop (b,f1,f2) ->
      fprintf fmt (protect_on (opl || opr) "%a %a@ %a")
        print_opr_fmla f1 print_binop b print_opl_fmla f2
  | Fnot f ->
      fprintf fmt (protect_on opr "not %a") print_opl_fmla f
  | Flet (t,f) ->
      let v,f = f_open_bound f in
      fprintf fmt (protect_on opr "let %a =@ %a in@ %a")
        print_vs v print_opl_term t print_opl_fmla f;
      forget_var v
  | Fcase (tl,bl) ->
      fprintf fmt "match %a with@\n@[<hov>%a@]@\nend"
        (print_list comma print_term) tl
        (print_list newline print_fbranch) bl
  | Fif (f1,f2,f3) ->
      fprintf fmt (protect_on opr "if %a@ then %a@ else %a")
        print_fmla f1 print_fmla f2 print_opl_fmla f3

and print_tbranch fmt br =
  let pl,svs,t = t_open_branch br in
  fprintf fmt "@[<hov 4>| %a ->@ %a@]"
    (print_list comma print_pat) pl print_term t;
  Svs.iter forget_var svs

and print_fbranch fmt br =
  let pl,svs,f = f_open_branch br in
  fprintf fmt "@[<hov 4>| %a ->@ %a@]"
    (print_list comma print_pat) pl print_fmla f;
  Svs.iter forget_var svs

and print_tl fmt tl =
  if tl = [] then () else fprintf fmt "@ [%a]"
    (print_list alt (print_list comma print_expr)) tl

and print_expr fmt = e_apply (print_term fmt) (print_fmla fmt)

(** Declarations *)

let print_constr fmt cs =
  fprintf fmt "@[<hov 4>| %a%a@]" print_cs cs
    (print_paren_l print_ty) cs.ls_args

let print_ty_args fmt = function
  | [] -> ()
  | [tv] -> fprintf fmt " %a" print_tv tv
  | l -> fprintf fmt " (%a)" (print_list ns_comma print_tv) l

let print_type_decl fmt (ts,def) = match def with
  | Tabstract -> begin match ts.ts_def with
      | None ->
          fprintf fmt "@[<hov 2>type%a %a@]"
            print_ty_args ts.ts_args print_ts ts
      | Some ty ->
          fprintf fmt "@[<hov 2>type%a %a =@ %a@]"
            print_ty_args ts.ts_args print_ts ts print_ty ty
      end
  | Talgebraic csl ->
      fprintf fmt "@[<hov 2>type%a %a =@\n@[<hov>%a@]@]"
        print_ty_args ts.ts_args print_ts ts
        (print_list newline print_constr) csl

let print_type_decl fmt d = print_type_decl fmt d; forget_tvs ()

let print_ls_type fmt = fprintf fmt " :@ %a" print_ty

let print_logic_decl fmt (ls,ld) = match ld with
  | Some ld ->
      let vl,e = open_ls_defn ld in
      fprintf fmt "@[<hov 2>logic %a%a%a =@ %a@]"
        print_ls ls (print_paren_l print_vsty) vl
        (print_option print_ls_type) ls.ls_value print_expr e;
      List.iter forget_var vl
  | None ->
      fprintf fmt "@[<hov 2>logic %a%a%a@]"
        print_ls ls (print_paren_l print_ty) ls.ls_args
        (print_option print_ls_type) ls.ls_value

let print_logic_decl fmt d = print_logic_decl fmt d; forget_tvs ()

let print_ind fmt (pr,f) =
  fprintf fmt "@[<hov 4>| %a : %a@]" print_pr pr print_fmla f

let print_ind_decl fmt (ps,bl) =
  fprintf fmt "@[<hov 2>inductive %a%a =@ @[<hov>%a@]@]"
    print_ls ps (print_paren_l print_ty) ps.ls_args
    (print_list newline print_ind) bl;
  forget_tvs ()

let print_pkind fmt = function
  | Paxiom -> fprintf fmt "axiom"
  | Plemma -> fprintf fmt "lemma"
  | Pgoal  -> fprintf fmt "goal"

let print_prop_decl fmt (k,pr,f) =
  fprintf fmt "@[<hov 2>%a %a : %a@]" print_pkind k
    print_pr pr print_fmla f;
  forget_tvs ()

let print_inst fmt (id1,id2) =
  if Hid.mem thash id2 then
    let n = id_unique tprinter id1 in
    fprintf fmt "type %s = %a" n print_ts (Hid.find thash id2)
  else if Hid.mem lhash id2 then
    let n = id_unique lprinter id1 in
    fprintf fmt "logic %s = %a" n print_ls (Hid.find lhash id2)
  else if Hid.mem phash id2 then
    let n = id_unique pprinter id1 in
    fprintf fmt "prop %s = %a" n print_pr (Hid.find phash id2)
  else
    fprintf fmt "ident %s = %s" id1.id_long id2.id_long

let print_decl fmt d = match d.d_node with
  | Dtype tl  -> print_list newline print_type_decl fmt tl
  | Dlogic ll -> print_list newline print_logic_decl fmt ll
  | Dind il   -> print_list newline print_ind_decl fmt il
  | Dprop p   -> print_prop_decl fmt p

let print_tdecl fmt = function
  | Decl d ->
      print_decl fmt d
  | Use th ->
      fprintf fmt "@[<hov 2>(* use %a *)@]" print_th th
  | Clone (th,inst) ->
      fprintf fmt "@[<hov 2>(* clone %a with %a *)@]"
        print_th th (print_list comma print_inst) inst

let print_decls fmt dl =
  fprintf fmt "@[<hov>%a@]@." (print_list newline2 print_decl) dl

let print_task fmt task = print_decls fmt (task_decls task)

let print_theory fmt th =
  fprintf fmt "@[<hov 2>theory %a@\n%a@]@\nend@."
    print_th th (print_list newline2 print_tdecl) th.th_decls

let print_named_task fmt name task =
  fprintf fmt "@[<hov 2>task %s@\n%a@]@\nend@."
    name print_task task

module NsTree = struct
  type t =
    | Namespace of string * namespace
    | Leaf      of string

  let contents ns =
    let add_ns s ns acc = Namespace (s, ns) :: acc in
    let add_s k s _ acc = Leaf (k ^ s) :: acc in
    let acc = Mnm.fold add_ns           ns.ns_ns []  in
    let acc = Mnm.fold (add_s "prop ")  ns.ns_pr acc in
    let acc = Mnm.fold (add_s "logic ") ns.ns_ls acc in
    let acc = Mnm.fold (add_s "type ")  ns.ns_ts acc in acc

  let decomp = function
    | Namespace (s,ns) -> s, contents ns
    | Leaf s           -> s, []
end

let print_namespace fmt name ns =
  let module P = Prtree.Make(NsTree) in
  fprintf fmt "@[<hov>%a@]@." P.print (NsTree.Namespace (name, ns))

