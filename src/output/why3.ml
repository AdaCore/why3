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
open Driver

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
  create_ident_printer bl ~sanitizer:lsanitize,
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
  tv_set := Sid.add (tv_name tv) !tv_set;
  let sanitize n = "'" ^ n in
  let n = id_unique iprinter ~sanitizer:sanitize (tv_name tv) in
  fprintf fmt "%s" n

let forget_tvs () =
  Sid.iter (forget_id iprinter) !tv_set;
  tv_set := Sid.empty

(* logic variables always start with a lower case letter *)
let print_vs fmt vs =
  let sanitize = String.uncapitalize in
  let n = id_unique iprinter ~sanitizer:sanitize vs.vs_name in
  fprintf fmt "%s" n

let forget_var vs = forget_id iprinter vs.vs_name

(* theory names always start with an upper case letter *)
let print_th fmt th =
  let sanitize = String.capitalize in
  let n = id_unique iprinter ~sanitizer:sanitize th.th_name in
  fprintf fmt "%s" n

let print_ts fmt ts =
  Hid.replace thash ts.ts_name ts;
  fprintf fmt "%s" (id_unique tprinter ts.ts_name)

let print_ls fmt ls =
  Hid.replace lhash ls.ls_name ls;
  let n = if ls.ls_constr
    then id_unique lprinter ~sanitizer:String.capitalize ls.ls_name
    else id_unique lprinter ls.ls_name
  in
  fprintf fmt "%s" n

let print_pr fmt pr =
  Hid.replace phash (pr_name pr) pr;
  fprintf fmt "%s" (id_unique pprinter (pr_name pr))

(** Types *)

let rec ns_comma fmt () = fprintf fmt ",@,"

let rec print_ty drv fmt ty = match ty.ty_node with
  | Tyvar v -> print_tv fmt v
  | Tyapp (ts, tl) ->
    begin match query_ident drv ts.ts_name with
      | Syntax s -> syntax_arguments s (print_ty drv) fmt tl
      | _ ->
        begin match tl with
          | []  -> print_ts fmt ts
          | [t] -> fprintf fmt "%a@ %a" (print_ty drv) t print_ts ts
          | l   -> fprintf fmt "(%a)@ %a"
                     (print_list ns_comma (print_ty drv)) l print_ts ts
        end
    end

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

let rec print_pat drv fmt p = match p.pat_node with
  | Pwild -> fprintf fmt "_"
  | Pvar v -> print_vs fmt v
  | Pas (p,v) -> fprintf fmt "%a as %a" (print_pat drv) p print_vs v
  | Papp (cs,pl) ->
    begin match query_ident drv cs.ls_name with
      | Syntax s -> syntax_arguments s (print_pat drv) fmt pl
      | _ -> fprintf fmt "%a%a"
          print_ls cs (print_paren_r (print_pat drv)) pl
    end

let print_vsty drv fmt v =
  fprintf fmt "%a:@,%a" print_vs v (print_ty drv) v.vs_ty

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

let rec print_term drv fmt t = print_lrterm false false drv fmt t
and     print_fmla drv fmt f = print_lrfmla false false drv fmt f
and print_opl_term drv fmt t = print_lrterm true  false drv fmt t
and print_opl_fmla drv fmt f = print_lrfmla true  false drv fmt f
and print_opr_term drv fmt t = print_lrterm false true  drv fmt t
and print_opr_fmla drv fmt f = print_lrfmla false true  drv fmt f

and print_lrterm opl opr drv fmt t = match t.t_label with
  | [] -> print_tnode opl opr drv fmt t
  | ll -> fprintf fmt "(%a %a)"
      (print_list space print_label) ll (print_tnode false false drv) t

and print_lrfmla opl opr drv fmt f = match f.f_label with
  | [] -> print_fnode opl opr drv fmt f
  | ll -> fprintf fmt "(%a %a)"
      (print_list space print_label) ll (print_fnode false false drv) f

and print_tnode opl opr drv fmt t = match t.t_node with
  | Tbvar _ ->
      assert false
  | Tvar v ->
      print_vs fmt v
  | Tconst c ->
      print_const fmt c
  | Tlet (t1,tb) ->
      let v,t2 = t_open_bound tb in
      fprintf fmt (protect_on opr "let %a =@ %a in@ %a")
        print_vs v (print_opl_term drv) t1 (print_opl_term drv) t2;
      forget_var v
  | Tcase (t1,bl) ->
      fprintf fmt "match %a with@\n@[<hov>%a@]@\nend"
        (print_term drv) t1 (print_list newline (print_tbranch drv)) bl
  | Teps fb ->
      let v,f = f_open_bound fb in
      fprintf fmt (protect_on opr "epsilon %a.@ %a")
        (print_vsty drv) v (print_opl_fmla drv) f;
      forget_var v
  | Tapp (fs, tl) ->
    begin match query_ident drv fs.ls_name with
      | Syntax s -> syntax_arguments s (print_term drv) fmt tl
      | _ -> if unambig_fs fs
          then fprintf fmt "%a%a" print_ls fs
            (print_paren_r (print_term drv)) tl
          else fprintf fmt (protect_on opl "%a%a:%a") print_ls fs
            (print_paren_r (print_term drv)) tl (print_ty drv) t.t_ty
    end

and print_fnode opl opr drv fmt f = match f.f_node with
  | Fquant (q,fq) ->
      let vl,tl,f = f_open_quant fq in
      fprintf fmt (protect_on opr "%a %a%a.@ %a") print_quant q
        (print_list comma (print_vsty drv)) vl
        (print_tl drv) tl (print_fmla drv) f;
      List.iter forget_var vl
  | Ftrue ->
      fprintf fmt "true"
  | Ffalse ->
      fprintf fmt "false"
  | Fbinop (b,f1,f2) ->
      fprintf fmt (protect_on (opl || opr) "%a %a@ %a")
        (print_opr_fmla drv) f1 print_binop b (print_opl_fmla drv) f2
  | Fnot f ->
      fprintf fmt (protect_on opr "not %a") (print_opl_fmla drv) f
  | Flet (t,f) ->
      let v,f = f_open_bound f in
      fprintf fmt (protect_on opr "let %a =@ %a in@ %a")
        print_vs v (print_opl_term drv) t (print_opl_fmla drv) f;
      forget_var v
  | Fcase (t,bl) ->
      fprintf fmt "match %a with@\n@[<hov>%a@]@\nend" (print_term drv) t
        (print_list newline (print_fbranch drv)) bl
  | Fif (f1,f2,f3) ->
      fprintf fmt (protect_on opr "if %a@ then %a@ else %a")
        (print_fmla drv) f1 (print_fmla drv) f2 (print_opl_fmla drv) f3
  | Fapp (ps, tl) ->
    begin match query_ident drv ps.ls_name with
      | Syntax s -> syntax_arguments s (print_term drv) fmt tl
      | _ -> fprintf fmt "%a%a" print_ls ps
            (print_paren_r (print_term drv)) tl
    end

and print_tbranch drv fmt br =
  let pat,svs,t = t_open_branch br in
  fprintf fmt "@[<hov 4>| %a ->@ %a@]" (print_pat drv) pat (print_term drv) t;
  Svs.iter forget_var svs

and print_fbranch drv fmt br =
  let pat,svs,f = f_open_branch br in
  fprintf fmt "@[<hov 4>| %a ->@ %a@]" (print_pat drv) pat (print_fmla drv) f;
  Svs.iter forget_var svs

and print_tl drv fmt tl =
  if tl = [] then () else fprintf fmt "@ [%a]"
    (print_list alt (print_list comma (print_expr drv))) tl

and print_expr drv fmt = e_apply (print_term drv fmt) (print_fmla drv fmt)

(** Declarations *)

let print_constr drv fmt cs =
  fprintf fmt "@[<hov 4>| %a%a@]" print_ls cs
    (print_paren_l (print_ty drv)) cs.ls_args

let print_ty_args fmt = function
  | [] -> ()
  | [tv] -> fprintf fmt " %a" print_tv tv
  | l -> fprintf fmt " (%a)" (print_list ns_comma print_tv) l

let print_type_decl drv fmt (ts,def) = match def with
  | Tabstract -> begin match ts.ts_def with
      | None ->
          fprintf fmt "@[<hov 2>type%a %a@]@\n@\n"
            print_ty_args ts.ts_args print_ts ts
      | Some ty ->
          fprintf fmt "@[<hov 2>type%a %a =@ %a@]@\n@\n"
            print_ty_args ts.ts_args print_ts ts (print_ty drv) ty
      end
  | Talgebraic csl ->
      fprintf fmt "@[<hov 2>type%a %a =@\n@[<hov>%a@]@]@\n@\n"
        print_ty_args ts.ts_args print_ts ts
        (print_list newline (print_constr drv)) csl

let print_type_decl drv fmt d =
  match query_ident drv (fst d).ts_name with
    | Syntax _ -> ()
    | _ -> print_type_decl drv fmt d; forget_tvs ()

let print_ls_defn drv fmt ld =
  let _,vl,e = open_ls_defn ld in
  fprintf fmt " =@ %a" (print_expr drv) e;
  List.iter forget_var vl

let print_ls_type drv fmt = fprintf fmt " :@ %a" (print_ty drv)

let print_logic_decl drv fmt (ls,ld) =
  fprintf fmt "@[<hov 2>logic %a%a%a%a@]@\n@\n"
    print_ls ls (print_paren_l (print_ty drv)) ls.ls_args
    (print_option (print_ls_type drv)) ls.ls_value
    (print_option (print_ls_defn drv)) ld

let print_logic_decl drv fmt d =
  match query_ident drv (fst d).ls_name with
    | Syntax _ -> ()
    | _ -> print_logic_decl drv fmt d; forget_tvs ()

let print_ind drv fmt (pr,f) =
  fprintf fmt "@[<hov 4>| %a : %a@]" print_pr pr (print_fmla drv) f

let print_ind_decl drv fmt (ps,bl) =
  fprintf fmt "@[<hov 2>inductive %a%a =@ @[<hov>%a@]@]@\n@\n"
     print_ls ps (print_paren_l (print_ty drv)) ps.ls_args
     (print_list newline (print_ind drv)) bl

let print_ind_decl drv fmt d =
  match query_ident drv (fst d).ls_name with
    | Syntax _ -> ()
    | _ -> print_ind_decl drv fmt d; forget_tvs ()

let print_pkind fmt = function
  | Paxiom -> fprintf fmt "axiom"
  | Plemma -> fprintf fmt "lemma"
  | Pgoal  -> fprintf fmt "goal"

let print_prop_decl drv fmt (k,pr,f) =
  fprintf fmt "@[<hov 2>%a %a : %a@]@\n@\n" print_pkind k
    print_pr pr (print_fmla drv) f

let print_prop_decl drv fmt (k,pr,f) =
  match k, query_ident drv (pr_name pr) with
    | Paxiom, Remove -> ()
    | _ -> print_prop_decl drv fmt (k,pr,f); forget_tvs ()

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

let print_decl drv fmt d = match d.d_node with
  | Dtype tl  -> print_list nothing (print_type_decl drv) fmt tl
  | Dlogic ll -> print_list nothing (print_logic_decl drv) fmt ll
  | Dind il   -> print_list nothing (print_ind_decl drv) fmt il
  | Dprop p -> print_prop_decl drv fmt p
  | Duse th ->
      fprintf fmt "@[<hov 2>(* use %a *)@]@\n@\n" print_th th
  | Dclone (th,inst) ->
      fprintf fmt "@[<hov 2>(* clone %a with %a *)@]@\n@\n"
        print_th th (print_list comma print_inst) inst

let print_decls drv fmt dl =
  fprintf fmt "@[<hov>%a@\n@]" (print_list nothing (print_decl drv)) dl

let print_context drv fmt ctxt =
  forget_all (); print_decls drv fmt (Context.get_decls ctxt)

let () = register_printer "why3" print_context

