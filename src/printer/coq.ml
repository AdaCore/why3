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
open Printer

let iprinter,tprinter,lprinter,pprinter =
  let bl = [ "at"; "cofix"; "exists2"; "fix"; "IF"; "mod"; "Prop";
	     "return"; "Set"; "Type"; "using"; "where"]
  in
  let isanitize = sanitizer char_to_alpha char_to_alnumus in
  let lsanitize = sanitizer char_to_lalpha char_to_alnumus in
  let usanitize = sanitizer char_to_ualpha char_to_alnumus in
  create_ident_printer bl ~sanitizer:isanitize,
  create_ident_printer bl ~sanitizer:lsanitize,
  create_ident_printer bl ~sanitizer:lsanitize,
  create_ident_printer bl ~sanitizer:usanitize

let forget_all () =
  forget_all iprinter;
  forget_all tprinter;
  forget_all lprinter;
  forget_all pprinter

let tv_set = ref Sid.empty

(* type variables *)
let print_tv fmt tv =
  tv_set := Sid.add tv.tv_name !tv_set;
  let n = id_unique iprinter tv.tv_name in
  fprintf fmt "%s" n

let forget_tvs () =
  Sid.iter (forget_id iprinter) !tv_set;
  tv_set := Sid.empty

(* logic variables *)
let print_vs fmt vs =
  let n = id_unique iprinter vs.vs_name in
  fprintf fmt "%s" n

let forget_var vs = forget_id iprinter vs.vs_name

let print_ts fmt ts =
  fprintf fmt "%s" (id_unique tprinter ts.ts_name)

let print_ls fmt ls =
  fprintf fmt "%s" (id_unique lprinter ls.ls_name)

let print_pr fmt pr =
  fprintf fmt "%s" (id_unique pprinter pr.pr_name)

(* info *)

type info = {
  info_syn : string Mid.t;
  info_rem : Sid.t;
}

(** Types *)

let rec print_ty info fmt ty = match ty.ty_node with
  | Tyvar v -> print_tv fmt v
  | Tyapp (ts, tl) -> begin match query_syntax info.info_syn ts.ts_name with
      | Some s -> syntax_arguments s (print_ty info) fmt tl
      | None -> begin match tl with
          | []  -> print_ts fmt ts
          | l   -> fprintf fmt "(%a@ %a)" print_ts ts
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
let print_paren_l fmt x = print_list_delim lparen_l rparen comma fmt x
let print_paren_r fmt x = print_list_delim lparen_r rparen comma fmt x

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
  | Papp (cs,pl) -> 
      begin match query_syntax info.info_syn cs.ls_name with
        | Some s -> syntax_arguments s (print_pat info) fmt pl
        | _ -> fprintf fmt "%a%a"
            print_ls cs (print_paren_r (print_pat info)) pl
      end

let print_vsty info fmt v =
  fprintf fmt "(%a:%a)" print_vs v (print_ty info) v.vs_ty

let print_quant fmt = function
  | Fforall -> fprintf fmt "forall"
  | Fexists -> fprintf fmt "exists"

let print_binop fmt = function
  | Fand -> fprintf fmt "/\\"
  | For -> fprintf fmt "\\/"
  | Fimplies -> fprintf fmt "->"
  | Fiff -> fprintf fmt "<->"

let print_label = Pretty.print_label

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

let rec print_term info fmt t = print_lrterm false false info fmt t
and     print_fmla info fmt f = print_lrfmla false false info fmt f
and print_opl_term info fmt t = print_lrterm true  false info fmt t
and print_opl_fmla info fmt f = print_lrfmla true  false info fmt f
and print_opr_term info fmt t = print_lrterm false true  info fmt t
and print_opr_fmla info fmt f = print_lrfmla false true  info fmt f

and print_lrterm opl opr info fmt t = match t.t_label with
  | [] -> print_tnode opl opr info fmt t
  | ll -> fprintf fmt "(%a %a)"
      (print_list space print_label) ll (print_tnode false false info) t

and print_lrfmla opl opr info fmt f = match f.f_label with
  | [] -> print_fnode opl opr info fmt f
  | ll -> fprintf fmt "(%a %a)"
      (print_list space print_label) ll (print_fnode false false info) f

and print_tnode opl opr info fmt t = match t.t_node with
  | Tbvar _ ->
      assert false
  | Tvar v ->
      print_vs fmt v
  | Tconst (ConstInt n) -> fprintf fmt "%s%%Z" n
  | Tconst (ConstReal c) ->
      Print_real.print_with_integers
	"(%s)%%R" "(%s * %s)%%R" "(%s / %s)%%R" fmt c
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
      let v,f = f_open_bound fb in
      fprintf fmt (protect_on opr "epsilon %a.@ %a")
        (print_vsty info) v (print_opl_fmla info) f;
      forget_var v
  | Tapp (fs, tl) ->
    begin match query_syntax info.info_syn fs.ls_name with
      | Some s ->
          syntax_arguments s (print_term info) fmt tl
      | _ -> if unambig_fs fs
          then fprintf fmt "(%a %a)" print_ls fs
            (print_space_list (print_term info)) tl
          else fprintf fmt (protect_on opl "%a%a:%a") print_ls fs
            (print_paren_r (print_term info)) tl (print_ty info) t.t_ty
    end

and print_fnode opl opr info fmt f = match f.f_node with
  | Fquant (q,fq) ->
      let vl,tl,f = f_open_quant fq in
      fprintf fmt (protect_on opr "%a %a%a,@ %a") print_quant q
        (print_space_list (print_vsty info)) vl
        (print_tl info) tl (print_fmla info) f;
      List.iter forget_var vl
  | Ftrue ->
      fprintf fmt "True"
  | Ffalse ->
      fprintf fmt "False"
  | Fbinop (b,f1,f2) ->
      fprintf fmt (protect_on (opl || opr) "%a %a@ %a")
        (print_opr_fmla info) f1 print_binop b (print_opl_fmla info) f2
  | Fnot f ->
      fprintf fmt (protect_on opr "~ %a") (print_opl_fmla info) f
  | Flet (t,f) ->
      let v,f = f_open_bound f in
      fprintf fmt (protect_on opr "let %a :=@ %a in@ %a")
        print_vs v (print_opl_term info) t (print_opl_fmla info) f;
      forget_var v
  | Fcase (t,bl) ->
      fprintf fmt "match %a with@\n@[<hov>%a@]@\nend"
        (print_term info) t
        (print_list newline (print_fbranch info)) bl
  | Fif (f1,f2,f3) ->
      fprintf fmt (protect_on opr "if %a@ then %a@ else %a")
        (print_fmla info) f1 (print_fmla info) f2 (print_opl_fmla info) f3
  | Fapp (ps, tl) ->
    begin match query_syntax info.info_syn ps.ls_name with
      | Some s -> syntax_arguments s (print_term info) fmt tl
      | _ -> fprintf fmt "(%a %a)" print_ls ps
          (print_space_list (print_term info)) tl
    end

and print_tbranch info fmt br =
  let p,t = t_open_branch br in
  fprintf fmt "@[<hov 4>| %a =>@ %a@]"
    (print_pat info) p (print_term info) t;
  Svs.iter forget_var p.pat_vars

and print_fbranch info fmt br =
  let p,f = f_open_branch br in
  fprintf fmt "@[<hov 4>| %a =>@ %a@]"
    (print_pat info) p (print_fmla info) f;
  Svs.iter forget_var p.pat_vars

and print_tl info fmt tl =
  if tl = [] then () else fprintf fmt "@ [%a]"
    (print_list alt (print_list comma (print_expr info))) tl

and print_expr info fmt = e_apply (print_term info fmt) (print_fmla info fmt)

(** Declarations *)

let print_constr info fmt cs =
  fprintf fmt "@[<hov 4>| %a%a@]" print_ls cs
    (print_paren_l (print_ty info)) cs.ls_args

let print_type_decl info fmt (ts,def) = match def with
  | Tabstract -> begin match ts.ts_def with
      | None ->
          fprintf fmt "@[<hov 2>Parameter %a : %aType.@]@\n@\n"
            print_ts ts (print_arrow_list print_tv) ts.ts_args
      | Some ty ->
          fprintf fmt "@[<hov 2>Definition %a %a :=@ %a@]@\n@\n"
            print_ts ts (print_arrow_list print_tv) ts.ts_args
	    (print_ty info) ty
      end
  | Talgebraic csl ->
      fprintf fmt "@[<hov 2>Inductive %a %a :=@\n@[<hov>%a@].@]@\n@\n"
        print_ts ts (print_arrow_list print_tv) ts.ts_args
        (print_list newline (print_constr info)) csl

let print_type_decl info fmt d =
  if not (Sid.mem (fst d).ts_name info.info_rem) then
    (print_type_decl info fmt d; forget_tvs ())

let print_ls_type ?(arrow=false) info fmt ls =
  if arrow then fprintf fmt " ->@ ";
  match ls with
  | None -> fprintf fmt "Prop"
  | Some ty -> print_ty info fmt ty

let print_logic_decl info fmt (ls,ld) = match ld with
  | Some ld ->
      let vl,e = open_ls_defn ld in
      fprintf fmt "@[<hov 2>Definition %a%a: %a :=@ %a.@]@\n@\n"
        print_ls ls (print_space_list (print_vsty info)) vl
        (print_ls_type info) ls.ls_value
        (print_expr info) e;
      List.iter forget_var vl
  | None ->
      fprintf fmt "@[<hov 2>Parameter %a: %a@ %a.@]@\n@\n"
        print_ls ls (print_arrow_list (print_ty info)) ls.ls_args
        (print_ls_type ~arrow:(List.length ls.ls_args > 0) info) ls.ls_value

let print_logic_decl info fmt d =
  if not (Sid.mem (fst d).ls_name info.info_rem) then 
    (print_logic_decl info fmt d; forget_tvs ())

let print_ind info fmt (pr,f) =
  fprintf fmt "@[<hov 4>| %a : %a@]" print_pr pr (print_fmla info) f

let print_ind_decl info fmt (ps,bl) =
  fprintf fmt "@[<hov 2>Inductive %a%a : Prop :=@ @[<hov>%a@].@]@\n@\n"
     print_ls ps (print_paren_l (print_ty info)) ps.ls_args
     (print_list newline (print_ind info)) bl

let print_ind_decl info fmt d =
  if not (Sid.mem (fst d).ls_name info.info_rem) then 
    (print_ind_decl info fmt d; forget_tvs ())

let print_pkind fmt = function
  | Paxiom -> fprintf fmt "Axiom"
  | Plemma -> fprintf fmt "Lemma"
  | Pgoal  -> fprintf fmt "Theorem"
  | Pskip  -> assert false (* impossible *)

let print_proof fmt = function
  | Paxiom | Pskip -> ()
  | Plemma | Pgoal -> fprintf fmt "Qed.@\n"

let print_decl info fmt d = match d.d_node with
  | Dtype tl  -> print_list nothing (print_type_decl info) fmt tl
  | Dlogic ll -> print_list nothing (print_logic_decl info) fmt ll
  | Dind il   -> print_list nothing (print_ind_decl info) fmt il
  | Dprop (_,pr,_) when Sid.mem pr.pr_name info.info_rem -> ()
  | Dprop (k,pr,f) ->
      fprintf fmt "@[<hov 2>%a %a : %a.@]@\n%a@\n" print_pkind k
        print_pr pr (print_fmla info) f print_proof k;
      forget_tvs ()

let print_decls info fmt dl =
  fprintf fmt "@[<hov>%a@\n@]" (print_list nothing (print_decl info)) dl

let print_task pr thpr fmt task =
  forget_all ();
  print_prelude fmt pr;
  print_th_prelude task fmt thpr;
  let info = {
    info_syn = get_syntax_map task;
    info_rem = get_remove_set task } in
  print_decls info fmt (Task.task_decls task)

let () = register_printer "coq" print_task

