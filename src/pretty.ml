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
open Ident
open Ty
open Term
open Theory

let print_list_paren x = print_list_delim lparen rparen x

let printer =
  let sanitize = sanitizer char_to_alpha char_to_alnumus in
  create_printer [] ~sanitizer:sanitize

let print_ident fmt id = Format.fprintf fmt "%s" (id_unique printer id)

let forget_var v = forget_id printer v.vs_name

let print_typevar fmt x =
  fprintf fmt "'%a" print_ident x

let rec print_ty fmt ty = match ty.ty_node with
  | Tyvar n ->
      fprintf fmt "'%a" print_ident n
  | Tyapp (s, []) -> 
      print_ident fmt s.ts_name
  | Tyapp (s, [t]) -> 
      fprintf fmt "%a %a" print_ty t print_ident s.ts_name
  | Tyapp (s, l) -> 
      fprintf fmt "(%a)@ %a" (print_list comma print_ty) l print_ident s.ts_name
  
let rec print_term fmt t = match t.t_node with
  | Tbvar n -> 
      assert false
  | Tvar n -> 
      print_ident fmt n.vs_name
  | Tconst (ConstInt s) ->
      fprintf fmt "%s" s
  | Tconst (ConstReal _) ->
      fprintf fmt "<real constant>"
  | Tapp (s, tl) ->
      fprintf fmt "@[<hov>%a(%a):%a@]" 
	print_ident s.ls_name (print_list comma print_term) tl
	print_ty t.t_ty
  | Tlet (t1,tbound) -> 
      let vs,t2 = t_open_bound tbound in
      fprintf fmt "(let %a = %a in@ %a)"
      print_ident vs.vs_name print_term t1 print_term t2;
      forget_var vs
  | Tcase _ ->
      assert false (*TODO*)
  | Teps _ -> 
      assert false (*TODO*)

let print_vsymbol fmt vs = 
  fprintf fmt "%a :@ %a" print_ident vs.vs_name print_ty vs.vs_ty

let rec print_fmla fmt f = match f.f_node with
  | Fapp (s,tl) -> 
      fprintf fmt "@[<hov>%a(%a)@]" 
	print_ident s.ls_name (print_list comma print_term) tl
  | Fquant (q,fquant) ->
      let vl,tl,f = f_open_quant fquant in
      fprintf fmt "(%s %a %a.@ %a)"
        (match q with Fforall -> "forall" | Fexists -> "exists")
        (print_list comma print_vsymbol) vl print_tl tl print_fmla f;
      List.iter forget_var vl
  | Ftrue -> 
      fprintf fmt "true"
  | Ffalse -> 
      fprintf fmt "false)"
  | Fbinop (b,f1,f2) -> 
      fprintf fmt "(%a@ %s@ %a)"
        print_fmla f1
        (match b with 
           | Fand -> "and" | For -> "or" 
           | Fimplies -> "->" | Fiff -> "<->")
        print_fmla f2
  | Fnot f -> 
      fprintf fmt "(not@ %a)" print_fmla f
  | Flet (t, f) -> 
      let v,f = f_open_bound f in
      fprintf fmt "@[<hov 2>let %a = %a in@ %a@]" print_ident v.vs_name
        print_term t print_fmla f;
      forget_var v
  | Fcase _ ->
      assert false (*TODO*)
  | Fif _ ->
      assert false (*TODO*)

and print_tl fmt tl =
  fprintf fmt "[%a]" (print_list alt (print_list comma print_tr)) tl

and print_tr fmt = function
  | TrTerm t -> print_term fmt t
  | TrFmla f -> print_fmla fmt f

let print_lsymbol fmt {ls_name = ls_name; ls_args = tyl; ls_value = vty } = 
  match vty with
    | Some ty ->
        fprintf fmt "%a%a :@ %a" print_ident ls_name
          (print_list_paren comma print_ty) tyl 
          print_ty ty
    | None ->
        fprintf fmt "%a%a" print_ident ls_name
          (print_list_paren comma print_ty) tyl 

let print_ty_decl fmt (ts,tydef) = match tydef,ts.ts_def with
  | Tabstract,None -> 
      fprintf fmt "@[<hov>type %a %a@]" 
	(print_list_paren comma print_typevar) ts.ts_args
	print_ident ts.ts_name
  | Tabstract,Some f -> 
      fprintf fmt "@[<hov>type %a %a =@ @[<hov>%a@]@]" 
	(print_list_paren comma print_typevar) ts.ts_args
	print_ident ts.ts_name
	print_ty f
  | Talgebraic d, None -> 
      fprintf fmt "@[<hov>type %a %a =@ @[<hov>%a@]@]" 
	(print_list_paren comma print_typevar) ts.ts_args
	print_ident ts.ts_name
	(print_list newline print_lsymbol) d
  | Talgebraic _, Some _ -> 
      assert false

let print_vsymbol fmt {vs_name = vs_name; vs_ty = vs_ty} =
  fprintf fmt "%a :@ %a" print_ident vs_name print_ty vs_ty

let print_logic_decl fmt = function
  | Lfunction (fs,None) -> 
      fprintf fmt "@[<hov 2>logic %a@]" print_lsymbol fs
  | Lfunction (fs,Some fd) -> 
      fprintf fmt "@[<hov 2>logic %a :@ %a@]" print_ident fs.ls_name
        print_fmla (fs_defn_axiom fd)
  | Lpredicate (fs,None) -> 
      fprintf fmt "@[<hov 2>logic %a@]" print_lsymbol fs
  | Lpredicate (ps,Some fd) -> 
      fprintf fmt "@[<hov 2>logic %a :@ %a@]" print_ident ps.ls_name
        print_fmla (ps_defn_axiom fd)

let print_ind_decl fmt (ps,_) =
  fprintf fmt "@[<hov 2>inductive %a ...@]" print_ident ps.ls_name

let print_decl fmt d = match d.d_node with
  | Dtype tl -> 
      fprintf fmt "@[<hov>%a@ (* *)@]" (print_list newline print_ty_decl) tl
  | Dlogic ldl -> 
      fprintf fmt "@[<hov>%a@ (* *)@]" 
	(print_list newline print_logic_decl) ldl 
  | Dind idl -> 
      fprintf fmt "@[<hov>%a@ (* *)@]" 
	(print_list newline print_ind_decl) idl 
  | Dprop (k,pr) -> 
      fprintf fmt "%s %a :@ %a@\n" 
        (match k with Paxiom -> "axiom" | Pgoal -> "goal" | Plemma -> "lemma")
        print_ident pr.pr_name
        print_fmla pr.pr_fmla
  | Duse u -> fprintf fmt "use export %a@\n" print_ident u.th_name
  | Dclone (th,il) -> fprintf fmt "(*@[<hov 2>clone export %a with %a@]@\n" 
      print_ident th.th_name
      (print_list comma (print_pair_delim nothing nothing equal print_ident print_ident)) il 

let print_decl_list fmt de = 
  fprintf fmt "@[<hov>%a@]" (print_list newline print_decl) de

let print_context fmt ctxt = print_list newline print_decl fmt 
  (Context.get_decls ctxt) 

let print_theory fmt t =
  fprintf fmt "@[@[<hov 2>theory %a@\n%a@]@\nend@]@\n@\n" print_ident t.th_name 
    print_context t.th_ctxt;
  fprintf fmt "@?"

