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

let print_ident =
  let printer = create_printer () in
  let print fmt id = Format.fprintf fmt "%s" (id_unique printer id) in
  print

let rec print_ty fmt ty = match ty.ty_node with
  | Tyvar n ->
      fprintf fmt "'%a" print_ident n
  | Tyapp (s, []) -> 
      print_ident fmt s.ts_name
  | Tyapp (s, [t]) -> 
      fprintf fmt "%a %a" print_ty t print_ident s.ts_name
  | Tyapp (s, l) -> 
      fprintf fmt "(%a) %a" (print_list comma print_ty) l print_ident s.ts_name
  
let rec print_term fmt t = match t.t_node with
  | Tbvar n -> 
      assert false
  | Tvar n -> 
      print_ident fmt n.vs_name
  | Tapp (s, tl) ->
      fprintf fmt "(%a(%a) : %a)" 
	print_ident s.fs_name (print_list comma print_term) tl
	print_ty t.t_ty
  | Tlet (t1,tbound) -> 
      let vs,t2 = t_open_bound tbound in
      fprintf fmt "(let %a = %a in %a)"
      print_ident vs.vs_name print_term t1 print_term t2
  | Tcase _ -> assert false (*TODO*)
  | Teps _ -> assert false

let rec print_fmla fmt f = match f.f_node with
  | Fapp (s,tl) -> 
      fprintf fmt "(%a(%a))" 
	print_ident s.ps_name (print_list comma print_term) tl
  | Fquant (q,fbound) ->
      let vs,f = f_open_bound fbound in
      fprintf fmt "(%s %a : %a. %a)"
        (match q with Fforall -> "forall" | Fexists -> "exists")
        print_ident vs.vs_name print_ty vs.vs_ty print_fmla f
  | Ftrue -> fprintf fmt "(true)"
  | Ffalse -> fprintf fmt "(false)"
  | Fbinop (b,f1,f2) -> 
      fprintf fmt "(%a %s %a)"
        print_fmla f1
        (match b with 
           | Fand -> "and" | For -> "or" 
           | Fimplies -> "->" | Fiff -> "<->")
        print_fmla f2
  | Fnot f -> fprintf fmt "(not %a)" print_fmla f
  | _ -> assert false (*TODO*) 

(*
let print_decl fmt d = match d.d_node with
  | Dtype tl ->
  | Dlogic ldl ->
  | Dprop (k,id,fmla) ->
*)
