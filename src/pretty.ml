(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Francois Bobot, Jean-Christophe Filliatre,              *)
(*  Johannes Kanig and Andrei Paskevich.                                  *)
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
open Term
open Ty

let rec print_ty fmt ty = match ty.ty_node with
  | Tyvar n ->
      fprintf fmt "'%a" Name.print n
  | Tyapp (s, []) -> 
      Name.print fmt s.ts_name
  | Tyapp (s, [t]) -> 
      fprintf fmt "%a %a" print_ty t Name.print s.ts_name
  | Tyapp (s, l) -> 
      fprintf fmt "(%a) %a" (print_list comma print_ty) l Name.print s.ts_name
  
let rec print_term fmt t = match t.t_node with
  | Tbvar n -> 
      assert false
  | Tvar n -> 
      Name.print fmt n.vs_name
  | Tapp (s, tl) ->
      fprintf fmt "(%a(%a) : %a)" 
	Name.print s.fs_name (print_list comma print_term) tl
	print_ty t.t_ty
  | _ ->
      assert false (*TODO*)

let rec print_fmla fmt f =
  assert false (*TODO*)

