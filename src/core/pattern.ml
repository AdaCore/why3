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

open Ident
open Ty
open Term

module Compile
  (X : sig
     type action
     val mk_let : vsymbol -> term -> action -> action
     val mk_case : term -> (pattern * action) list -> action
     val constructors : tysymbol -> lsymbol list
   end) =
struct

  open X

  exception NonExhaustive of pattern list
  exception Unused of action

  type row = {
    elements : pattern list;
    action : action;
  }

  type matrix = {
    values : term list;
    rows : row list;
  }

  let rec update_action t r = match r.elements with
    | { pat_node = Pvar x } :: _ -> 
	mk_let x t r.action
    | { pat_node = Pwild } :: _ -> 
	r.action
    | { pat_node = Pas (p, x) } :: l -> 
	mk_let x t (update_action (t_var x) { r with elements = p :: l })
    | [] | { pat_node = Papp _ } :: _ -> 
	assert false 
	
  let rec is_var p = match p.pat_node with
    | Pwild | Pvar _ -> true
    | Pas (p, _) -> is_var p
    | Papp _ -> false

  let not_enough_for n ty = match ty.ty_node with
    | Tyvar _ -> assert (n = 0); false
    | Tyapp (ts, _) -> n < List.length (constructors ts)

  let rec matrix m = match m.rows with
    | [] -> 
	(* no line *)
	let pl = List.map (fun t -> pat_wild t.t_ty) m.values in
	raise (NonExhaustive pl)
    | { elements = []; action = a } :: _ -> 
	(* at least one action *)
	a
	  (* note : s'il y en a plus, cela ne signifie pas nécessairement
	     que la clause est inutile car l'algo duplique des actions *)
    | _ when List.for_all (fun r -> is_var (List.hd r.elements)) m.rows ->
	(* first column contains only vars -> remove it *)
	let t1 = List.hd m.values in
	let update_row r =
	  { elements = List.tl r.elements; action = update_action t1 r }
	in
	matrix { values = List.tl m.values;
		 rows = List.map update_row m.rows }
    | _ ->
	(* first column contains constructor(s) *)
	let t1 = List.hd m.values in
	let ty = t1.t_ty in
	let vars_for = Hls.create 17 in
	let cm0 = 
	  let empty c pl =
	    let new_var p = create_vsymbol (id_fresh "x") p.pat_ty in
	    let vars = List.map new_var pl in
	    Hls.add vars_for c vars;
	    { values = List.map t_var vars @ List.tl m.values; rows = [] }
	  in
	  let rec add_matrix_from_p cm p = match p.pat_node with
	    | Papp (c, pl) when not (Mls.mem c cm) -> 
		Mls.add c (empty c pl) cm
	    | Pas (p, _) -> 
		add_matrix_from_p cm p
	    | Papp _ | Pwild | Pvar _ -> 
		cm
	  in
	  let add_matrix_for_c cm r = match r.elements with
	    | [] -> assert false
	    | p :: _ -> add_matrix_from_p cm p
	  in
	  List.fold_left add_matrix_for_c Mls.empty m.rows
	in
	let rec dispatch t1 r cm = match r.elements with
	  | [] -> 
	      assert false
	  | { pat_node = Pwild | Pvar _ } :: rr ->
	      (* une variable => on doit la reprendre pour chaque constr. *)
	      Mls.fold
		(fun c m cm -> 
		   let vars = Hls.find vars_for c in
		   let h = List.map (fun v -> pat_wild v.vs_ty) vars in 
		   let r' = 
		     { elements = h @ rr; action = update_action t1 r } 
		   in
		   Mls.add c { m with rows = r' :: m.rows } cm)
		cm cm
	  | { pat_node = Papp (c, pl) } :: rr ->
	      let m = Mls.find c cm in
	      let r' = { elements = pl @ rr; action = r.action } in
	      Mls.add c { m with rows = r' :: m.rows } cm
	  | { pat_node = Pas (p, x) } :: rr ->
	      let r = { r with action = mk_let x t1 r.action } in
	      dispatch (t_var x) r cm
	in
	(* FIXME: turn this into tail-calls using fold_left + rev *)
	let cm = List.fold_right (dispatch t1) m.rows cm0 in
	let nbc = ref 0 in
	let cases = 
	  Mls.fold 
	    (fun c m acc -> 
	       incr nbc; 
	       let pat_vars = List.map pat_var (Hls.find vars_for c) in
	       let pat_c = pat_app c pat_vars ty in
	       (pat_c, matrix m) :: acc) 
	    cm []
	in
	let otherwise = matrix_variables m t1 (not_enough_for !nbc ty) in
	mk_case t1 (cases @ otherwise)

  and matrix_variables m t1 exhaustive = 
    let variable r mr = match r.elements with
      | [] -> 
	  assert false
      | p :: rr when is_var p -> 
	  let r' = { elements = rr; action = update_action t1 r } in
	  r' :: mr
      | _ -> 
	  mr
    in
    let mr = { values = List.tl m.values;
	       rows = List.fold_right variable m.rows [] } in
    if not exhaustive then
      [pat_wild t1.t_ty, matrix mr]
    else match mr.rows with
      | [] -> []
      | { action = a } :: _ -> raise (Unused a)

  let compile tl bl =
    matrix 
      { values = tl;
	rows = List.map (fun (pl, a) -> { elements = pl; action = a }) bl }

    
end

