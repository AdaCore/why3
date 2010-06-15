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

(**s Transformation which removes most hypothesis, only keeping the one
a graph-based heuristic finds close enough to the goal *)

open Util
open Ident
open Ty
open Term
open Decl
open Task

(* requires ocamlgraph. TODO : recode this inside *)
open Graph.Persistent

module Int_Dft = struct
  type t = int
  let compare = Pervasives.compare
  let default = max_int
end

module GP = Digraph.AbstractLabeled(struct type t = Term.lsymbol end)(Int_Dft)
module GC = Graph.AbstractLabeled(struct type t = int end)(Int_Dft)			    
module FmlaHashtbl =
  Hashtbl.Make(struct type t = Term.fmla
		      let equal x y = x.f_tag = y.f_tag
		      let hash x = x.f_tag
	       end)
module SymbHashtbl = 
  Hashtbl.Make(struct type t = Term.lsymbol
		      let equal x y = x.ls_name.id_tag = y.ls_name.id_tag
		      let hash x = x.ls_name.id_tag
	       end)

let err = Format.err_formatter

module Util = struct
  let print_clause fmt = Format.fprintf fmt "@[[%a]@]"
    (Pp.print_list Pp.comma Pretty.print_fmla)
  let print_clauses fmt = Format.fprintf fmt "[%a]@."
    (Pp.print_list Pp.comma print_clause)
  
  (** all combinations of elements of left and right *)
  let map_complete combinator left right =
    let explorer left_elt =
      List.map (fun right_elt -> combinator left_elt right_elt) right in
    List.flatten (List.map explorer left)
end


(** module used to reduce formulae to Normal Form *)
module NF = struct (* add memoization, one day ? *)

  (* TODO !*)
  (** all quantifiers in prenex form *)
  let prenex_fmla fmla =
    Format.fprintf err "prenex_fmla : @[%a@]@." Pretty.print_fmla fmla;
    fmla

  (** creates a fresh formula representing a quantified formula *)
  let create_fmla (vars:Term.vsymbol list) : Term.fmla =
    let pred = create_psymbol (id_fresh "temoin")
      (List.map (fun var -> var.vs_ty) vars) in
    f_app pred (List.map t_var vars)


  (** transforms a formulae into its Normal Form as a list of clauses.
      The first argument is a hastable from formulae to formulae.
      A clause is a list of formulae *)
  let rec transform fmlaTable fmla =
    Format.fprintf err "transform : @[%a@]@." Pretty.print_fmla fmla;
    match fmla.f_node with
    | Fquant (_,f_bound) ->
	let var,_,f =  f_open_quant f_bound in
	traverse fmlaTable fmla var f
    | Fbinop (_,_,_) ->
	let clauses = split fmla in
	Format.fprintf err "split : @[%a@]@." Util.print_clause clauses;
	begin match clauses with
	  | [f] -> begin match f.f_node with
	      | Fbinop (For,f1,f2) ->
		  let left = transform fmlaTable f1 in
		  let right = transform fmlaTable f2 in
		  Util.map_complete List.append left right
	      | _ -> [[f]]
	    end
	  | _ -> List.concat (List.map (transform fmlaTable) clauses)
	end
    | Fnot f -> handle_not fmlaTable fmla f
    | Fapp (_,_) -> [[fmla]]
    | Ftrue | Ffalse -> [[fmla]]
    | Fif (_,_,_) -> failwith "if formulae not handled"
    | Flet (_,_) -> failwith "let formulae not handled"
    | Fcase (_,_) -> failwith "case formulae not handled"
  and traverse fmlaTable old_fmla vars fmla = match fmla.f_node with
    | Fquant (_,f_bound) ->
	let var,_,f = f_open_quant f_bound in
	traverse fmlaTable old_fmla (var@vars) f
    | _ -> (* TODO !! remember link between new term and old quantified formula *)
	if FmlaHashtbl.mem fmlaTable fmla then
	  [[FmlaHashtbl.find fmlaTable fmla]]
	else
	  let new_fmla = create_fmla vars in
	  FmlaHashtbl.add fmlaTable old_fmla new_fmla;
	  FmlaHashtbl.add fmlaTable new_fmla new_fmla;
	  [[new_fmla]]
  and skipPrenex fmlaTable fmla = match fmla.f_node with
    | Fquant (_,f_bound) ->
	let _,_,f = f_open_quant f_bound in
	skipPrenex fmlaTable f
    | _ -> transform fmlaTable fmla
  and split f = match f.f_node with
    | Fbinop (Fimplies,{f_node = Fbinop (For, h1, h2)},f2) ->
	(split (f_binary Fimplies h1 f2)) @ (split (f_binary Fimplies h2 f2))
    | Fbinop (Fimplies,f1,f2) ->
	let clauses = split f2 in
	if List.length clauses >= 2 then
	  List.concat
	    (List.map (fun f -> split (f_binary Fimplies f1 f)) clauses)
	else split (f_or (f_not f1) f2)
    | Fbinop (Fand,f1,f2) -> [f1; f2]
    | _ -> [f]
  and handle_not fmlaTable old_f f = match f.f_node with
    | Fquant (Fforall,f_bound) ->
	let vars,triggers,f1 = f_open_quant f_bound in
	transform fmlaTable (f_exists vars triggers (f_not f1))
    | Fnot f1 -> transform fmlaTable f1
    | Fbinop (Fand,f1,f2) ->
	transform fmlaTable (f_or (f_not f1) (f_not f2))
    | Fbinop (For,f1,f2) ->
	transform fmlaTable (f_and (f_not f1) (f_not f2))
    | Fbinop (Fimplies,f1,f2) ->
	transform fmlaTable (f_and f1 (f_not f2))
    | Fbinop (Fiff,f1,f2) ->
	transform fmlaTable (f_or (f_and f1 (f_not f2)) (f_and (f_not f1) f2))
    | _ -> [[old_f]] (* default case *)

  let make_clauses fmlaTable prop =
    let prenex_fmla = prenex_fmla prop in
    let clauses = skipPrenex fmlaTable prenex_fmla in
    Format.eprintf "==>@ @[%a@]@.@." Util.print_clauses clauses;
    clauses
end


(** module used to compute the graph of constants *)
module GraphConstant = struct

  let update gc _task_head = gc (* TODO *)

end

(** module used to compute the directed graph of predicates *)
module GraphPredicate = struct

  exception Exit of lsymbol

  let is_negative = function
    | { f_node = Fnot _ } -> true
    | _ -> false

  let extract_symbol fmla = 
    let rec search = function
      | { f_node = Fapp(p,_) } -> raise (Exit p)
      | f -> f_map (fun t->t) search f in
    try ignore (search fmla);
      Format.eprintf "invalid formula : ";
      Pretty.print_fmla Format.err_formatter fmla; assert false
    with Exit p -> p
 
  let find symbTbl x = try
    SymbHashtbl.find symbTbl x
  with Not_found ->
    let new_v = GP.V.create x in
    SymbHashtbl.add symbTbl x new_v;
    (* Format.eprintf "generating new vertex : %a@." Pretty.print_ls x; *)
    new_v

  (** analyse a single clause, and creates an edge between every positive
      litteral and every negative litteral of [clause] in [gp] graph. *)
  let analyse_clause symbTbl gp clause =
    let get_symbol x = find symbTbl (extract_symbol x) in
    let negative,positive = List.partition is_negative clause in
    let negative = List.map get_symbol negative in
    let positive = List.map get_symbol positive in
    let n = List.length clause in
    let add left gp right =
      try
	let old = GP.find_edge gp left right in
	if GP.E.label old <= n
	then gp (* old edge is fine *)
	else
	  let new_gp = GP.remove_edge_e gp old in
	  assert (not (GP.mem_edge new_gp left right));
	  GP.add_edge_e gp (GP.E.create left n right)
      with Not_found ->
	let e = GP.E.create left n right in
	GP.add_edge_e gp e in
    List.fold_left (* add an edge from every negative to any positive *)
      (fun gp left ->
	 List.fold_left (add left) gp positive) gp negative

  (** takes a prop, puts it in Normal Form and then builds a clause
      from it *)
  let analyse_prop fmlaTable symbTbl gp prop =
    let clauses = NF.make_clauses fmlaTable prop in
    List.fold_left (analyse_clause symbTbl) gp clauses

  let add_symbol symbTbl gp lsymbol =
    GP.add_vertex gp (find symbTbl lsymbol)

  (** takes a constant graph and a task_head, and add any interesting
      element to the graph it returns. *)
  let update fmlaTable symbTbl gp task_head =
    match task_head.task_decl with
      | Decl {d_node = Dprop (_,_,prop_decl) } ->
	  (* a proposition to analyse *)
	  analyse_prop fmlaTable symbTbl gp prop_decl
      | Decl {d_node = Dlogic logic_decls } ->
	  (* a symbol to add *)
	  List.fold_left
	    (fun gp logic_decl -> add_symbol symbTbl gp (fst logic_decl))
	    gp logic_decls
      | _ -> gp
end

(** module that makes the final selection *)
module Select = struct

  let get_predicates fmla =
    let id acc _ = acc in
    let rec explore acc fmla = match fmla.f_node with
      | Fapp (pred,_) -> pred::acc
      | _ -> f_fold id explore acc fmla
    in explore [] fmla

  let get_clause_predicates acc clause =
    let rec fmla_get_pred ?(pos=true) acc fmla = match fmla.f_node with
      | Fnot f -> fmla_get_pred ~pos:false acc f
      | Fapp (pred,_) -> (pred, (if pos then `Positive else `Negative))::acc
      | _ -> failwith "bad formula in get_predicates !"
    in List.fold_left fmla_get_pred acc clause

  (** get the predecessors of [positive] in the graph [gp], at distance <= [i]*)
  let rec get_predecessors i gp acc positive =
    if i < 0
    then acc
    else
      let acc = positive :: acc in
      List.fold_left (follow_edge gp i) acc (GP.pred_e gp positive)
  and follow_edge gp i acc edge =
    get_predecessors (i - GP.E.label edge) gp acc (GP.E.src edge)

  let rec get_successors _j _gp acc _negative = acc

  (* TODO : be clear... *)
  (** determines if a proposition is pertinent w.r.t the given goal formula,
      from data stored in the two graphes [gc] and [gp] given.
      [i] is the parameter of predicate graph ([gp]) based filtering.
      [j] is the parameter for dynamic constants ([gc]) dependency filtering *)
  let is_pertinent symTbl goal_clauses ?(i=4) ?(j=2) (_gc,gp) fmla =
    let is_negative = function
      | (_,`Negative) -> true
      | (_,`Positive) -> false in
    let find_secure symbTbl x =
      try SymbHashtbl.find symbTbl x
      with Not_found ->
	Format.eprintf "failure finding %a !@." Pretty.print_ls x;
	raise Not_found in
    let goal_predicates =
      List.fold_left get_clause_predicates [] goal_clauses in
    let predicates = get_predicates fmla in
    let negative,positive = List.partition is_negative goal_predicates in
    let negative,positive = List.map fst negative, List.map fst positive in
    let negative = List.map (find_secure symTbl) negative in
    let positive = List.map (find_secure symTbl) positive in
    let predicates = List.map (find_secure symTbl) predicates in
    (* list of negative predecessors of any positive predicate of the goal,
       at distance <= i *)
    let predecessors = List.fold_left (get_predecessors i gp) [] positive in
    let successors = List.fold_left (get_successors j gp) [] negative in
    (* a predicates is accepted iff all its predicates are close enough in
       successors or predecessors lists *)
    List.for_all
      (fun x -> if List.mem x predecessors || List.mem x successors then true
       else begin Format.eprintf "%a not close enough (dist %d)@."
	 Pretty.print_ls (GP.V.label x) i; false end)
      predicates

  (** preprocesses the goal formula and the graph, and returns a function
      that will accept or not axioms according to their relevance. *)
  let filter symTbl goal_clauses (gc,gp) =
    function decl -> (* TODO : clean up *)
      match decl.d_node with
	| Dtype _ | Dlogic _ | Dind _ -> [decl]
	| Dprop (Paxiom,_,fmla) -> (* filter only axioms *)
	    Format.eprintf "filter : @[%a@]@." Pretty.print_fmla fmla;
	    let return_value =
	      try
		if is_pertinent symTbl goal_clauses (gc,gp) fmla
		then [decl] else []
	      with Not_found ->
		[decl] in (* TODO : remove ! *)
	    if return_value = [] then Format.eprintf "NO@.@."
	    else Format.eprintf "YES@.@.";
	    return_value
	| Dprop(_,_,_) -> [decl]

end

(** if this is the goal, return it as Some goal after checking there is no other
    goal. Else, return the option *)
let get_goal task_head option =
  match task_head.task_decl with
    | Decl {d_node = Dprop(Pgoal,_,goal_fmla)} ->
	assert (option = None); (* only one goal ! *)
	Some goal_fmla
    | _ -> option

(** collects data on predicates and constants in task *)
let collect_info fmlaTable symbTbl =
  Trans.fold 
    (fun t (gc, gp, goal_option) ->
       GraphConstant.update gc t,
       GraphPredicate.update fmlaTable symbTbl gp t,
       get_goal t goal_option)
    (GC.empty, GP.empty, None)

(** the transformation, made from applying collect_info and
then mapping Select.filter *)
let transformation fmlaTable symbTbl task =
  (* first, collect data in 2 graphes *)
  let (gc,gp,goal_option) =
    Trans.apply (collect_info fmlaTable symbTbl) task in				
  (* get the goal *)
  let goal_fmla = match goal_option with
    | None -> failwith "no goal !"
    | Some goal_fmla -> goal_fmla in
  let goal_clauses = NF.make_clauses fmlaTable goal_fmla in
  (* filter one declaration at once *)
  Trans.apply
    (Trans.decl
       (Select.filter symbTbl goal_clauses (gc,gp)) None) task

(** the transformation to be registered *)
let hypothesis_selection =
  Register.store
    (fun () -> Trans.store
       (transformation (FmlaHashtbl.create 17) (SymbHashtbl.create 17)))

let _ = Register.register_transform 
  "hypothesis_selection" hypothesis_selection

(*
Local Variables: 
  compile-command: "unset LANG; cd ../..; make src/transform/hypothesis_selection.cmo"
End: 
*)

