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
module FmlaHashtbl = Hashtbl.Make(struct type t = Term.fmla
					 let equal x y = x.f_tag = y.f_tag
					 let hash x = x.f_tag
				  end)

module Util = struct
end


(** module used to reduce formulae to Normal Form *)
module NF = struct (* add memoization, one day ? *)

  (** creates a fresh formula representing a quantified formula *)
  let create_fmla (vars:Term.vsymbol list) : Term.fmla =
    let pred = create_psymbol (id_fresh "temoin")
      (List.map (fun var -> var.vs_ty) vars) in
    f_app pred (List.map t_var vars)


  (** transforms a formulae into its Normal Form as a list of clauses.
  The first argument is a hastable from formulae to formulae *)
  let rec transform fmlaTable fmla = match fmla.f_node with
    | Fquant (_,f_bound) ->
	let var,_,f =  f_open_quant f_bound in
	traverse fmlaTable fmla var f
    | Fbinop (op,f1,f2) -> split_binop fmlaTable op f1 f2
    | Fnot f -> handle_not fmlaTable f
    | Fapp (_,_) -> [fmla]
    | Ftrue | Ffalse -> [fmla]
    | Fif (_,_,_) -> failwith "if formulae not handled"
    | Flet (_,_) -> failwith "let formulae not handled"
    | Fcase (_,_) -> failwith "case formulae not handled"
  and traverse fmlaTable old_fmla vars fmla = match fmla.f_node with
    | Fquant (_,f_bound) ->
	let var,_,f =  f_open_quant f_bound in
	traverse fmlaTable old_fmla (var@vars) f
    | _ ->
	let new_f = transform fmlaTable fmla in
	FmlaHashtbl.add fmlaTable old_fmla (create_fmla vars);
	assert false
  and split_binop fmlaTable op f1 f2 = match (op,f1,f2) with
    | Fimplies,{f_node = Fbinop (For, h1, h2)},f2 ->
	split_binop fmlaTable op h1 f2 @ split_binop fmlaTable op h2 f2
    | Fimplies,f1,f2 ->
	List.concat
	  (List.map (fun f -> split_binop fmlaTable op f1 f)
	     (transform fmlaTable f2))
    | Fand,f1,f2 ->
	transform fmlaTable f1 @ transform fmlaTable f2
    | _,_,_ ->
	[f_binary op f1 f2]
  and handle_not fmlaTable f = match f.f_node with
    | Fnot f1 -> transform fmlaTable f1
    | Fbinop (Fand,f1,f2) ->
	transform fmlaTable (f_or (f_not f1) (f_not f2))
    | Fbinop (For,f1,f2) ->
	transform fmlaTable (f_and (f_not f1) (f_not f2))
    | Fbinop (Fimplies,f1,f2) ->
	transform fmlaTable (f_and f1 (f_not f2))
    | Fbinop (Fiff,f1,f2) ->
	transform fmlaTable (f_or (f_and f1 (f_not f2)) (f_and (f_not f1) f2))
    | _ -> [f_not f] (* default case *)

end


(** module used to compute the graph of constants *)
module GraphConstant = struct

  let update gc task_head = gc (* TODO *)

end

(** module used to compute the directed graph of predicates *)
module GraphPredicate = struct

  (** analyse a single clause *)
  let analyse_clause gp clause = assert false

  let analyse_prop fmlaTable gp prop =
    let clauses = NF.transform fmlaTable prop in
    List.fold_left analyse_clause gp clauses

  let add_symbol gp lsymbol =
    GP.add_vertex gp (GP.V.create lsymbol)

  (** takes a constant graph and a task_head, and add any interesting
  element to the graph it returns. *)
  let update fmlaTable gp task_head =
    match task_head.task_decl with
      | Decl {d_node = Dprop (_,_,prop_decl) } ->
	  (* a proposition to analyse *)
	  analyse_prop fmlaTable gp prop_decl
      | Decl {d_node = Dlogic logic_decls } ->
	  (* a symbol to add *)
	  List.fold_left (fun gp logic_decl -> add_symbol gp (fst logic_decl))
	    gp logic_decls
      | _ -> gp
end

(** module that makes the final selection *)
module Select = struct

  let filter (gc,gp) decl = assert false

end

(** collects data on predicates and constants in task *)
let collect_info fmlaTable =
  Trans.fold (fun t (gc, gp) ->
    GraphConstant.update gc t, GraphPredicate.update fmlaTable gp t)
    (GC.empty, GP.empty)

(** the transformation, made from applying collect_info and
then mapping Select.filter *)
let transformation fmlaTable task =
  let (gc,gp) = Trans.apply (collect_info fmlaTable) task in
  Trans.apply (Trans.decl (Select.filter (gc,gp)) None) task

(** the transformation to be registered *)
let hypothesis_selection =
  Register.store
    (fun () -> Trans.store (transformation (FmlaHashtbl.create 17)))

let _ = Register.register_transform
  "hypothesis_selection" hypothesis_selection

(*
Local Variables: 
compile-command: "unset LANG; make -k -C ../.."
End: 
*)

