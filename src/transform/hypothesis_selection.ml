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


module Util = struct
end


(** module used to reduce formulae to Normal Form *)
module NF = struct (* add memoization ? *)


end


(** module used to compute the graph of constants *)
module GraphConstant = struct

  let update gc task_head = assert false

end

(** module used to compute the directed graph of predicates *)
module GraphPredicate : sig
  val update : GP.t -> Task.task_hd -> GP.t
end = struct

  let analyse_prop gp prop = assert false

  let add_symbol gp lsymbol = GP.add_vertex gp
    (GP.V.create lsymbol)

  (** takes a constant graph and a task_head, and add any interesting
  element to the graph it returns. *)
  let update gp task_head =
    match task_head.task_decl with
      | Decl {d_node = Dprop (_,_,prop_decl) } ->
	  (* a proposition to analyse *)
	  analyse_prop gp prop_decl
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
let collect_info =
  Trans.fold (fun t (gc, gp) ->
    GraphConstant.update gc t, GraphPredicate.update gp t)
    (GC.empty, GP.empty)

(** the transformation, made from applying collect_info and
then mapping Select.filter *)
let transformation task =
  let (gc,gp) = Trans.apply collect_info task in
  Trans.apply (Trans.decl (Select.filter (gc,gp)) None) task

(** the transformation to be registered *)
let hypothesis_selection =
  Register.store
    (fun () -> Trans.store transformation)

let _ = Register.register_transform
  "hypothesis_selection" hypothesis_selection

(*
Local Variables: 
compile-command: "unset LANG; make -k -C ../.."
End: 
*)

