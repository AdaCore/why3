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
open Graph.Pack.Digraph
open Graph.Pack.Graph

(** module used to reduce formulae to Conjonctive Normal Form *)
module CNF = struct


end


(** module used to compute the graph of constants *)
module GraphConstant = struct

end

(** module used to compute the directed graph of predicates *)
module GraphPredicate = struct


end

(** module that makes the final selection *)
module Select = struct



end

(* TODO : think of a correct way to insert this kind of transformation *)
(** the transformation to be registered *)
let hypothesis_selection =
  Register.store (fun () ->
    Trans.identity)


let _ = Register.register_transform
  "hypothesis_selection" hypothesis_selection

