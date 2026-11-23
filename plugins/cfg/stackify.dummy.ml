(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2026 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(********************************************************************)

open Why3
open Cfg_ast

type labeled_block = label * block

type usage = Multi | One

type exp_tree =
  | Scope of label * usage * exp_tree * exp_tree
  | Loop  of (loop_clause * Ptree.ident option * Ptree.term * int option ref) list * exp_tree
  | Block of labeled_block

(* Those functions are never ever called, they are here to satisfy
 * stackify.mli *)

let entry _ =
  failwith "not implemented"

let targets _ =
  failwith "not implemented"

let stackify _ =
  failwith "not implemented"
