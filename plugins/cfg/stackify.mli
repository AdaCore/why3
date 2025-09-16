(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3
open Cfg_ast

type labeled_block = label * block

type usage = Multi | One

type exp_tree =
  | Scope of label * usage * exp_tree * exp_tree
  | Loop  of (loop_clause * Ptree.ident option * Ptree.term * int option ref) list * exp_tree
  | Block of labeled_block


val entry : exp_tree -> labeled_block

val targets : cfg_term -> label list

val stackify : labeled_block list -> label -> exp_tree
