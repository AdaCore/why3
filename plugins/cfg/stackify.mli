
open Why3
open Cfg_ast

type labeled_block = label * block

type usage = Multi | One

type exp_tree =
  | Scope of label * usage * exp_tree * exp_tree
  | Loop  of (Ptree.ident * Ptree.term) list * exp_tree
  | Block of labeled_block


val entry : exp_tree -> labeled_block

val targets : cfg_term -> label list

val stackify : labeled_block list -> label -> exp_tree
