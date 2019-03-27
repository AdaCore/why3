(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* [tr] is a function that associates a symbol of the task with an attribute.
   This is used to add new attributes (such as @induction) on some quantified
   variables (see induction_arg_pr).
*)
val revert_tr_symbol:
  ?tr:(Args_wrapper.symbol -> Ident.attribute option) ->
    Args_wrapper.symbol list -> Task.task Trans.trans
