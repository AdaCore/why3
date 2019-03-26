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

(* [tr] gives a function that gives a set of attributes to the fresh elements
   generated during the revert. It allows in particular to add [@induction] for
   induction_ty_lex.
*)
val revert_tr_symbol:
  ?tr:(Term.lsymbol -> Ident.Sattr.t) ->
    Args_wrapper.symbol list -> Task.task Trans.trans
