(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)


(*
   TODO not implemented yet as forgetting functions.
   TODO only vars implemented as forgetting. We assume it is
   not necessary for others.

   When printing for errors reporting, we can have to print things that
   are not already in the task. So, printing those things will change
   the printer.
   Lets say that "tac" is a transformation that fails on "task" and that
   the error message is about a new variable "n". Then if you call "tac"
   several times on the same "task" (which is possible), you will get
   error messages with "n1" then "n2" then "n3" then...

   So we have these functions that should print elements inside term/variable...
   And they should forget the new printed things they just created.
   So the function printing all these should then forget all the ids that were
   recorded after it has printed everything.

*)

(*
val print_ls   : Trans.naming_table -> Format.formatter -> Term.lsymbol  -> unit
val print_tv   : Trans.naming_table -> Format.formatter -> Ty.tvsymbol   -> unit
val print_ts   : Trans.naming_table -> Format.formatter -> Ty.tysymbol   -> unit
val print_forget_vsty : Trans.naming_table -> Format.formatter -> Term.vsymbol  -> unit
val print_pr   : Trans.naming_table -> Format.formatter -> Decl.prsymbol -> unit
val print_pat  : Trans.naming_table -> Format.formatter -> Term.pattern  -> unit
val print_ty   : Trans.naming_table -> Format.formatter -> Ty.ty         -> unit
val print_term : Trans.naming_table -> Format.formatter -> Term.term     -> unit
val print_decl : Trans.naming_table -> Format.formatter -> Decl.decl     -> unit
*)
