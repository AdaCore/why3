(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3
open Term

val debug : Debug.flag

val decl : Pgm_module.uc -> Pgm_ttree.decl -> Pgm_module.uc
  (** weakest preconditions: takes a module (under construction) as argument,
      and a program declaration, and adds the verification conditions for that
      declaration as goals (in the logic theory contained in the module). *)

val declare_global_regions : Pgm_types.T.pvsymbol -> unit

val declare_mutable_field : Ty.tysymbol -> int -> int -> unit
  (* [declare_mutable_field ts i j] indicates that region [i] in
     [ts] args correspond to the mutable field [j] of [ts] *)

val default_variant : lsymbol -> lsymbol -> term -> term -> term
  (* [default_variant le lt phi phi0] = 0 <= phi0 and phi < phi0 *)

