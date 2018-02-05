(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)


(*

These modules are used only for their side-effects at load time

Do not remove these from the .mli, it would trigger the new warning 60
of OCaml 4.04

*)

module Kept : sig end
module Lskept : sig end
module Lsinst : sig end
