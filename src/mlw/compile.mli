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

val clean_name : string -> string

val module_name : ?fname:string -> string list -> string -> string

module Translate : sig
  val module_ : Pmodule.pmodule -> Mltree.pmodule

  val pdecl_m : Pmodule.pmodule -> Pdecl.pdecl -> Mltree.decl list
end

module Transform : sig
  val module_ : Mltree.pmodule -> Mltree.pmodule
end
