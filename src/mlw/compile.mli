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

val clean_name : string -> string

val module_name : ?fname:string -> string list -> string -> string

module Translate : sig
  val module_ : Pmodule.pmodule -> Mltree.pmodule

  val pdecl_m : Pmodule.pmodule -> Pdecl.pdecl -> Mltree.decl list
end

module InlineFunctionCalls : sig

  val inline_attr : Ident.attribute
  val inlined_call_attr : Ident.attribute

  (* Inlines calls to functions that have the inline attribute.
     Resulting expressions have the inlined_attribute. *)
  val module_ : Mltree.pmodule -> Mltree.pmodule

end

module InlineProxyVars : sig

  (* Inlines proxy variables where it's correct to do so. *)
  val module_ : Mltree.pmodule -> Mltree.pmodule

end

module Transform : sig

  (* Applies all the above transformations. *)
  val module_ : Mltree.pmodule -> Mltree.pmodule
end
