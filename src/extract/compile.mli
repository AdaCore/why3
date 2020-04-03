(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)


module Translate : sig
  val module_ : Pmodule.pmodule -> Mltree.pmodule

  val pdecl_m : Pmodule.pmodule -> Pdecl.pdecl -> Mltree.decl list
end


module RefreshLetBindings : sig

  (* Replace all let-bindings in the expression by fresh idents.
     This helps preserve unicity of let-bindings in presence of inlining. *)
  val expr : Mltree.expr -> Mltree.expr

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

module ExprSimplifications : sig

  (* Expression optimizations:
       - Optimizes trivial let-ins of the form `let x = e in x`.
       - Optimizes trivial matches of the form `match e1 with x -> e2 end`.
   *)
  val module_ : Mltree.pmodule -> Mltree.pmodule

end

module Transform : sig

  (* Applies all the above transformations. *)
  val module_ : Mltree.pmodule -> Mltree.pmodule
end
