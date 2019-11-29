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

val compile_match : Task.task Trans.trans

val meta_proj : Theory.meta (* [MTlsymbol; MTlsymbol; MTint; MTprsymbol] *)
(* projection symbol, constructor symbol, position, defining axiom *)

(* a type constructor generates an infinite type if either it is tagged by
   meta_infinite or one of its "material" arguments is an infinite type *)

val meta_infinite : Theory.meta (* [MTtysymbol] *)
val meta_material : Theory.meta (* [MTtysymbol; MTint] *)

(* extracts the material type arguments from [meta_material] *)
val get_material_args : Theory.meta_arg list list -> bool list Ty.Mts.t

(* tests if a type is infinite given [meta_infinite] and [meta_material] *)
val is_infinite_ty : Ty.Sts.t -> bool list Ty.Mts.t -> (Ty.ty -> bool)
