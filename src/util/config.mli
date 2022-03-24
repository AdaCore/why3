(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

val version : string
val editor : string
val libdir : string
val datadir : string
val localdir : string option

val libobjdir : string
val enable_ide : string
val enable_zarith : string
val enable_zip : string
val enable_coq_libs : string
val enable_coq_fp_libs : string
val enable_pvs_libs : string
val enable_isabelle_libs : string
val enable_hypothesis_selection : string
val enable_local : string
val enable_relocation : string
