(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Stdlib
open Mlw_module

type mlw_contents = modul Mstr.t
type mlw_library = mlw_contents Env.library
type mlw_file = mlw_contents * Theory.theory Mstr.t

val open_file : mlw_library -> Env.pathname -> Ptree.incremental
val close_file : unit -> mlw_file
