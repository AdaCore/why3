(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2016   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

val debug_parse_only : Debug.flag

val debug_type_only : Debug.flag

val open_file : Env.env -> Env.pathname -> unit

val close_file : unit -> Pmodule.pmodule Stdlib.Mstr.t

val open_module : Ptree.ident -> unit

val close_module : Loc.position -> unit

val open_scope : Loc.position -> Ptree.ident -> unit

val close_scope : Loc.position -> import:bool -> unit

val add_decl : Loc.position -> Ptree.decl -> unit
