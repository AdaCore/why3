(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2015   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

val debug_parse_only : Debug.flag

val debug_type_only : Debug.flag

val open_file : Env.env -> Env.pathname -> pure:bool -> unit

val close_file : unit -> Pmodule.pmodule Stdlib.Mstr.t

val open_module : Ptree.ident -> theory:bool -> unit

val close_module : Ptree.loc -> unit

val open_namespace : Ptree.ident -> unit

val close_namespace : Ptree.loc -> import:bool -> unit

val add_decl : Ptree.loc -> Ptree.decl -> unit

val use_clone : Ptree.loc -> Ptree.use_clone -> unit
