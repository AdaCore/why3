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

val debug : Debug.flag

type program_decl =
  | PDdecl of Ptree.decl
  | PDpdecl of Ptree.pdecl
  | PDuseclone of Ptree.use_clone
  | PDnamespace of string * bool * (Ptree.loc * program_decl) list

val decl :
  wp:bool -> Pgm_module.t Util.Mstr.t Env.library ->
  Theory.theory Util.Mstr.t ->
  Pgm_module.t Util.Mstr.t ->
  Pgm_module.uc -> (Ptree.loc * program_decl) -> Pgm_module.uc
