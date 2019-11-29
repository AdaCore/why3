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

(** {1 Pretty printing of Why3 parse trees as Why3 source code} *)

val pp_pattern : Format.formatter -> Ptree.pattern -> unit

val pp_expr : Format.formatter -> Ptree.expr -> unit

val pp_term : Format.formatter -> Ptree.term -> unit

val pp_pty : Format.formatter -> Ptree.pty -> unit

val pp_decl : Format.formatter -> Ptree.decl -> unit

val pp_mlw_file : Format.formatter -> Ptree.mlw_file -> unit
(** [pp_mlw_file fmt t] outputs the parse tree [t] in formatter [fmt] *)
