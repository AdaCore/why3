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

val meta_inst   : Theory.meta
val meta_lskept : Theory.meta
val meta_lsinst : Theory.meta

module Lsmap : sig
  type t
  val empty : t
  val add : Term.lsymbol -> Ty.ty list -> Ty.ty option -> t -> t
end

val ft_select_inst   : (Env.env,Ty.Sty.t) Trans.flag_trans
val ft_select_lskept : (Env.env,Term.Sls.t) Trans.flag_trans
val ft_select_lsinst : (Env.env,Lsmap.t) Trans.flag_trans

val get_lsinst : Task.task -> Term.lsymbol Term.Mls.t
val get_syntax_map : Task.task -> Printer.syntax_map

val on_lsinst : (Term.lsymbol Term.Mls.t -> 'a Trans.trans) -> 'a Trans.trans
val on_syntax_map : (Printer.syntax_map -> 'a Trans.trans) -> 'a Trans.trans
