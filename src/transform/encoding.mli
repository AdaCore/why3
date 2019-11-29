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

val ft_select_kept : (Env.env,Ty.Sty.t)  Trans.flag_trans
val ft_enco_kept   : (Env.env,Task.task) Trans.flag_trans
val ft_enco_poly   : (Env.env,Task.task) Trans.flag_trans

val encoding_smt  : Env.env -> Task.task Trans.trans
val encoding_tptp : Env.env -> Task.task Trans.trans

