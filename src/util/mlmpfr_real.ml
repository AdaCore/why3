(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* TODO This wrapper should eventually be removed ! *)

(* Exception to be raised if mpfr is not installed *)
exception Not_Implemented

include Mlmpfr

let get_formatted_str ?rnd ?base ?size mpfr_float =
  get_formatted_str ?rnd ?base ?size mpfr_float
