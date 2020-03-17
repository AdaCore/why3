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

(* Dummy implementation for mpfr that always raise Not_implemented *)

exception Not_Implemented

type mpfr_rnd_t =
  | To_Nearest
  | Toward_Zero
  | Toward_Plus_Infinity
  | Toward_Minus_Infinity
  | Away_From_Zero
  | Faithful

type sign = Positive | Negative

type mpfr_float = unit

let set_emin _ = ()
let set_emax _ = ()
let set_default_prec _ = ()

(* Elementary operations *)
let add ?rnd:_ ?prec:_ _ _ = raise Not_Implemented
let neg ?rnd:_ ?prec:_ _   = raise Not_Implemented
let mul ?rnd:_ ?prec:_ _ _ = raise Not_Implemented
let div ?rnd:_ ?prec:_ _ _ = raise Not_Implemented
let sqrt ?rnd:_ ?prec:_ _  = raise Not_Implemented
let sub ?rnd:_ ?prec:_ _ _ = raise Not_Implemented
let abs ?rnd:_ ?prec:_ _ = raise Not_Implemented
let fma ?rnd:_ ?prec:_ _ _ _ = raise Not_Implemented
let rint ?rnd:_ ?prec:_ _ = raise Not_Implemented
let exp ?rnd:_ ?prec:_ _ = raise Not_Implemented
let log ?rnd:_ ?prec:_ _ = raise Not_Implemented


let min ?rnd:_ ?prec:_ _ _ = raise Not_Implemented
let max ?rnd:_ ?prec:_ _ _ = raise Not_Implemented

let signbit _ = raise Not_Implemented

let subnormalize ?rnd:_ _ = () (* Used outside of try *)

let make_from_str ?prec:_ ?rnd:_ ?base:_ _ = ()
let make_from_int ?prec:_ ?rnd:_ _ = ()
let make_zero ?prec:_ _ = ()

let get_formatted_str ?rnd:_ ?base:_ ?size:_ _ = "Error: MPFR not configured"

(* Comparison functions *)

let greater_p _ _      = raise Not_Implemented
let greaterequal_p _ _ = raise Not_Implemented
let less_p _ _         = raise Not_Implemented
let lessequal_p _ _    = raise Not_Implemented
let equal_p _ _        = raise Not_Implemented
let lessgreater_p _ _  = raise Not_Implemented

let zero_p _ = raise Not_Implemented
let nan_p _ = raise Not_Implemented
let inf_p _ = raise Not_Implemented

(* Constants *)
let const_pi ?rnd:_ _ = ()
