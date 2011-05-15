(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(** The aim of this translation is to obtain terms where all epsilon
 * abstractions are closed *)

(** We do this by applying the following rewriting rule:
  εx.P(x) => εF.(P(F@y₁@...@y_n)) where y₁...y_n are the free variable in P and
  @ is the higher-order application symbol.
  *)

open Term

type lambda_match =
  | Flam of vsymbol list * trigger * fmla
  | Tlam of vsymbol list * trigger * term
  | LNone


val destruct_lambda : term -> lambda_match
val is_lambda : term -> bool
