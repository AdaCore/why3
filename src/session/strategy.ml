(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** {2 User-defined strategies} *)

open Wstdlib

type instruction =
  | Icall_prover of
      (Whyconf.prover * float option * int option * int option) list
      (** timelimit (if none use default timelimit), memlimit (if none use
          default memlimit) steplimit (if none use no step limit) *)
  | Itransform of string * int  (** successor state on success *)
  | Igoto of int  (** goto state *)

type t = instruction array

exception StratFailure of string * exn
exception UnknownStrat of string
exception KnownStrat of string

type strat =
  | Sdo_nothing
  | Sapply_trans of string * string list * strat list
  | Scont of string * string list * (Env.env -> Task.task -> strat)
  | Scall_prover of
      (Whyconf.prover * float option * int option * int option) list * strat

let named s f env (t : Task.task) =
  try f env t with e -> raise (StratFailure (s,e))

type reg_strat = Pp.formatted * (Env.env -> Task.task -> strat)

let strats : reg_strat Hstr.t = Hstr.create 17

let register_strat ~desc s p =
  if Hstr.mem strats s then raise (KnownStrat s);
  Hstr.replace strats s (desc, fun env task -> named s p env task)

let lookup_strat s =
  try snd (Hstr.find strats s) with
  | Not_found -> raise (UnknownStrat s)

let list_strats () = Hstr.fold (fun k (s, _) acc -> (k, s) :: acc) strats []
