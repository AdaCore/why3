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

let () = Exn_printer.register
    (fun fmt e ->
      match e with
      | StratFailure(s,e) ->
          Format.fprintf fmt "@[Strategy `%s` failure:@ @[%a@]@]" s Exn_printer.exn_printer e
      | UnknownStrat(s) ->
          Format.fprintf fmt "Strategy `%s` not known" s
      | KnownStrat(s) ->
          Format.fprintf fmt "Strategy `%s` already known" s
      | _ -> raise e)

type proof_tree =
  | Sdo_nothing
  | Sapply_trans of string * string list * proof_tree list
  | Scont of string * string list * (Env.env -> Task.task -> proof_tree)
  | Scall_prover of
      (Whyconf.prover * float option * int option * int option) list * proof_tree

let named s f env (t : Task.task) =
  try f env t with e -> raise (StratFailure (s,e))

let named_args s f args env naming_table ff (t : Task.task) =
  try f args env naming_table ff t with e -> raise (StratFailure (s,e))

type strat = Env.env -> Task.task -> proof_tree
type strat_with_args = string list -> Env.env -> Trans.naming_table -> Env.fformat -> Task.task -> proof_tree

type gen_strat = Strat of strat | StratWithArgs of strat_with_args

type reg_strat = Pp.formatted * gen_strat

let strats : reg_strat Hstr.t = Hstr.create 17

let register_strat ~desc s strat =
  if Hstr.mem strats s then raise (KnownStrat s);
  Hstr.replace strats s (desc, Strat (fun env task -> named s strat env task))

let register_strat_with_args ~desc s strat =
  if Hstr.mem strats s then raise (KnownStrat s);
  Hstr.replace strats s (desc, StratWithArgs (fun args env naming_table ff task -> named_args s strat args env naming_table ff task))

let lookup_strat s =
  try snd (Hstr.find strats s) with
  | Not_found -> raise (UnknownStrat s)

let list_strats () = Hstr.fold (fun k (s, _) acc -> (k, s) :: acc) strats []
