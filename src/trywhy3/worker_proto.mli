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

open Js_of_ocaml

type id = int
type loc = int * int * int * int
type why3_loc = string * (int * int * int * int)
(** kind, start line, start char, end line, end char.
    Line numbers start from 1, cf [src/util/Loc.mli]. *)

type status = StNew | StValid | StUnknown
type transform = Prove of int | Split of int | Clean

type why3_command =
  | ParseBuffer of string * string * int
  | ExecuteBuffer of string * string
  | Transform of transform * id
  | SetStatus of status * id
  | GetFormats

type why3_output =
  | Error of string
  | ErrorLoc of loc * string
  | Theory of id * string
  | Task of id * id * string * string * why3_loc list * string * int
  | Result of string list
  | UpdateStatus of status * id
  | Warning of ((int*int) * string) list
  | Idle
  | Formats of (string * string list) list

type prover_command = id * string * int
type prover_output = Valid | Unknown of string | Invalid of string

val marshal : 'a -> Js.js_string Js.t
val unmarshal : Js.js_string Js.t -> 'a
