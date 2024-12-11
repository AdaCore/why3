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

module Js = Js_of_ocaml.Js

type id = int
type loc = int * int * int * int
type why3_loc = string * (int * int * int * int)
type status = StNew | StValid | StUnknown
type transform = Prove of int | Split of int | Clean

type why3_command =
  | ParseBuffer of string * string * int
  | ExecuteBuffer of string * string
  | Transform of transform * id
  | SetStatus of status * id
  | GetFormats

type why3_output =
  | Error of string (* msg *)
  | ErrorLoc of loc * string (* loc * msg *)
  | Theory of id * string (* Theory (id, name) *)
  | Task of id * id * string * string * why3_loc list * string * int
  (* id, parent id, expl, code, location list, pretty, steps*)
  | Result of string list
  | UpdateStatus of status * id
  | Warning of ((int*int) * string) list
  | Idle
  | Formats of (string * string list) list

type prover_command = id * string * int
type prover_output = Valid | Unknown of string | Invalid of string

let marshal a =
  Js.string (String.escaped (Marshal.to_string a [Marshal.No_sharing; Marshal.Compat_32]))

let unmarshal a =
  Marshal.from_string (Scanf.unescaped (Js.to_string a)) 0
