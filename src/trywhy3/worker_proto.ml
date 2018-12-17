(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

type id = string
type loc = int * int * int * int
type why3_loc = string * (int * int * int) (* kind, line, column, length *)
type status = [`New | `Valid | `Unknown ]

type why3_command =  ParseBuffer of string
		   | ExecuteBuffer of string
		   | ProveAll
		   | Transform of [ `Prove of int | `Split | `Clean ] * id
		   | SetStatus of status * id

type why3_output = Error of string (* msg *)
                 | ErrorLoc of (loc * string) (* loc * msg *)
                 | Theory of id * string (* Theory (id, name) *)
                 | Task of (id * id * string * string * why3_loc list * string * int)
                 (* id, parent id, expl, code, location list, pretty, steps*)
                 | Result of string list
                 | UpdateStatus of status * id
                 | Warning of ((int*int) * string) list
                 | Idle

type prover_command = OptionSteps of int | Goal of id * string * int
type prover_output = Valid | Unknown of string | Invalid of string

let marshal a =
  Js.string (String.escaped (Marshal.to_string a [Marshal.No_sharing; Marshal.Compat_32]))

let unmarshal a =
  Marshal.from_string (Scanf.unescaped (Js.to_string a)) 0

let status_of_result = function
    (id, Valid) -> SetStatus(`Valid, id)
  | (id, _) -> SetStatus(`Unknown, id)

let log s = ignore (Firebug.console ## log (Js.string s))
let log_time s =
  let date = new%js Js.date_now in
  let date_str = string_of_float (date ## getTime /. 1000.) in
  log (date_str ^ " : " ^ s)
