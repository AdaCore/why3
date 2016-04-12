type id = string
type loc = int * int * int * int
type status = [`New | `Valid | `Unknown ]
type why3_command =  ParseBuffer of string
              | ExecuteBuffer of string
              | Transform of [ `Prove | `Split | `Clean ] * id
              | SetStatus of status * id

type why3_output = Error of string (* msg *)
                 | ErrorLoc of (loc * string) (* loc * msg *)
                 | Theory of id * string (* Theory (id, name) *)
                 | Task of (id * id * string * string * loc list) (* id, parent id, expl, code, location list *)
                 | Result of string list
                 | UpdateStatus of status * id

type prover_command = OptionSteps of int | Goal of id * string
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
  let date = jsnew Js.date_now () in
  let date_str = string_of_float ((date ## getTime ()) /. 1000.) in
  log (date_str ^ " : " ^ s)
