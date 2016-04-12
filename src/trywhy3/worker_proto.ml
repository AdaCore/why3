type id = string

type why3_command =  ParseBuffer of string
              | ExecuteBuffer of string


type why3_output = Error of string (* msg *)
             | ErrorLoc of ((int*int*int*int) * string) (* loc * msg *)
             | Tasks of ((id * string) (* Theory (id, name) *)
                       * (id * string) (* Task (id, name *)
                       * (id * string * string)) (* VC (id, expl, code ) *)
             | Result of string list

type prover_command = OptionSteps of int | Task of id * string

type prover_output = Valid | Unknown of string | Invalid of string

let marshal a =
  Js.string (String.escaped (Marshal.to_string a [Marshal.No_sharing; Marshal.Compat_32]))

let unmarshal a =
  Marshal.from_string (Scanf.unescaped (Js.to_string a)) 0



let log s = ignore (Firebug.console ## log (Js.string s))
let log_time s =
  let date = jsnew Js.date_now () in
  let date_str = string_of_float ((date ## getTime ()) /. 1000.) in
  log (date_str ^ " : " ^ s)
