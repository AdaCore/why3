type command =  ParseBuffer of string
              | ExecuteBuffer of string
              | Init


type output = Error of string (* msg *)
             | ErrorLoc of ((int*int*int*int) * string) (* loc * msg *)
             | Tasks of ((string * string) (* Theory (id, name) *)
                       * (string * string) (* Task (id, name *)
                       * (string * string * string)) (* VC (id, expl, code ) *)
             | Result of string list

type prover_answer = Valid | Unknown of string | Invalid of string

let marshal a =
  Js.string (String.escaped (Marshal.to_string a [Marshal.No_sharing; Marshal.Compat_32]))

let unmarshal a =
  Marshal.from_string (Scanf.unescaped (Js.to_string a)) 0



let log s = ignore (Firebug.console ## log (Js.string s))
let log_time s =
  let date = jsnew Js.date_now () in
  let date_str = string_of_float ((date ## getTime ()) /. 1000.) in
  log (date_str ^ " : " ^ s)
