open Why3.Json_base

let abort_with_message ~internal s =
  Format.printf "{%a, %a, %a}"
  (print_json_field "error" string) s
  (print_json_field "internal" bool) internal
  (print_json_field "results" (list int)) [];
  exit 1

let () =
  Printexc.set_uncaught_exception_handler
    (fun exn raw_backtrace ->
       let bt = Printexc.raw_backtrace_to_string raw_backtrace in
       let msg = Format.asprintf "%a\nBacktrace is the following:\n%s@."
           Why3.Exn_printer.exn_printer exn bt
       in
       abort_with_message ~internal:true msg)

let colon = ':'

let colon_split s =
   let acc : string list ref = ref [] in
   let last_index = ref (String.length s) in
   let cur_index = ref (String.length s - 1) in
   try
      while true do
         cur_index := String.rindex_from s (!cur_index - 1) colon;
         acc :=
            String.sub s (!cur_index + 1) (!last_index - !cur_index - 1):: !acc;
         last_index := !cur_index;
      done;
      !acc
   with Invalid_argument _ | Not_found ->
      String.sub s 0 (!last_index) :: !acc
