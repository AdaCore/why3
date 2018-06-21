(*

Simple utility to extract a portion of the standard input

  extract_ocaml_code <id>

outputs the part of the standard input between anchors BEGIN{id} and END{id}

*)

let section =
  match Sys.argv with
  | [| _; section |] -> section
  | _ ->
    Format.eprintf "Usage: %s <id>@\n\
Output the part of the standard input between anchors BEGIN{id} and END{id}@."
      Sys.argv.(0);
    exit 2

let begin_re = Str.regexp_string ("BEGIN{" ^ section ^ "}")

let search_begin () =
  try
    while true do
      let l = read_line () in
      try
        let _ = Str.search_forward begin_re l 0 in raise Exit
      with Not_found -> ()
    done
  with
  | End_of_file ->
    Format.eprintf "Error: opening anchor BEGIN{%s} not found@." section;
    exit 1
  | Exit -> ()


let end_re = Str.regexp_string ("END{" ^ section ^ "}")

let search_end () =
  try
    while true do
      let l = read_line () in
      try
        let _ = Str.search_forward end_re l 0 in raise Exit
      with Not_found ->
        print_string l;
        print_char '\n'
    done
  with Exit -> ()

let () =
  search_begin (); search_end ()
