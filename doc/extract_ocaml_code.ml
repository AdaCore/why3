
(*

Simple utility to extract a portion of a file

  extract_ocaml_code <path/file.ext> <id> <dir>

extracts the part of path/file.ext between lines containing anchors BEGIN{id} and END{id}
and puts the result in the file dir/file_id.ext

*)

open Format

let filename,section,output_dir =
  if Array.length Sys.argv = 4 then
    Sys.argv.(1), Sys.argv.(2), Sys.argv.(3)
  else
    begin
      eprintf "Usage: %s <path/file.ext> <id> <dir>@\n\
Extract the part of path/file.ext between lines containing anchors BEGIN{id} and END{id}@\n\
and puts the result in the file dir/file_id.ext@."
              Sys.argv.(0);
      exit 2
    end

let ch_in =
  try
    open_in filename
  with
    exn ->
    eprintf "Cannot open %s for reading: %s@." filename (Printexc.to_string exn);
    exit 1

let basename = Filename.basename filename

let ext = Filename.extension basename

let basename = Filename.remove_extension basename

let begin_re = Str.regexp_string ("BEGIN{" ^ section ^ "}")

let search_begin () =
  try
    while true do
      let l = input_line ch_in in
      try
        let _ = Str.search_forward begin_re l 0 in raise Exit
      with Not_found -> ()
    done
  with
    End_of_file ->
    eprintf "Error: opening anchor BEGIN{%s} not found in file %s@." section filename;
    close_in ch_in;
    exit 1
  | Exit -> ()


let end_re = Str.regexp_string ("END{" ^ section ^ "}")

let file_out = Filename.concat output_dir (basename ^ "_" ^ section ^ ext)

let ch_out =
  try
    open_out file_out
  with
    exn ->
    eprintf "Cannot open %s for writing: %s@." file_out (Printexc.to_string exn);
    close_in ch_in;
    exit 1

let search_end () =
  try
    while true do
      let l = input_line ch_in in
      try
        let _ = Str.search_forward end_re l 0 in raise Exit
      with Not_found ->
        output_string ch_out l;
        output_char ch_out '\n'
    done
  with
    End_of_file ->
    eprintf "Error: ending anchor END{%s} not found in file %s@." section filename;
    close_in ch_in;
    close_out ch_out;
    exit 1
  | Exit ->
    close_in ch_in;
    close_out ch_out

let () =
  search_begin (); search_end ()
