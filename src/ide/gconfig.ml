
open Format
open Why

type t = 
    { mutable window_width : int;
      mutable window_height : int;
      mutable tree_width : int;
      mutable task_height : int;
    }

let default = 
  { window_width = 1024;
    window_height = 768;
    tree_width = 512;
    task_height = 384;
  }

let conf_file = Filename.concat (Rc.get_home_dir ()) ".whyide.conf"

let save_config config =
  let ch = open_out conf_file in
  let fmt = formatter_of_out_channel ch in
  fprintf fmt "[main]@\n";
  fprintf fmt "width = %d@\n" config.window_width;
  fprintf fmt "height = %d@\n" config.window_height;
  fprintf fmt "tree_width = %d@\n" config.tree_width;
  fprintf fmt "task_height = %d@\n" config.task_height;
  fprintf fmt "@.";
  close_out ch

let load_main c (key, value) = 
  match key with
    | "width" -> c.window_width <- Rc.int value
    | "height" -> c.window_height <- Rc.int value
    | "tree_width" -> c.tree_width <- Rc.int value
    | "task_height" -> c.task_height <- Rc.int value
    | s -> 
        eprintf "Warning: ignore unknown key [%s] in whyide config file@." s
        
let load c (key, al) = 
  match key with
    | "main" :: _ ->
        List.iter (load_main c) al
    | s :: _ -> 
        eprintf "Warning: ignored unknown section [%s] in whyide config file@." s
    | [] -> assert false
        
let read_config () =
  try
    let rc = Rc.from_file conf_file in
    let c = default in
    List.iter (load c) rc;
    c
  with
    | Failure "lexing" -> 
        eprintf "Warning: syntax error in whyide config file@.";
        default
    | Not_found ->
        eprintf "Warning: no whyide config file, using default values@.";
        default
    


(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. bin/whyide.opt"
End: 
*)
