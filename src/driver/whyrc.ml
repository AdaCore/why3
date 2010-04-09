


let default_why3rc_file () = 
  let home = 
    try Sys.getenv "HOME"
    with Not_found -> 
      (* try windows env var *)
      try Sys.getenv "USERPROFILE"
      with Not_found -> ""
  in
  Filename.concat (Filename.concat home ".why") "why3rc"

let read_config_file ?(name = default_why3rc_file()) =
  assert false (* TODO *)


let known_provers () = 
  assert false (* TODO *)

let get_driver name env = 
  assert false (* TODO *)


let add_driver_config id file cmd =
  assert false (* TODO *)

let save () =
  assert false (* TODO *)
