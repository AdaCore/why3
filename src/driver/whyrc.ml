
open Format

let default_why3rc_file () = 
  let home = Rc.get_home_dir () in
  let dir = Filename.concat home ".why" in
  (* TODO: create dir if not exists *)
  Filename.concat dir "why3rc"

let known_provers : (string, string * Driver.driver option ref) Hashtbl.t = 
  Hashtbl.create 7  

let load_prover_info info =
  let name = ref "" in
  let driv = ref "" in
  List.iter
    (function 
       | ("name",Rc.RCstring s) -> name := s
       | ("driver",Rc.RCstring s) -> driv := s
       | (field,_) ->
	   eprintf 
	     "Warning: ignored field `%s' in section [prover] of rc file@." 
	     field)
    info;
  Hashtbl.add known_provers !name (!driv,ref None)

let config_file = ref ""

let read_config_file ?(name = default_why3rc_file()) () =
  if !config_file <> "" then begin
    eprintf "Whyrc.read_config_file: cannot load config file twice@.";
    exit 2;
  end;
  config_file := name;
  let rc = Rc.from_file name in
  List.iter
    (fun (key,args) ->
       match key with
	 | "prover" -> load_prover_info args
	 | _ -> 
	     eprintf 
	       "Warning: ignored section [%s] in config file '%s'@." key name)
    rc

let get_driver name env = 
  if !config_file = "" then begin
    eprintf "Whyrc.get_driver: config file not loaded yet@.";
    exit 2;
  end;
  let (file,driv) = Hashtbl.find known_provers name in
  match !driv with
    | Some d -> d
    | None ->
	let d = Driver.load_driver file env in
	driv := Some d;
	d

let add_driver_config id file cmd =
    (* TODOL the command [cmd] should be inserted in the template [file] 
       and the result copied into ".why/<id>.drv" 
       corresponding values must be added into [known_provers]
    *)
  Hashtbl.add known_provers id (file, ref None)
       
let save () =
  if !config_file = "" then begin
    eprintf "Whyrc.save: config file not loaded yet@.";
    exit 2;
  end;
  let ch = open_out !config_file in
  let fmt = Format.formatter_of_out_channel ch in
  Hashtbl.iter
    (fun name (driv,_) -> 
       fprintf fmt "[prover]@.";
       fprintf fmt "name = \"%s\"@." name;
       fprintf fmt "driver = \"%s\"@." driv;
       fprintf fmt "@.")
    known_provers;
  close_out ch

    
let known_provers () = 
  Hashtbl.fold (fun key _ acc -> key::acc) known_provers []

