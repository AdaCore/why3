
open Format

let default_whyconf_file () = 
  let home = Rc.get_home_dir () in
  Filename.concat home ".why.conf"

type prover_info =
    {
      invocation : string;
      driver_file : string;
      mutable driver : Driver.driver option;
    }

let loadpath = ref []
let timelimit = ref 10

let get_loadpath () = !loadpath

let get_timelimit () = !timelimit

let known_provers : (string, prover_info) Hashtbl.t = 
  Hashtbl.create 7  

let load_prover_info info =
  let name = ref "" in
  let driv = ref "" in
  let invoc = ref "" in
  List.iter
    (function 
       | ("name",Rc.RCstring s) -> name := s
       | ("invocation",Rc.RCstring s) -> invoc := s
       | ("driver",Rc.RCstring s) -> driv := s
       | (field,_) ->
	   eprintf 
	     "Warning: ignored field `%s' in section [prover] of conf file@." 
	     field)
    info;
  Hashtbl.add known_provers !name 
    { invocation = !invoc; driver_file = !driv ; driver = None }


let load_main_settings args =
  List.iter
    (function
       | ("timelimit", Rc.RCint n) -> timelimit := n
       | ("loadpath", Rc.RCstring s) -> loadpath := s :: !loadpath
       | (field,_) ->
	   eprintf 
	     "Warning: ignored field `%s' in section [main] of conf file@." 
	     field)
    args

let config_file = ref ""

let read_config_file ?(name = default_whyconf_file()) () =
  if !config_file <> "" then begin
    eprintf "Whyconf.read_config_file: cannot load config file twice@.";
    exit 2;
  end;
  config_file := name;
  let rc = Rc.from_file name in
  List.iter
    (fun (key,args) ->
       match key with
	 | "prover" -> load_prover_info args
	 | "main" -> load_main_settings args
	 | _ -> 
	     eprintf 
	       "Warning: ignored section [%s] in config file '%s'@." key name)
    rc

let get_driver name env = 
  if !config_file = "" then begin
    eprintf "Whyconf.get_driver: config file not loaded yet@.";
    exit 2;
  end;
  let pi = Hashtbl.find known_provers name in
  match pi.driver with
    | Some d -> d
    | None ->
	let d = Driver.load_driver pi.driver_file env in
	pi.driver <- Some d;
	d

let add_driver_config id file cmd =
    (* TODO 
       check that id does not exist yet

       
       the command [cmd] should be inserted in the template [file] 
       and the result copied into ".why/<id>.drv" 
       corresponding values must be added into [known_provers]
    *)
  Hashtbl.add known_provers id 
    { invocation = cmd; driver_file = file; driver = None; }

let set_loadpath s = loadpath := s
let add_loadpath s = loadpath := s :: !loadpath
let set_timelimit n = timelimit := n
       
let save () =
  if !config_file = "" then begin
    eprintf "Whyconf.save: config file not loaded yet@.";
    exit 2;
  end;
  let ch = open_out !config_file in
  let fmt = Format.formatter_of_out_channel ch in
  fprintf fmt "[main]@.";
  List.iter
    (fun s ->
       fprintf fmt "loadpath = \"%s\"@." s)
    !loadpath;
  fprintf fmt "timelimit = %d@." !timelimit;
  fprintf fmt "@.";  
  Hashtbl.iter
    (fun name pi -> 
       fprintf fmt "[prover]@.";
       fprintf fmt "name = \"%s\"@." name;
       fprintf fmt "invocation= \"%s\"@." pi.invocation;
       fprintf fmt "driver = \"%s\"@." pi.driver_file;
       fprintf fmt "@.")
    known_provers;
  close_out ch

    
let known_provers () = 
  Hashtbl.fold (fun key _ acc -> key::acc) known_provers []

