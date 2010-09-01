
open Format
open Why

type prover_data =
    { prover_id : string;
      prover_name : string;
      prover_version : string;
      command : string;
      driver_name : string;
      driver : Driver.driver;
      mutable editor : string;
    }

type t = 
    { mutable window_width : int;
      mutable window_height : int;
      mutable tree_width : int;
      mutable task_height : int;
      mutable time_limit : int;
      mutable verbose : int;
      mutable max_running_processes : int;
      mutable provers : prover_data list;
      mutable default_editor : string;
    }

let default = 
  { window_width = 1024;
    window_height = 768;
    tree_width = 512;
    task_height = 384;
    time_limit = 2;
    verbose = 0;
    max_running_processes = 2;
    provers = [];
    default_editor = "";
  }

let conf_file = Filename.concat (Rc.get_home_dir ()) ".why.conf"

let save_prover fmt p =
  fprintf fmt "[prover %s]@\n" p.prover_id;
  fprintf fmt "name = \"%s\"@\n" p.prover_name;
  fprintf fmt "version = \"%s\"@\n" p.prover_version;
  fprintf fmt "command = \"%s\"@\n" p.command;
  fprintf fmt "driver = \"%s\"@\n" p.driver_name;  
  fprintf fmt "editor = \"%s\"@\n" p.editor;  
  fprintf fmt "@."

let save_config config =
  let ch = open_out conf_file in
  let fmt = formatter_of_out_channel ch in
  fprintf fmt "[main]@\n";
  fprintf fmt "width = %d@\n" config.window_width;
  fprintf fmt "height = %d@\n" config.window_height;
  fprintf fmt "tree_width = %d@\n" config.tree_width;
  fprintf fmt "task_height = %d@\n" config.task_height;
  fprintf fmt "time_limit = %d@\n" config.time_limit;
  fprintf fmt "verbose = %d@\n" config.verbose;
  fprintf fmt "max_processes = %d@\n" config.max_running_processes;
  fprintf fmt "default_editor = \"%s\"@\n" config.default_editor;  
  fprintf fmt "@.";
  List.iter (save_prover fmt) config.provers; 
  close_out ch

let load_main c (key, value) = 
  match key with
    | "width" -> c.window_width <- Rc.int value
    | "height" -> c.window_height <- Rc.int value
    | "tree_width" -> c.tree_width <- Rc.int value
    | "task_height" -> c.task_height <- Rc.int value
    | "time_limit" -> c.time_limit <- Rc.int value
    | "verbose" -> c.verbose <- Rc.int value
    | "max_processes" -> c.max_running_processes <- Rc.int value
    | "default_editor" -> c.default_editor <- Rc.string value
    | s -> 
        eprintf "Warning: ignore unknown key [%s] in whyide config file@." s



let get_prover_data env id name ver c d e = 
  try
    let dr = Driver.load_driver env d in
    { prover_id = id ;
      prover_name = name;
      prover_version = ver;
      command = c;
      driver_name = d;
      driver = dr; 
      editor = e;
    }
  with _e ->
    eprintf "Failed to load driver %s for prover %s. prover disabled@."
      d name;
    raise Not_found

let load_prover env id l =
  let name = ref "?" in
  let v = ref "?" in
  let c = ref "?" in
  let d = ref "?" in
  let e = ref "" in
  List.iter
    (fun (key, value) -> 
	match key with
	  | "name" -> name := Rc.string value
	  | "version" -> v := Rc.string value
          | "command" -> c := Rc.string value
          | "driver" -> d := Rc.string value
          | "editor" -> e := Rc.string value
	  | s -> 
            eprintf "Warning: ignore unknown key [%s] in prover data of whyide config file@." s)
    l;
  get_prover_data env id !name !v !c !d !e
        
let load env c (key, al) = 
  match key with
    | "main" :: _ -> List.iter (load_main c) al
    | "prover" :: id :: _ -> 
        c.provers <- load_prover env id al :: c.provers
    | s :: _ -> 
        eprintf "Warning: ignored unknown section [%s] in whyide config file@." s
    | [] -> assert false
        
let read_config env =
  try
    let rc = Rc.from_file conf_file in
    let c = default in
    List.iter (load env c) rc;
    c
  with
    | Failure "lexing" -> 
        eprintf "Warning: syntax error in whyide config file@.";
        default
    | Not_found ->
        eprintf "Warning: no whyide config file, using default values@.";
        default
    

(*

  boomy icons

*)

let image ?size f =
  let n = Filename.concat "" (* todo: libdir *) (Filename.concat "images" (f^".png"))
  in
  match size with
    | None ->
        GdkPixbuf.from_file n
    | Some s ->
        GdkPixbuf.from_file_at_size ~width:s ~height:s n

let iconname_default = "pause32"
let iconname_scheduled = "pause32"
let iconname_running = "play32"
let iconname_valid = "accept32"
let iconname_unknown = "help32"
let iconname_invalid = "delete32"
let iconname_timeout = "clock32"
let iconname_failure = "bug32"
let iconname_yes = "accept32"
let iconname_no = "delete32"
let iconname_directory = "folder32"
let iconname_file = "file32"
let iconname_prover = "wizard32"
let iconname_transf = "cutb32"

let image_default = ref (image ~size:20 iconname_default)
let image_scheduled = ref !image_default
let image_running = ref !image_default
let image_valid = ref !image_default
let image_unknown = ref !image_default
let image_invalid = ref !image_default
let image_timeout = ref !image_default
let image_failure = ref !image_default
let image_yes = ref !image_default
let image_no = ref !image_default
let image_directory = ref !image_default
let image_file = ref !image_default
let image_prover = ref !image_default
let image_transf = ref !image_default

let resize_images size =
  image_default := image ~size iconname_default;
  image_scheduled := image ~size iconname_scheduled;
  image_running := image ~size iconname_running;
  image_valid := image ~size iconname_valid;
  image_unknown := image ~size iconname_unknown;
  image_invalid := image ~size iconname_invalid;
  image_timeout := image ~size iconname_timeout;
  image_failure := image ~size iconname_failure;
  image_yes := image ~size iconname_yes;
  image_no := image ~size iconname_no;
  image_directory := image ~size iconname_directory;
  image_file := image ~size iconname_file;
  image_prover := image ~size iconname_prover;
  image_transf := image ~size iconname_transf;
  ()

let () = resize_images 20



let show_legend_window () =
  let dialog = GWindow.dialog ~title:"Why: legend of icons" () in      
  let vbox = dialog#vbox in
  let text = GText.view ~packing:vbox#add () in
  let b = text#buffer in
  let i s = b#insert ~iter:b#end_iter s in
  let ib i = b#insert_pixbuf ~iter:b#end_iter ~pixbuf:!i in
  i "== icons in the tree view on the left ==\n";
  i "\n";
  ib image_directory;
  i "A theory, containing a set of goals\n";
  ib image_file;
  i "A goal\n";
  ib image_prover;
  i "An external prover\n";
  ib image_transf;
  i "A split transformation\n";
  i "\n";
  i "== icons in the satatus column\n";
  i "\n";
  ib image_scheduled;
  i "external proof scheduled by not started yet\n";
  ib image_running;
  i "external proof is running\n";
  ib image_valid;
  i "goal is proved/theory is fully verified\n";
  ib image_timeout;
  i "external prover reached the time limit\n";
  ib image_unknown;
  i "external prover answer was not conclusive\n";
  ib image_failure;
  i "external prover call failed\n";
  i "\n";
  dialog#add_button "Close" `CLOSE ;
  let ( _ : GWindow.Buttons.about) = dialog#run () in
  dialog#destroy ()


let show_about_window () =
  let about_dialog = 
    GWindow.about_dialog 
      ~name:"Why" 
      ~authors:["Francois Bobot";
                "Jean-Christophe Filliatre";
                "Johannes Kanig";
                "Claude Marche";
                "Andrei Paskevich"
               ]
      ~copyright:"Copyright 2010"
      ~license:"Gnu Lesser General Public License"
      ~website:"http://why.lri.fr"
      ~website_label:"Click here for the web site"
      ~version:"3.0 alpha"
      ()
  in      
  let ( _ : GWindow.Buttons.about) = about_dialog#run () in
  about_dialog#destroy ()

let preferences c =
  let dialog = GWindow.dialog ~title:"Why: preferences" () in      
  let vbox = dialog#vbox in
  let notebook = GPack.notebook ~packing:vbox#add () in
  (** page 1 **)
  let label1 = GMisc.label ~text:"General" () in
  let page1 =
    GPack.vbox ~homogeneous:false ~packing:
      (fun w -> ignore(notebook#append_page ~tab_label:label1#coerce w)) ()
  in 
  (* debug mode ? *)
  let debugmode = 
    GButton.check_button ~label:"debug" ~packing:page1#add ()
      ~active:(c.verbose > 0)
  in
  let (_ : GtkSignal.id) = 
    debugmode#connect#toggled ~callback:
      (fun () -> c.verbose <- 1 - c.verbose)
  in
  (* timelimit ? *)
  let hb = GPack.hbox ~homogeneous:false ~packing:page1#add () in
  let _ = GMisc.label ~text:"Time limit" ~packing:hb#add () in
  let timelimit_spin = GEdit.spin_button ~digits:0 ~packing:hb#add () in
  timelimit_spin#adjustment#set_bounds ~lower:2. ~upper:300. ~step_incr:1. ();
  timelimit_spin#adjustment#set_value (float_of_int c.time_limit);
  let (_ : GtkSignal.id) = 
    timelimit_spin#connect#value_changed ~callback:
      (fun () -> c.time_limit <- timelimit_spin#value_as_int)
  in
  (* nb of processes ? *)
  let hb = GPack.hbox ~homogeneous:false ~packing:page1#add () in
  let _ = GMisc.label ~text:"Nb of processes" ~packing:hb#add () in
  let nb_processes_spin = GEdit.spin_button ~digits:0 ~packing:hb#add () in
  nb_processes_spin#adjustment#set_bounds ~lower:1. ~upper:16. ~step_incr:1. ();
  nb_processes_spin#adjustment#set_value (float_of_int c.max_running_processes);
  let (_ : GtkSignal.id) = 
    nb_processes_spin#connect#value_changed ~callback:
      (fun () -> c.max_running_processes <- nb_processes_spin#value_as_int)
  in
  (** page 2 **)
  let label2 = GMisc.label ~text:"Provers" () in
  let _page2 = GMisc.label ~text:"This page should display detected provers" 
    ~packing:(fun w -> ignore(notebook#append_page ~tab_label:label2#coerce w)) () 
  in
  dialog#add_button "Close" `CLOSE ;
  let ( _ : GWindow.Buttons.about) = dialog#run () in
  eprintf "saving IDE config file@.";
  save_config c;
  dialog#destroy ()





(* auto-detection of provers *)

type prover_kind = ATP | ITP
type prover_autodetection_data =
    { kind : prover_kind;
      prover_id : string;
      mutable prover_name : string;
      mutable execs : string list;
      mutable version_switch : string;
      mutable version_regexp : string;
      mutable versions_ok : string list;
      mutable versions_old : string list;
      mutable command : string;
      mutable driver : string;
    }

let default k id =
  { kind = k;
    prover_id = id;
    prover_name = "";
    execs = [];
    version_switch = "";
    version_regexp = "";
    versions_ok = [];
    versions_old = [];
    command = "";
    driver ="";
    }

let load_prover d (key, value) = 
  match key with
    | "name" -> d.prover_name <- Rc.string value
    | "exec" -> d.execs <- Rc.string value :: d.execs
    | "version_switch" -> d.version_switch <- Rc.string value
    | "version_regexp" -> d.version_regexp <- Rc.string value
    | "version_ok" -> d.versions_ok <- Rc.string value :: d.versions_ok
    | "version_old" -> d.versions_old <- Rc.string value :: d.versions_old
    | "command" -> d.command <- Rc.string value 
    | "driver" -> d.driver <- Rc.string value
    | s -> 
        eprintf "unknown key [%s] in autodetection data@." s;
        exit 1
        
let load acc (key,l) =
  match key with
    | ["ATP" ; id] -> 
        let d = default ATP id in
        List.iter (load_prover d) l;
        d :: acc
    | ["ITP" ; id] -> 
        let d = default ITP id in
        List.iter (load_prover d) l;
        d :: acc
    | s :: _ ->
        eprintf "unknown section [%s] in auto detection data@." s;
        exit 1
    | [] -> assert false
  
let read_auto_detection_data () =
  try
    let rc = Rc.from_file "prover-detection-data.conf" in
    List.fold_left load [] rc
  with
    | Failure "lexing" -> 
        eprintf "Syntax error in prover-detection-data.conf@.";
        exit 2
    | Not_found ->
        eprintf "prover-detection-data.conf not found@.";
        exit 2
    

let provers_found = ref 0

let prover_tips_info = ref false


let make_command exec com =
  let cmd_regexp = Str.regexp "%\\(.\\)" in
  let replace s = match Str.matched_group 1 s with
    | "e" -> exec
    | c -> "%"^c
  in
  Str.global_substitute cmd_regexp replace com

let detect_prover env acc data =
  List.fold_left
    (fun acc com ->
	let out = Filename.temp_file "out" "" in
        let cmd = com ^ " " ^ data.version_switch in
	let c = cmd ^ " > " ^ out in
	let ret = Sys.command c in
	if ret <> 0 then
	  begin
	    eprintf "command '%s' failed@." cmd;
	    acc
	  end
	else
	  let s = 
            try 
              let ch = open_in out in
              let s = ref (input_line ch) in
              while !s = "" do s := input_line ch done;
              close_in ch;
	      Sys.remove out;
              !s              
            with Not_found | End_of_file  -> ""
          in
	  let re = Str.regexp data.version_regexp in
	  if Str.string_match re s 0 then            
	    let nam = data.prover_name in
	    let ver = Str.matched_group 1 s in
            if List.mem ver data.versions_ok then 
	      eprintf "Found prover %s version %s, OK.@." nam ver
            else
              begin
                prover_tips_info := true;
                if List.mem ver data.versions_old then 
                  eprintf "Warning: prover %s version %s is quite old, please consider upgrading to a newer version.@." nam ver	    
                else
                  eprintf "Warning: prover %s version %s is not known to be supported, use it at your own risk!@." nam ver
              end;
            incr provers_found;
            let c = make_command com data.command in
	    get_prover_data env data.prover_id data.prover_name ver 
              c data.driver "" :: acc
	  else 
	    begin
              prover_tips_info := true;
	      eprintf "Warning: found prover %s but name/version not recognized by regexp `%s'@." data.prover_name data.version_regexp;
	      eprintf "Answer was `%s'@." s;
	      acc
	    end)
    acc
    data.execs


let run_auto_detection env gconfig =
  let l = read_auto_detection_data () in
  let detect = List.fold_left (detect_prover env) [] l in
  eprintf "%d provers detected.@." (List.length detect);
  gconfig.provers <- detect
    

(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. bin/whyide.opt"
End: 
*)
