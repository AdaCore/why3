(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Format
open Util

(* Error handling *)

exception SyntaxError
exception ExtraParameters of string
exception MissingParameters of string
exception UnknownSection of string
exception UnknownField of string
exception MissingSection of string
exception MissingField of string
exception DuplicateSection of string
exception DuplicateField of string * Rc.rc_value * Rc.rc_value
exception StringExpected of string * Rc.rc_value
exception IdentExpected of string * Rc.rc_value
exception IntExpected of string * Rc.rc_value
exception DuplicateProver of string

let error ?loc e = match loc with
  | None -> raise e
  | Some loc -> raise (Loc.Located (loc, e))

(* lib and shared dirs *)

let libdir =  
    try
      Sys.getenv "WHY3LIB"
    with Not_found -> Config.libdir

let datadir =
    try
      Sys.getenv "WHY3DATA"
    with Not_found -> Config.datadir




(* conf files *)

let print_rc_value fmt = function
  | Rc.RCint i -> fprintf fmt "%d" i
  | Rc.RCbool b -> fprintf fmt "%B" b
  | Rc.RCfloat f -> fprintf fmt "%f" f
  | Rc.RCstring s -> fprintf fmt "\"%s\"" s
  | Rc.RCident s -> fprintf fmt "%s" s

let () = Exn_printer.register (fun fmt e -> match e with
  | SyntaxError ->
      fprintf fmt "syntax error"
  | ExtraParameters s ->
      fprintf fmt "section '%s': header too long" s
  | MissingParameters s ->
      fprintf fmt "section '%s': header too short" s
  | UnknownSection s ->
      fprintf fmt "unknown section '%s'" s
  | UnknownField s ->
      fprintf fmt "unknown field '%s'" s
  | MissingSection s ->
      fprintf fmt "section '%s' is missing" s
  | MissingField s ->
      fprintf fmt "field '%s' is missing" s
  | DuplicateSection s ->
      fprintf fmt "section '%s' is already given" s
  | DuplicateField (s,u,v) ->
      fprintf fmt "cannot set field '%s' to %a, as it is already set to %a"
        s print_rc_value v print_rc_value u
  | StringExpected (s,v) ->
      fprintf fmt "cannot set field '%s' to %a: a string is expected"
        s print_rc_value v
  | IdentExpected (s,v) ->
      fprintf fmt "cannot set field '%s' to %a: an identifier is expected"
        s print_rc_value v
  | IntExpected (s,v) ->
      fprintf fmt "cannot set field '%s' to %a: an integer is expected"
        s print_rc_value v
  | DuplicateProver s ->
      fprintf fmt "prover %s is already listed" s
  | e -> raise e)

(* Configuration file *)

type config_prover = {
  name    : string;   (* "Alt-Ergo v2.95 (special)" *)
  command : string;   (* "exec why-limit %t %m alt-ergo %f" *)
  driver  : string;   (* "/usr/local/share/why/drivers/ergo-spec.drv" *)
  version : string;   (* "v2.95" *)
  editor  : string;
}

type main = {
  loadpath  : string list;  (* "/usr/local/share/why/theories" *)
  timelimit : int;
  memlimit  : int;
  running_provers_max : int;
}

type ide = {
  window_width : int;
  window_height : int;
  tree_width : int;
  task_height : int;
  verbose : int;
  default_editor : string;
}

type config = {
  conf_file : string;       (* "/home/innocent_user/.why.conf" *)
  provers   : config_prover Mstr.t;   (* indexed by short identifiers *)
  main      : main;
  ide       : ide;
}

let default_main = {
  loadpath = [Filename.concat Config.why_libdir "theories"];
  timelimit = 10;
  memlimit = 0;
  running_provers_max = 2;
}

let default_ide =
  { window_width = 1024;
    window_height = 768;
    tree_width = 512;
    task_height = 384;
    verbose = 0;
    default_editor = "";
  }

let default_config =
  { conf_file = Filename.concat (Rc.get_home_dir ()) ".why.conf";
    provers   = Mstr.empty;
    main      = default_main;
    ide       = default_ide;
  }

let to_string key = function
  | Rc.RCstring s -> s
  | v -> error (StringExpected (key,v))

let to_ident key = function
  | Rc.RCident s -> s
  | v -> error (IdentExpected (key,v))

let to_int key = function
  | Rc.RCint i -> i
  | v -> error (IntExpected (key,v))

let set_string key r v = match !r with
  | Some u -> error (DuplicateField (key,Rc.RCstring u,v))
  | None -> r := Some (to_string key v)

let set_ident key r v = match !r with
  | Some u -> error (DuplicateField (key,Rc.RCident u,v))
  | None -> r := Some (to_ident key v)

let set_int key r v = match !r with
  | Some u -> error (DuplicateField (key,Rc.RCint u,v))
  | None -> r := Some (to_int key v)

let get_field f = function
  | None -> error (MissingField f)
  | Some v -> v

let absolute_filename dirname f =
  if Filename.is_relative f then
    Filename.concat dirname f
  else
    f

let load_prover dirname al =
  let nam = ref None in
  let cmd = ref None in
  let drv = ref None in
  let version = ref None in
  let editor = ref "" in
  let load (key, value) = match key with
    | "name"        -> set_string key nam value
    | "command"     -> set_string key cmd value
    | "driver"      -> set_string key drv value;
	               drv := option_map (absolute_filename dirname) !drv
    | "version"     -> set_string key version value
    | "editor"      -> editor := Rc.string value
    | _             -> error (UnknownField key)
  in
  List.iter load al;
  { name    = get_field "name" !nam;
    command = get_field "command" !cmd;
    driver  = get_field "driver" !drv;
    version = get_field "version" !version;
    editor  = !editor;
  }

let load_main dirname main al =
  let lp = ref [] in
  let tl = ref None in
  let ml = ref None in
  let rp = ref None in
  let load (key, value) = match key with
    | "library"   -> 
	lp := absolute_filename dirname (to_string key value) :: !lp
    | "timelimit" -> set_int key tl value
    | "memlimit"  -> set_int key ml value
    | "running_provers_max" -> set_int key rp value
    | _           -> () (*error (UnknownField key)*)
  in
  List.iter load al;
  (* let none_if_null d = function None -> d | Some 0 -> None | v -> v in *)
  { loadpath  = List.rev !lp;
    timelimit = default_option main.timelimit !tl;
    memlimit  = default_option main.memlimit !ml;
    running_provers_max = default_option main.running_provers_max !rp
  }


let load_ide ide al =
  let width = ref None in
  let height = ref None in
  let tree_width = ref None in
  let task_height = ref None in
  let verbose = ref None in
  let default_editor = ref None in
  let load (key, value) = match key with
    | "window_width"   -> set_int key width value
    | "window_height"  -> set_int key height value
    | "tree_width" -> set_int key tree_width value
    | "task_height" -> set_int key task_height value
    | "verbose" -> set_int key verbose value
    | "default_editor" -> set_string key default_editor value
    | _           -> error (UnknownField key)
  in
  List.iter load al;
  { window_height = default_option ide.window_height !height;
    window_width = default_option ide.window_width !width;
    tree_width = default_option ide.tree_width !tree_width;
    task_height = default_option ide.task_height !task_height;
    verbose = default_option ide.verbose !verbose;
    default_editor = default_option ide.default_editor !default_editor;
  }


let read_config conf_file =
  let filename = match conf_file with
    | Some filename -> filename
    | None -> begin try Sys.getenv "WHY_CONFIG" with Not_found ->
          if Sys.file_exists "why.conf" then "why.conf" else
          if Sys.file_exists ".why.conf" then ".why.conf" else
          let f = Filename.concat (Rc.get_home_dir ()) ".why.conf" in
	  if Sys.file_exists f then f else raise Not_found
        end
  in
  let dirname = Filename.dirname filename in
  let rc = try Rc.from_file filename with
    | Failure "lexing" -> error SyntaxError
  in
  let provers = ref Mstr.empty in
  let main = ref default_main in
  let have_main = ref false in
  let ide = ref default_ide in
  let have_ide = ref false in
  let load (key, al) = match key with
    | ["main"] when not !have_main ->
      main := load_main dirname !main al;
      have_main := true
    | ["main"] when !have_main -> error (DuplicateSection "main")
    | "main" :: _ -> error (ExtraParameters "main");
    | ["ide"] when not !have_ide ->
      ide := load_ide !ide al;
      have_ide := true
    | ["ide"] when !have_ide -> error (DuplicateSection "ide")
    | "ide" :: _ -> error (ExtraParameters "ide");
    | "prover" :: name :: rest ->
        if rest <> [] then error (ExtraParameters ("prover " ^ name));
        if Mstr.mem name !provers then error (DuplicateProver name);
        provers := Mstr.add name (load_prover dirname al) !provers
    | "prover" :: [] -> error (MissingParameters "prover")
    | s :: _ -> error (UnknownSection s)
    | [] -> assert false
  in
  List.iter load rc;
  { conf_file = filename;
    provers = !provers;
    main = !main;
    ide = !ide}

let read_config conf_file =
  try read_config conf_file with Not_found -> default_config

let save_config config =
  let ch = open_out config.conf_file in
  let fmt = Format.formatter_of_out_channel ch in
  fprintf fmt "[main]@\n";
  List.iter (fprintf fmt "library = \"%s\"@\n") config.main.loadpath;
  fprintf fmt "timelimit = %d@\n"
    config.main.timelimit;
  fprintf fmt "memlimit = %d@\n"
    config.main.memlimit;
  fprintf fmt "running_provers_max = %d@\n"
    config.main.running_provers_max;
  fprintf fmt "@.";
  fprintf fmt "[ide]@\n";
  fprintf fmt "window_width = %d@\n" config.ide.window_width;
  fprintf fmt "window_height = %d@\n" config.ide.window_height;
  fprintf fmt "tree_width = %d@\n" config.ide.tree_width;
  fprintf fmt "task_height = %d@\n" config.ide.task_height;
  fprintf fmt "verbose = %d@\n" config.ide.verbose;
  fprintf fmt "default_editor = \"%s\"@\n" config.ide.default_editor;
  fprintf fmt "@.";
  let print_prover name prover =
    fprintf fmt "[prover %s]@\n" name;
    fprintf fmt "name = \"%s\"@\n" prover.name;
    fprintf fmt "command = \"%s\"@\n" prover.command;
    fprintf fmt "driver = \"%s\"@\n@." prover.driver;
    fprintf fmt "version = \"%s\"@\n@." prover.version;
    fprintf fmt "editor = \"%s\"@\n@." prover.editor;
  in
  Mstr.iter print_prover config.provers;
  close_out ch

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
      mutable prover_command : string;
      mutable prover_driver : string;
      mutable prover_editor : string;
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
    prover_command = "";
    prover_driver = "";
    prover_editor = "";
    }

let load_prover d (key, value) =
  match key with
    | "name" -> d.prover_name <- Rc.string value
    | "exec" -> d.execs <- Rc.string value :: d.execs
    | "version_switch" -> d.version_switch <- Rc.string value
    | "version_regexp" -> d.version_regexp <- Rc.string value
    | "version_ok" -> d.versions_ok <- Rc.string value :: d.versions_ok
    | "version_old" -> d.versions_old <- Rc.string value :: d.versions_old
    | "command" -> d.prover_command <- Rc.string value
    | "driver" -> d.prover_driver <- Rc.string value
    | "editor" -> d.prover_editor <- Rc.string value
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

let detect_prover acc data =
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
                  eprintf "Warning: prover %s version %s is quite old, please \
                           consider upgrading to a newer version.@."
                    nam ver
                else
                  eprintf "Warning: prover %s version %s is not known to be \
                           supported, use it at your own risk!@." nam ver
              end;
            incr provers_found;
            let c = make_command com data.prover_command in
            Mstr.add data.prover_id
              {name = data.prover_name;
               version = ver;
               command = c;
               driver  = Filename.concat Config.why_libdir data.prover_driver;
               editor = data.prover_editor} acc
	  else
	    begin
              prover_tips_info := true;
	      eprintf "Warning: found prover %s but name/version not \
                       recognized by regexp `%s'@."
                data.prover_name data.version_regexp;
	      eprintf "Answer was `%s'@." s;
	      acc
	    end)
    acc
    data.execs


let run_auto_detection config =
  let l = read_auto_detection_data () in
  let detect = List.fold_left detect_prover Mstr.empty l in
  let length = Mstr.fold (fun _ _ i -> i+1) detect 0 in
  eprintf "%d provers detected.@." length;
  {config with provers = detect}
