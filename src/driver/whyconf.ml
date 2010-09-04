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
open Rc

(* Error handling *)

exception SyntaxError
exception ExtraParameters of string
exception MissingParameters of string
exception UnknownSection of string
exception UnknownField of string
exception MissingSection of string
exception MissingField of string
exception DuplicateSection of string
(* exception DuplicateField of string * Rc.rc_value * Rc.rc_value *)
(* exception StringExpected of string * Rc.rc_value *)
(* exception IdentExpected of string * Rc.rc_value *)
(* exception IntExpected of string * Rc.rc_value *)
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
(*
let print_rc_value fmt = function
  | Rc.RCint i -> fprintf fmt "%d" i
  | Rc.RCbool b -> fprintf fmt "%B" b
  | Rc.RCfloat f -> fprintf fmt "%f" f
  | Rc.RCstring s -> fprintf fmt "\"%s\"" s
  | Rc.RCident s -> fprintf fmt "%s" s
*)
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
  (* | DuplicateField (s,u,v) -> *)
  (*     fprintf fmt "cannot set field '%s' to %a, as it is already set to %a"
  *)
  (*       s print_rc_value v print_rc_value u *)
  (* | StringExpected (s,v) -> *)
  (*     fprintf fmt "cannot set field '%s' to %a: a string is expected" *)
  (*       s print_rc_value v *)
  (* | IdentExpected (s,v) -> *)
  (*     fprintf fmt "cannot set field '%s' to %a: an identifier is expected"*)
  (*       s print_rc_value v *)
  (* | IntExpected (s,v) -> *)
  (*     fprintf fmt "cannot set field '%s' to %a: an integer is expected" *)
  (*       s print_rc_value v *)
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

type config = {
  conf_file : string;       (* "/home/innocent_user/.why.conf" *)
  config    : Rc.t  ;
}

let default_main = {
  loadpath = [Filename.concat Config.why_libdir "theories"];
  timelimit = 10;
  memlimit = 0;
  running_provers_max = 2;
}

let set_main config main =
  let section = empty_section in
  let section = set_stringl section "loadpath" main.loadpath in
  let section = set_int section "timelimit" main.timelimit in
  let section = set_int section "memlimit" main.memlimit in
  let section =
    set_int section "running_provers_max" main.running_provers_max in
  {config with config = set_section config.config "main" section}

let set_prover id prover family =
  let section = empty_section in
  let section = set_string section "name" prover.name in
  let section = set_string section "command" prover.command in
  let section = set_string section "driver" prover.driver in
  let section = set_string section "version" prover.version in
  let section = set_string section "editor" prover.editor in
  (id,section)::family

let set_provers config provers =
  let family = Mstr.fold set_prover provers [] in
  {config with config = set_family config.config "prover" family}

let default_config =
  {conf_file = Filename.concat (Rc.get_home_dir ()) ".why.conf";
   config = Rc.empty;
  }

let absolute_filename dirname f =
  if Filename.is_relative f then
    Filename.concat dirname f
  else
    f

let load_prover dirname provers (id,section) =
  Mstr.add id
    { name    = get_string section "name";
      command = get_string section "command";
      (* TODO command : absolute_filename dirname ? *)
      driver  = absolute_filename dirname (get_string section "driver");
      version = get_string ~default:"" section "version";
      editor  = get_string ~default:"" section "editor";
    } provers

let get_provers config =
  let dirname = Filename.dirname config.conf_file in
  let provers = get_family config.config "prover" in
  List.fold_left (load_prover dirname) Mstr.empty provers

let load_main dirname section =
  { loadpath  = List.map (absolute_filename dirname)
      (get_stringl ~default:default_main.loadpath section "loadpath");
    timelimit = get_int ~default:default_main.timelimit section "timelimit";
    memlimit  = get_int ~default:default_main.memlimit section "memlimit";
    running_provers_max =
      get_int ~default:default_main.running_provers_max section
        "running_provers_max";
  }

let get_main config =
  match get_section config.config "main" with
    | None -> default_main
    | Some main ->
      let dirname = Filename.dirname config.conf_file in
      load_main dirname main

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
  let rc = Rc.from_file filename in
  { conf_file = filename;
    config = rc;
  }

let read_config conf_file =
  try read_config conf_file with Not_found -> default_config

let save_config config = to_file config.conf_file config.config

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

let prover_keys =
  let add acc k = Sstr.add k acc in
  List.fold_left add Sstr.empty
    ["name";"exec";"version_switch";"version_regexp";
     "version_ok";"version_old";"command";
     "editor";"driver"]

let load_prover kind (id,section) =
  check_exhaustive section prover_keys;
  { kind = kind;
    prover_id = id;
    prover_name = get_string section "name";
    execs = get_stringl section "exec";
    version_switch = get_string section ~default:"" "version_switch";
    version_regexp = get_string section ~default:"" "version_regexp";
    versions_ok = get_stringl section ~default:[] "version_ok";
    versions_old = get_stringl section ~default:[] "version_old";
    prover_command = get_string section "command";
    prover_driver = get_string section "driver";
    prover_editor = get_string section ~default:"" "editor";
  }

let load rc =
  let atps = get_family rc "ATP" in
  let atps = List.map (load_prover ATP) atps in
  let itps = get_family rc "ITP" in
  let tps = List.fold_left (cons (load_prover ITP)) atps itps in
  tps

let read_auto_detection_data () =
  try
    let rc = Rc.from_file "prover-detection-data.conf" in
    load rc
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


let run_auto_detection () =
  let l = read_auto_detection_data () in
  let detect = List.fold_left detect_prover Mstr.empty l in
  let length = Mstr.fold (fun _ _ i -> i+1) detect 0 in
  eprintf "%d provers detected.@." length;
  detect
