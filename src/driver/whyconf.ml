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

(* are we executed with an implicit path or not ? 
   
   cmd   -> yes (dirname = ".", is_implicit = yes)
   /...  -> no   (dirname = "/...", is_implicit = no)
   ./t   -> no   (dirname = ".", is_implicit = no)
   bin/t -> no   (dirname = "bin", is_implicit = yes)

*)
let implicit_path =
  let s = Sys.argv.(0) in
  Filename.is_implicit s && 
    Filename.dirname s = Filename.current_dir_name

let libdir =  
  if implicit_path then
    try
      Sys.getenv "WHY3LIB"
    with Not_found -> Config.libdir
  else "."

let datadir =
  if implicit_path then
    try
      Sys.getenv "WHY3DATA"
    with Not_found -> Config.datadir
  else "share"




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
}

type config = {
  conf_file : string;       (* "/home/innocent_user/.why.conf" *)
(*
  loadpath  : string list;  (* "/usr/local/share/why/theories" *)
*)
  timelimit : int option;   (* default prover time limit in seconds *)
  memlimit  : int option;   (* default prover memory limit in megabytes *)
  running_provers_max : int option; (* max number of running prover processes *)
  provers   : config_prover Mstr.t; (* indexed by short identifiers *)
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
  let load (key, value) = match key with
    | "name"        -> set_string key nam value
    | "command"     -> set_string key cmd value
    | "driver"      -> set_string key drv value; 
	               drv := option_map (absolute_filename dirname) !drv
    | _             -> ()
        (*
          error (UnknownField key)
        *)
  in
  List.iter load al;
  { name    = get_field "name" !nam;
    command = get_field "command" !cmd;
    driver  = get_field "driver" !drv }

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
    | _           -> ()
        (*
          error (UnknownField key)
        *)
  in
  List.iter load al;
  { main with
(*
    loadpath  = List.rev !lp;
*)
    timelimit = !tl;
    memlimit  = !ml;
    running_provers_max = !rp;
    provers   = Mstr.empty }

let read_config conf_file =
  let filename = match conf_file with
    | Some filename -> filename
    | None -> begin try Sys.getenv "WHY_CONFIG" with Not_found ->
          if Sys.file_exists "why.conf" then "why.conf" else
          if Sys.file_exists ".why.conf" then ".why.conf" else
          let f = Filename.concat (Rc.get_home_dir ()) ".why.conf" in
	  if Sys.file_exists f then f else
	  Filename.concat Config.libdir "why.conf"
        end
  in
  let dirname = Filename.dirname filename in
  let rc = try Rc.from_file filename with
    | Failure "lexing" -> error SyntaxError
  in
  let main = ref {
    conf_file = filename;
(*
    loadpath  = [];
*)
    timelimit = None;
    memlimit  = None;
    running_provers_max = None;
    provers   = Mstr.empty }
  in
  let provers = ref Mstr.empty in
  let have_main = ref false in
  let load (key, al) = match key with
    | "main" :: rest ->
        if rest <> [] then error (ExtraParameters "main");
        if !have_main then error (DuplicateSection "main");
        main := load_main dirname !main al
    | "prover" :: name :: rest ->
        if rest <> [] then error (ExtraParameters ("prover " ^ name));
        if Mstr.mem name !provers then error (DuplicateProver name);
        provers := Mstr.add name (load_prover dirname al) !provers
    | "prover" :: [] -> error (MissingParameters "prover")
    | s :: _ -> error (UnknownSection s)
    | [] -> assert false
  in
  List.iter load rc;
  { !main with provers = !provers }

let save_config config =
  let ch = open_out config.conf_file in
  let fmt = Format.formatter_of_out_channel ch in
  fprintf fmt "[main]@\n";
(*
  List.iter (fprintf fmt "library = \"%s\"@\n") config.loadpath;
*)
  Util.option_iter (fprintf fmt "timelimit = %d@\n") config.timelimit;
  Util.option_iter (fprintf fmt "memlimit = %d@\n") config.memlimit;
  Util.option_iter (fprintf fmt "running_provers_max = %d@\n") config.running_provers_max;
  fprintf fmt "@.";
  let print_prover name prover =
    fprintf fmt "[prover %s]@\n" name;
    fprintf fmt "name = \"%s\"@\n" prover.name;
    fprintf fmt "command = \"%s\"@\n" prover.command;
    fprintf fmt "driver = \"%s\"@\n@." prover.driver;
  in
  Mstr.iter print_prover config.provers;
  close_out ch

