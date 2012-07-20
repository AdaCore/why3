(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
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

(*****
1) For every block, for every executable call the prover using the
version switch and add the prover to the configuration if the version
match one of the version_ok or version_old but none of the version_bad
2) We consider that an executable name which appears in a block, but
which version isn't a version_ok, version_old or version_bad has an
unknown version
3) For every executable which have an unknown version, we add the
prover using the first block that contains it.

Don't use the family argument except when you add manualy one prover.

So the order of the block is used only when the version of an
executable appears in none of the block.

A block with more than one exec fields is now the same thing than if you
split the block into blocks containing one fields.

New message field that allows to print a message when a prover is
detected. If a message is not present, we print ", Ok." if the version
is good (version_good) and not old, and " (it is an old version)." if
the version is old (version_old).

The field command can be missing in a block, in that case the block
defines a version known to be buggy: no prover config is generated.

*)

open Format
open Util
open Ident
open Whyconf
module Wc = Whyconf
open Rc

let debug = Debug.register_flag "autodetect"

(* auto-detection of provers *)

type prover_kind = ATP | ITP
type prover_autodetection_data =
    { kind : prover_kind;
      prover_id : string;
      prover_name : string;
      prover_altern : string;
      execs : string list;
      version_switch : string;
      version_regexp : string;
      versions_ok : string list;
      versions_old : string list;
      versions_bad : string list;
      (** If none it's a fake prover (very bad version) *)
      prover_command : string option;
      prover_driver : string;
      prover_editor : string;
      prover_in_place : bool;
      message : string option;
    }

let prover_keys =
  let add acc k = Sstr.add k acc in
  List.fold_left add Sstr.empty
    ["name";"exec";"version_switch";"version_regexp";
     "version_ok";"version_old";"version_bad";"command";
     "editor";"driver";"in_place";"message"]

let load_prover kind (id,section) =
  check_exhaustive section prover_keys;
  { kind = kind;
    prover_id = id;
    prover_name = get_string section "name";
    prover_altern = get_string section ~default:"" "altern";
    execs = get_stringl section "exec";
    version_switch = get_string section ~default:"" "version_switch";
    version_regexp = get_string section ~default:"" "version_regexp";
    versions_ok = get_stringl section ~default:[] "version_ok";
    versions_old = get_stringl section ~default:[] "version_old";
    versions_bad = get_stringl section ~default:[] "version_bad";
    prover_command = get_stringo section "command";
    prover_driver = get_string section "driver";
    prover_editor = get_string section ~default:"" "editor";
    prover_in_place = get_bool section ~default:false "in_place";
    message = get_stringo section "message";
  }

let editor_keys =
  let add acc k = Sstr.add k acc in
  List.fold_left add Sstr.empty
    ["command"]

let load_editor section =
  check_exhaustive section prover_keys;
  { editor_name = get_string section "name";
    editor_command = get_string section "command";
    editor_options = []
  }

(** returned in reverse order *)
let load rc =
  let atps = get_family rc "ATP" in
  let atps = List.rev_map (load_prover ATP) atps in
  let itps = get_family rc "ITP" in
  let tps = List.fold_left (cons (load_prover ITP)) atps itps in
  tps

let read_auto_detection_data main =
  let filename = Filename.concat (Whyconf.datadir main)
    "provers-detection-data.conf" in
  try
    let rc = Rc.from_file filename in
    List.rev (load rc)
  with
    | Failure "lexing" ->
        Loc.errorm "Syntax error in provers-detection-data.conf@."
    | Not_found ->
        Loc.errorm "provers-detection-data.conf not found at %s@." filename

let provers_found = ref 0

let read_editors main =
  let filename = Filename.concat (Whyconf.datadir main)
    "provers-detection-data.conf" in
  try
    let rc = Rc.from_file filename in
    List.fold_left (fun editors (id, section) ->
      Meditor.add id (load_editor section) editors
    ) Meditor.empty (get_family rc "editor")
  with
    | Failure "lexing" ->
        Loc.errorm "Syntax error in provers-detection-data.conf@."
    | Not_found ->
        Loc.errorm "provers-detection-data.conf not found at %s@." filename

let make_command exec com =
  let cmd_regexp = Str.regexp "%\\(.\\)" in
  let replace s = match Str.matched_group 1 s with
    | "e" -> exec
    | c -> "%"^c
  in
  Str.global_substitute cmd_regexp replace com

let sanitize_exec =
  let first c = match c with
    | '_' | ' ' -> "_"
    | _ -> char_to_alpha c
  in
  let rest c = match c with
    | '+' | '-' | '.' -> String.make 1 c
    | _ -> char_to_alnumus c
  in
  sanitizer first rest

type env =
  {
    (** memoization of (exec_name,version_switch)
        -> Some output | None doesn't exists *)
    prover_output : ((string * string),string option) Hashtbl.t;
    (** existing executable table:
        exec_name -> | Some prover_config unknown version (neither good or bad)
                     | None               there is a good version *)
    prover_unknown_version : (string, config_prover option) Hashtbl.t;
  }

let create_env () =
{ prover_output = Hashtbl.create 10;
  prover_unknown_version = Hashtbl.create 10 }

let ask_prover_version exec_name version_switch =
  let out = Filename.temp_file "out" "" in
  let cmd = sprintf "%s %s" exec_name version_switch in
  let c = sprintf "(%s) > %s 2>&1" cmd out in
  Debug.dprintf debug "Run : %s@." c;
  let ret = Sys.command c in
  if ret <> 0 then
    begin
      Debug.dprintf debug "command '%s' failed@." cmd;
      None
    end
  else
    try
      let ch = open_in out in
      let c = Sysutil.channel_contents ch in
      close_in ch;
      Sys.remove out;
      Some c
    with Not_found | End_of_file  -> Some ""

let ask_prover_version env exec_name version_switch =
  try
    Hashtbl.find env.prover_output (exec_name,version_switch)
  with Not_found ->
    let res = ask_prover_version exec_name version_switch in
    Hashtbl.replace env.prover_output (exec_name,version_switch) res;
    res

let check_version (version : string) schema = schema = version

let known_version env exec_name =
  Hashtbl.replace env.prover_unknown_version exec_name None

let unknown_version env exec_name prover_config =
  if not (Hashtbl.mem env.prover_unknown_version exec_name)
  then Hashtbl.replace env.prover_unknown_version exec_name (Some prover_config)


let empty_alt s = if s = "" then "alt" else s

let find_prover_altern provers prover_id =
  if not (Mprover.mem prover_id provers) then prover_id
  else
    let prover_id =
      {prover_id with
        Wc.prover_altern = empty_alt prover_id.Wc.prover_altern} in
    if not (Mprover.mem prover_id provers) then prover_id
    else
    let rec aux n =
      let prover_id_n = {prover_id with
        Wc.prover_altern = sprintf "%s_%i"
          (empty_alt prover_id.Wc.prover_altern) n} in
      if Mprover.mem prover_id_n provers
      then aux (n+1)
      else prover_id_n in
    (** start with 2 in order to have toto_alt, toto_alt2,
        toto_alt3,... and not toto_alt, toto_alt1 which can be
        confusing *)
    aux 2

let add_prover_with_uniq_id prover provers =
  (** find an unique prover triplet *)
  let prover_id = find_prover_altern provers prover.Wc.prover in
  let prover = {prover with Wc.prover = prover_id} in
  (** find an unique id *)
  let test id _ p = p.Wc.id = id in
  if not (Mprover.exists (test prover.Wc.id) provers)
  then Mprover.add prover.Wc.prover prover provers
  else
    let rec aux i =
      let prover_id = sprintf "%s_%i" prover.Wc.id i in
      if not (Mprover.exists (test prover_id) provers)
      then Mprover.add prover.Wc.prover
        {prover with id = prover_id}  provers
      else aux (i+1) in
    aux 2


let detect_exec env main data acc exec_name =
  let s = ask_prover_version env exec_name data.version_switch in
  match s with
  | None -> acc
  | Some s ->
  let re = Str.regexp data.version_regexp in
  let ver =
    try
      ignore (Str.search_forward re s 0);
      Str.matched_group 1 s
    with Not_found ->
      begin
        Debug.dprintf debug "Warning: found prover %s but name/version not \
                       recognized by regexp `%s'@."
          data.prover_name data.version_regexp;
        Debug.dprintf debug "Answer was `%s'@." s;
        ""
      end
  in
  (** bad mean here not good, it's not the same thing than a version
      of a prover with known problems *)
  let bad = List.exists (check_version ver) data.versions_bad in
  if bad then (known_version env exec_name; acc)
  else

    let good = List.exists (check_version ver) data.versions_ok in
    let old  = List.exists (check_version ver) data.versions_old in
    match data.prover_command with
    | None ->
      (** Empty prover *)
      if good || old then begin (** Known version with error *)
        known_version env exec_name;
        eprintf "Found prover %s version %s%s@."
          data.prover_name ver
          (def_option
             ". This version of the prover is known to have problems."
             data.message);
        acc
      end
      else (** it's not a known bad version *) acc

    | Some prover_command ->
    (** create the prover config *)
    let c = make_command exec_name prover_command in
    let prover = {Wc.prover_name = data.prover_name;
                  prover_version      = ver;
                  prover_altern       = data.prover_altern} in
    let prover_config =
      {prover  = prover;
       id      = data.prover_id;
       command = c;
       driver  = Filename.concat (datadir main) data.prover_driver;
       editor  = data.prover_editor;
       in_place      = data.prover_in_place;
       interactive   = (match data.kind with ITP -> true | ATP -> false);
       extra_options = [];
       extra_drivers = [] } in

    if good || old then begin
      eprintf "Found prover %s version %s%s@."
        data.prover_name ver
        (def_option (if old then " (it is an old version)." else ", Ok.")
           data.message);
      known_version env exec_name;
      add_prover_with_uniq_id prover_config acc
    end
    else (unknown_version env exec_name prover_config; acc)

let detect_prover env main acc data =
  List.fold_left (detect_exec env main data) acc data.execs

(** add the prover unknown *)
let detect_unknown env detected =
  Hashtbl.fold (fun _ pc acc ->
    match pc with
    | None -> acc
    | Some prover_config ->
      let prover = prover_config.prover in
      eprintf "Warning: prover %s version %s is not known to be \
                     supported, use it at your own risk!@."
        prover.Wc.prover_name prover.prover_version;
      add_prover_with_uniq_id prover_config acc)
    env.prover_unknown_version detected

let run_auto_detection config =
  let main = get_main config in
  let l = read_auto_detection_data main in
  let env = create_env () in
  let detect = List.fold_left (detect_prover env main) Mprover.empty l in
  let length_detected = Mprover.cardinal detect in
  let detect = detect_unknown env detect in
  let length_unsupported_version = Mprover.cardinal detect - length_detected in
  eprintf
    "%d provers detected and %d provers detected with unsupported version@."
    length_detected length_unsupported_version;
  set_provers (set_editors config (read_editors main)) detect

let list_prover_ids () =
  let config = default_config "/dev/null" in
  let main = get_main config in
  let l = read_auto_detection_data main in
  let s = List.fold_left (fun s p -> Sstr.add p.prover_id s) Sstr.empty l in
  Sstr.elements s

let get_suffix id alt =
  let ilen = String.length id in
  let alen = String.length alt in
  let rec aux i =
    if i = alen then "alt" else
    if i = ilen then String.sub alt i (alen-i) else
    if id.[i] = alt.[i] then aux (i+1) else
    String.sub alt i (alen-i)
  in
  aux 0


let get_altern id path =
  let alt = Filename.basename path in
  get_suffix id alt

let add_prover_binary config id path =
  let main = get_main config in
  let l = read_auto_detection_data main in
  let l = List.filter (fun p -> p.prover_id = id) l in
  if l = [] then Loc.errorm "Unknown prover id: %s" id;
  let env = create_env () in
  let detected = List.fold_left
    (fun acc data -> detect_exec env main data acc path) Mprover.empty l in
  let detected = detect_unknown env detected in
  if Mprover.is_empty detected then
    Loc.errorm "File %s does not correspond to the prover id %s" path id;
  let provers = get_provers config in
  let fold _ p provers =
    (** find a prover altern not used *)
    (* Is a prover with this name and version already in config? *)
    let prover_id =
      if not (Mprover.mem p.prover provers) then p.prover else
        let alt = get_altern id path in
        let prover_id = { p.prover with
          Wc.prover_altern =
            Util.concat_non_empty " " [p.prover.Wc.prover_altern;alt] } in
        find_prover_altern provers prover_id in
    let p_new = {p with prover = prover_id} in
    let alt = sanitizer char_to_alnumus char_to_alnumus
      (get_suffix p.prover.Wc.prover_altern
         prover_id.Wc.prover_altern) in
    let p_new = { p_new with id = p.id ^ "-" ^ alt } in
    add_prover_with_uniq_id p_new provers in
  let provers = Mprover.fold fold detected provers in
  set_provers config provers
