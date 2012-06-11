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

open Format
open Util
open Rc
open Stdlib

(* magicnumber for the configuration :
  - 0 before the magic number
  - 1 when no loadpath meant default loadpath
  - 2
  - 5 cvc3 native
  - 6 driver renaming
  - 7 yices native (used for release 0.70)
  - 8 for release 0.71
  - 9 coq realizations
  - 10 require %f in editor lines
  - 11 change prover identifiers in provers-detection-data.conf
  - 12 split editors out of provers

If a configuration doesn't contain the actual magic number we don't use it.*)

let magicnumber = 12

exception WrongMagicNumber

(* lib and shared dirs *)

let default_loadpath =
  [ Filename.concat Relocatable.datadir "theories";
    Filename.concat Relocatable.datadir "modules"; ]

let default_conf_file =
  match Config.localdir with
    | None -> Filename.concat (Rc.get_home_dir ()) ".why3.conf"
    | Some d -> Filename.concat d "why3.conf"

(* Prover *)

type prover =
    { prover_name : string;
      prover_version : string;
      prover_altern : string;
    }

let print_prover fmt p =
  Format.fprintf fmt "%s (%s)" p.prover_name p.prover_version
  (* Format.fprintf fmt "%s (%s%s%s)" *)
  (*   p.prover_name p.prover_version *)
  (*   (if p.prover_altern = "" then "" else " ") p.prover_altern *)

module Prover = struct
  type t = prover
  let compare s1 s2 =
    if s1 == s2 then 0 else
    let c = String.compare s1.prover_name s2.prover_name in
    if c <> 0 then c else
    let c = String.compare s1.prover_version s2.prover_version in
    (* if c <> 0 then c else *)
    (* let c = String.compare s1.prover_altern s2.prover_altern in *)
    c

  let equal s1 s2 =
    s1 == s2 ||
      (s1.prover_name = s2.prover_name &&
       s1.prover_version = s2.prover_version(*  && *)
       (* s1.prover_altern = s2.prover_altern *))

  let hash s1 =
      2 * Hashtbl.hash s1.prover_name +
      3 * Hashtbl.hash s1.prover_version (* + *)
      (* 5 * Hashtbl.hash s1.prover_altern *)
end

module Mprover = Map.Make(Prover)
module Sprover = Mprover.Set
module Hprover = Hashtbl.Make(Prover)

module Editor = struct
  type t = string
  let compare = Pervasives.compare
end

module Meditor = Map.Make(Editor)

(* Configuration file *)

type prover_upgrade_policy =
  | CPU_keep
  | CPU_upgrade of prover
  | CPU_duplicate of prover

type config_prover = {
  prover  : prover;
  id      : string;
  command : string;
  driver  : string;
  editor  : string;
  interactive : bool;
  extra_options : string list;
  extra_drivers : string list;
}

type config_editor = {
  editor_name : string;
  editor_command : string;
  editor_options : string list;
}


type main = {
  libdir   : string;      (* "/usr/local/lib/why/" *)
  datadir  : string;      (* "/usr/local/share/why/" *)
  loadpath  : string list;  (* "/usr/local/lib/why/theories" *)
  timelimit : int;
  (* default prover time limit in seconds (0 unlimited) *)
  memlimit  : int;
  (* default prover memory limit in megabytes (0 unlimited)*)
  running_provers_max : int;
  (* max number of running prover processes *)
  plugins : string list;
  (* plugins to load, without extension, relative to [libdir]/plugins *)
}

let libdir m =
  try
    Sys.getenv "WHY3LIB"
  with Not_found -> m.libdir

let datadir m =
  try
    let d = Sys.getenv "WHY3DATA" in
(*
    eprintf "[Info] datadir set using WHY3DATA='%s'@." d;
*)
    d
  with Not_found -> m.datadir

let loadpath m =
  try
    let d = Sys.getenv "WHY3LOADPATH" in
(*
    eprintf "[Info] loadpath set using WHY3LOADPATH='%s'@." d;
*)
    Str.split (Str.regexp ":") d
  with Not_found -> m.loadpath

let timelimit m = m.timelimit
let memlimit m = m.memlimit
let running_provers_max m = m.running_provers_max

let set_limits m time mem running =
  { m with timelimit = time; memlimit = mem; running_provers_max = running }

let plugins m = m.plugins
let set_plugins m pl =
  (* TODO : sanitize? *)
  { m with plugins = pl}

let add_plugin m p =
  if List.mem p m.plugins
  then m
  else { m with plugins = List.rev (p::(List.rev m.plugins))}

let pluginsdir m = Filename.concat m.libdir "plugins"
let load_plugins m =
  let load x =
    try Plugin.load x
    with exn ->
      Format.eprintf "%s can't be loaded : %a@." x
        Exn_printer.exn_printer exn in
  List.iter load m.plugins

type config = {
  conf_file : string;       (* "/home/innocent_user/.why3.conf" *)
  config    : Rc.t;
  main      : main;
  provers   : config_prover Mprover.t;
  editors   : config_editor Meditor.t;
  provers_upgrade_policy : prover_upgrade_policy Mprover.t;
}

let default_main =
  {
    libdir = Relocatable.libdir;
    datadir = Relocatable.datadir;
    loadpath = default_loadpath;
    timelimit = 5;   (* 5 seconds *)
    memlimit = 1000; (* 1 Mb *)
    running_provers_max = 2; (* two provers run in parallel *)
    plugins = [];
  }

let set_main rc main =
  let section = empty_section in
  let section = set_int section "magic" magicnumber in
  let section = set_string ~default:default_main.libdir
    section "libdir" main.libdir in
  let section = set_string ~default:default_main.datadir
    section "datadir" main.datadir in
  let section = set_stringl section "loadpath" main.loadpath in
  let section = set_int section "timelimit" main.timelimit in
  let section = set_int section "memlimit" main.memlimit in
  let section =
    set_int section "running_provers_max" main.running_provers_max in
  let section = set_stringl section "plugin" main.plugins in
  set_section rc "main" section

exception NonUniqueId

let set_prover _ prover (ids,family) =
  if Sstr.mem prover.id ids then raise NonUniqueId;
  let section = empty_section in
  let section = set_string section "name" prover.prover.prover_name in
  let section = set_string section "command" prover.command in
  let section = set_string section "driver" prover.driver in
  let section = set_string section "version" prover.prover.prover_version in
  let section = set_string ~default:"" section "alternative" prover.prover.prover_altern in
  let section = set_string section "editor" prover.editor in
  let section = set_bool section "interactive" prover.interactive in
  (Sstr.add prover.id ids,(prover.id,section)::family)

let set_provers rc provers =
  let _,family = Mprover.fold set_prover provers (Sstr.empty,[]) in
  set_family rc "prover" family

let set_editor id editor (ids, family) =
  if Sstr.mem id ids then raise NonUniqueId;
  let section = empty_section in
  let section = set_string section "name" editor.editor_name in
  let section = set_string section "command" editor.editor_command in
  (Sstr.add id ids, (id, section)::family)

let set_editors rc editors =
  let _,family = Meditor.fold set_editor editors (Sstr.empty,[]) in
  set_family rc "editor" family

let set_prover_upgrade_policy prover policy (i, family) =
  let section = empty_section in
  let section = set_string section "name" prover.prover_name in
  let section = set_string section "version" prover.prover_version in
  let section = set_string section "alternative" prover.prover_altern in
  let section =
    match policy with
      | CPU_keep -> 
        set_string section "policy" "keep"
      | CPU_upgrade p ->
        let section = set_string section "target_name" p.prover_name in
        let section = set_string section "target_version" p.prover_version in
        let section = set_string section "target_alternative" p.prover_altern in
        set_string section "policy" "upgrade"
      | CPU_duplicate p ->
        let section = set_string section "target_name" p.prover_name in
        let section = set_string section "target_version" p.prover_version in
        let section = set_string section "target_alternative" p.prover_altern in
        set_string section "policy" "duplicate"
  in
  (i+1,("policy" ^ string_of_int i, section)::family)

let set_policies rc policy =
  let _,family =
    Mprover.fold set_prover_upgrade_policy policy (0,[])
  in
  set_family rc "uninstalled_prover" family

let absolute_filename = Sysutil.absolutize_filename

let load_prover dirname provers (id,section) =
  let name = get_string section "name" in
  let version = get_string ~default:"" section "version" in
  let altern = get_string ~default:"" section "alternative" in
  let prover =
    { prover_name = name;
      prover_version = version;
      prover_altern = altern;
    }
  in
  Mprover.add prover
    { id = id;
      prover  = prover;
      command = get_string section "command";
      driver  = absolute_filename dirname (get_string section "driver");
      editor  = get_string ~default:"" section "editor";
      interactive = get_bool ~default:false section "interactive";
      extra_options = [];
      extra_drivers = [];
    } provers

let load_editor editors (id, section) =
  Meditor.add id
    { editor_name = get_string ~default:id section "name";
      editor_command = get_string section "command";
      editor_options = [];
    } editors

let load_policy provers acc (_,section) =
  let source =
    {prover_name = get_string section "name";
     prover_version = get_string section "version";
     prover_altern = get_string ~default:"" section "alternative"
    } in
  try
    match get_string section "policy" with
      | "keep" -> Mprover.add source CPU_keep acc
      | "upgrade" ->
        let target =
          { prover_name = get_string section "target_name";
            prover_version = get_string section "target_version";
            prover_altern = get_string ~default:"" section "target_alternative";
          }
        in
        let _target = Mprover.find target provers in
        Mprover.add source (CPU_upgrade target) acc
      | "duplicate" -> 
        let target =
          { prover_name = get_string section "target_name";
            prover_version = get_string section "target_version";
            prover_altern = get_string ~default:"" section "target_alternative";
          }
        in
        let _target = Mprover.find target provers in
        Mprover.add source (CPU_duplicate target) acc
      | _ -> raise Not_found
  with Not_found -> acc

let load_main dirname section =
  if get_int ~default:0 section "magic" <> magicnumber then
    raise WrongMagicNumber;
  { libdir    = get_string ~default:default_main.libdir section "libdir";
    datadir   = get_string ~default:default_main.datadir section "datadir";
    loadpath  = List.map (absolute_filename dirname)
      (get_stringl ~default:[] section "loadpath");
    timelimit = get_int ~default:default_main.timelimit section "timelimit";
    memlimit  = get_int ~default:default_main.memlimit section "memlimit";
    running_provers_max = get_int ~default:default_main.running_provers_max
      section "running_provers_max";
    plugins = get_stringl ~default:[] section "plugin";
  }

let read_config_rc conf_file =
  let filename = match conf_file with
    | Some filename -> filename
    | None -> begin try Sys.getenv "WHY3CONFIG" with Not_found ->
          if Sys.file_exists default_conf_file then default_conf_file
          else raise Exit
        end
  in
  filename, Rc.from_file filename

exception ConfigFailure of string (* filename *) * string

let () = Exn_printer.register (fun fmt e -> match e with
  | ConfigFailure (f, s) ->
      Format.fprintf fmt "error in config file %s: %s" f s
  | WrongMagicNumber ->
      Format.fprintf fmt "outdated config file; rerun why3config"
  | NonUniqueId ->
    Format.fprintf fmt "InternalError : two provers share the same id"
  | _ -> raise e)

let get_config (filename,rc) =
  let dirname = Filename.dirname filename in
  let rc, main =
    match get_section rc "main" with
      | None      -> raise (ConfigFailure (filename, "no main section"))
      | Some main -> rc, load_main dirname main
  in
  let provers = get_family rc "prover" in
  let provers = List.fold_left (load_prover dirname) Mprover.empty provers in
  let editors = get_family rc "editor" in
  let editors = List.fold_left load_editor Meditor.empty editors in
  let policy = get_family rc "uninstalled_prover" in
  let policy = List.fold_left (load_policy provers) Mprover.empty policy in
  { conf_file = filename;
    config    = rc;
    main      = main;
    provers   = provers;
    editors   = editors;
    provers_upgrade_policy = policy;
  }

let default_config conf_file =
  get_config (conf_file, set_main Rc.empty default_main)

let read_config conf_file =
  let filenamerc =
    try
      read_config_rc conf_file
    with Exit ->
      default_conf_file, set_main Rc.empty default_main
  in
  try
    get_config filenamerc
  with e when not (Debug.test_flag Debug.stack_trace) ->
    let b = Buffer.create 40 in
    Format.bprintf b "%a" Exn_printer.exn_printer e;
    raise (ConfigFailure (fst filenamerc, Buffer.contents b))

let merge_config config filename =
  let dirname = Filename.dirname filename in
  let rc = Rc.from_file filename in
  let main = match get_section rc "main" with
    | None -> config.main
    | Some rc ->
      let loadpath = (List.map (absolute_filename dirname)
        (get_stringl ~default:[] rc "loadpath")) @ config.main.loadpath in
      let plugins = (get_stringl ~default:[] rc "plugin") @ config.main.plugins in
      { config.main with loadpath = loadpath; plugins = plugins } in
  let provers = get_family rc "prover" in
  let provers = List.fold_left
    (fun provers (id, section) ->
      try
        let key,c = Mprover.choose (Mprover.filter (fun _ p -> p.id = id) provers) in
        let opt = (get_stringl ~default:[] section "option") @ c.extra_options in
        let drv = (List.map (absolute_filename dirname)
          (get_stringl ~default:[] section "driver")) @ c.extra_options in
        Mprover.add key { c with extra_options = opt ; extra_drivers = drv } provers
      with
        Not_found -> load_prover dirname provers (id, section)
    ) config.provers provers in
  let editors = get_family rc "editor" in
  let editors = List.fold_left
    (fun editors (id, section) ->
      try
        let c = Meditor.find id editors in
        let opt = (get_stringl ~default:[] section "option") @ c.editor_options in
        Meditor.add id { c with editor_options = opt } editors
      with
        Not_found -> load_editor editors (id, section)
    ) config.editors editors in
  { config with main = main; provers = provers; editors = editors }

let save_config config =
  let filename = config.conf_file in
  Sysutil.backup_file filename;
  to_file filename config.config

let get_main config = config.main
let get_provers config = config.provers
let get_policies config = config.provers_upgrade_policy
let get_prover_upgrade_policy config p =
  Mprover.find p config.provers_upgrade_policy

let set_main config main =
  {config with
    config = set_main config.config main;
    main = main;
  }

let set_provers config provers =
  {config with
    config = set_provers config.config provers;
    provers = provers;
  }

let set_editors config editors =
  { config with
    config = set_editors config.config editors;
    editors = editors;
  }

let set_prover_upgrade_policy config prover target =
  let m = Mprover.add prover target config.provers_upgrade_policy in
  {config with
    config = set_policies config.config m;
    provers_upgrade_policy = m;
  }

let set_policies config policies = 
  { config with
    config = set_policies config.config policies;
    provers_upgrade_policy = policies }



(*******)

let set_conf_file config conf_file = {config with conf_file = conf_file}
let get_conf_file config           =  config.conf_file

(*******)

let is_prover_known whyconf prover =
  Mprover.mem prover (get_provers whyconf)

exception ProverNotFound of config * string

let prover_by_id whyconf id =
  let potentials =
    Mprover.filter (fun _ p -> p.id = id) whyconf.provers in
  match Mprover.keys potentials with
    | [] -> raise (ProverNotFound(whyconf,id))
    | [_] -> snd (Mprover.choose potentials)
    |  _  -> assert false (** by the verification done by set_provers *)

let () = Exn_printer.register
  (fun fmt exn ->
    match exn with
      | ProverNotFound (config,s) ->
        fprintf fmt "Prover '%s' not found in %s@."
          s (get_conf_file config)
      | e -> raise e
  )

let get_editors c = c.editors

let editor_by_id whyconf id =
  Meditor.find id whyconf.editors

(******)

let get_section config name = assert (name <> "main");
  get_section config.config name

let get_family config name = assert (name <> "prover");
  get_family config.config name


let set_section config name section = assert (name <> "main");
  {config with config = set_section config.config name section}

let set_family config name section = assert (name <> "prover");
  {config with config = set_family config.config name section}

