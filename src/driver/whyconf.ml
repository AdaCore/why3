(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Wstdlib
open Rc

let debug = Debug.register_info_flag "whyconf"
  ~desc:"Print@ debugging@ messages@ about@ whyconf."


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
  - 13 add shortcuts
  - 14 use simple_family for prover and shortcut section

If a configuration doesn't contain the actual magic number we don't use it.*)

let magicnumber = 14

exception WrongMagicNumber

let why3_regexp_of_string s = (* define a regexp in why3 *)
  if s = "" then Re.Str.regexp "^$" else
  if s.[0] = '^' then Re.Str.regexp s else
  Re.Str.regexp ("^" ^ Re.Str.quote s ^ "$")

(* lib and shared dirs *)

let default_conf_file =
  match Config.localdir with
  | None -> Filename.concat (Util.get_home_dir ()) ".why3.conf"
  | Some d -> Filename.concat d "why3.conf"

(* Prover *)

(* BEGIN{provertype} anchor for automatic documentation, do not remove *)
type prover =
    { prover_name : string;
      prover_version : string;
      prover_altern : string;
    }
(* END{provertype} anchor for automatic documentation, do not remove *)

let print_altern fmt s =
  if s <> "" then Format.fprintf fmt " (%s)" s

let print_prover fmt p =
  Format.fprintf fmt "%s %s%a"
    p.prover_name p.prover_version print_altern p.prover_altern

let prover_parseable_format p =
  if p.prover_altern = "" then
    Format.sprintf "%s,%s"
                   p.prover_name p.prover_version
  else
    Format.sprintf "%s,%s,%s"
                   p.prover_name p.prover_version p.prover_altern

let print_prover_parseable_format fmt p =
  Format.pp_print_string fmt (prover_parseable_format p)

module Prover = struct
  type t = prover
  let compare s1 s2 =
    if s1 == s2 then 0 else
    let c = String.compare s1.prover_name s2.prover_name in
    if c <> 0 then c else
    let c = String.compare s1.prover_version s2.prover_version in
    if c <> 0 then c else
    let c = String.compare s1.prover_altern s2.prover_altern in
    c

  let equal s1 s2 =
    s1 == s2 ||
      (s1.prover_name = s2.prover_name &&
       s1.prover_version = s2.prover_version &&
       s1.prover_altern = s2.prover_altern )

  let hash s1 =
      2 * Hashtbl.hash s1.prover_name +
      3 * Hashtbl.hash s1.prover_version +
      5 * Hashtbl.hash s1.prover_altern
end

module Mprover = Extmap.Make(Prover)
module Sprover = Extset.MakeOfMap(Mprover)
module Hprover = Exthtbl.Make(Prover)

module Editor = struct
  type t = string
  let compare = String.compare
end

module Meditor = Extmap.Make(Editor)

(* Configuration file *)

type prover_upgrade_policy =
  | CPU_keep
  | CPU_upgrade of prover
  | CPU_duplicate of prover
  | CPU_remove

let print_prover_upgrade_policy fmt p =
  match p with
  | CPU_keep -> Format.pp_print_string fmt "keep"
  | CPU_upgrade p -> Format.fprintf fmt "upgrade to %a" print_prover p
  | CPU_duplicate p -> Format.fprintf fmt "copy to %a" print_prover p
  | CPU_remove -> Format.pp_print_string fmt "remove"



type config_prover = {
  prover  : prover;
  command : string;
  command_steps : string option;
  driver  : string option * string;
  in_place: bool;
  editor  : string;
  interactive : bool;
  extra_options : string list;
  extra_drivers : (string * string list) list;
}

type config_editor = {
  editor_name : string;
  editor_command : string;
  editor_options : string list;
}

(** Strategies *)

type config_strategy = {
  strategy_name : string;
  strategy_desc : string;
  strategy_code : string;
  strategy_shortcut : string;
}

let get_strategies rc =
  get_simple_family rc "strategy"

let set_strategy _ s family =
  let section = empty_section in
  let section = set_string section "name" s.strategy_name in
  let section = set_string section "desc" s.strategy_desc in
  let section = set_string section "shortcut" s.strategy_shortcut in
  let section = set_string section "code" s.strategy_code in
  section::family

let set_strategies rc strategies =
  let family = Mstr.fold set_strategy strategies [] in
  set_simple_family rc "strategy" family

(** Main record *)

type main = {
  libdir   : string;
  (* arch-dependent data, say "/usr/local/lib/why3/" *)
  datadir  : string;
  (* arch-independent data, say "/usr/local/share/why3/" *)
  loadpath  : string list;
  (* standard library, say "/usr/local/lib/why3/stdlib" *)
  stdlib  : bool;
  (* add the standard library in the loadpath (default true) *)
  load_default_plugins  : bool;
  (* autoload the plugins in libdir (default true) *)
  timelimit : float;
  (* default prover time limit in seconds (0 means unlimited) *)
  memlimit  : int;
  (* default prover memory limit in megabytes (0 means unlimited)*)
  running_provers_max : int;
  (* max number of running prover processes *)
  plugins : string list;
  (* plugins to load, without extension, relative to [libdir]/plugins *)
  default_editor : string;
  (* editor name used when no specific editor known for a prover *)
}

let libdir =
  let env_libdir = try Some (Sys.getenv "WHY3LIB") with Not_found -> None in
  fun m -> Option.value ~default:m.libdir env_libdir

let set_libdir m d = { m with libdir = d}

let datadir =
  let env_datadir = try Some (Sys.getenv "WHY3DATA") with Not_found -> None in
  fun m -> Option.value ~default:m.datadir env_datadir

let set_datadir m d = { m with datadir = d}

let stdlib_path = ref ""

let default_loadpath m =
  [ Filename.concat (datadir m) "stdlib" ]

let loadpath =
  let env_loadpath =
    try Some (Strings.split ':' (Sys.getenv "WHY3LOADPATH"))
    with Not_found -> None
  in
  fun m ->
    match env_loadpath with
    | Some l -> stdlib_path := List.hd l; l
    | None ->
      let stdlib =
        if m.stdlib then
          let loadpath = default_loadpath m in
          let () = stdlib_path := List.hd loadpath in
          loadpath
        else [] in
      m.loadpath@stdlib

let set_loadpath m l = { m with loadpath = l}

let timelimit m = m.timelimit
let memlimit m = m.memlimit
let running_provers_max m = m.running_provers_max
let default_editor m = m.default_editor

exception StepsCommandNotSpecified of string

let get_complete_command pc ~with_steps =
  let comm = if not with_steps then pc.command
    else
      match pc.command_steps with
      | None -> raise (StepsCommandNotSpecified
          "The solver is used with a step limit and the command for \
            running the solver with a step limit is not specified.")
      | Some command_steps -> command_steps in
  String.concat " " (comm :: pc.extra_options)

let set_limits m time mem running =
  { m with timelimit = time; memlimit = mem; running_provers_max = running }

let set_default_editor m e = { m with default_editor = e }

let plugins m = m.plugins
let set_plugins m pl =
  (* TODO : sanitize? *)
  { m with plugins = pl}

let add_plugin m p =
  if List.mem p m.plugins
  then m
  else { m with plugins = List.rev (p::(List.rev m.plugins))}

let pluginsdir m = Filename.concat (libdir m) "plugins"

let plugins_auto_detection main =
  let dir = pluginsdir main in
  let ext = if Dynlink.is_native then ".cmxs" else ".cma" in
  let files = try Sys.readdir dir with Sys_error _ -> [||] in
  let fold acc p =
    let open Filename in
    if extension p = ext then
      concat dir (chop_extension p) :: acc
    else
      acc in
  Array.fold_left fold [] files

let load_plugins main =
  let load x =
    try Plugin.load x
    with exn ->
      Format.eprintf "%s cannot be loaded: %a@." x
        Exn_printer.exn_printer exn in
  if main.load_default_plugins then List.iter load (plugins_auto_detection main);
  List.iter load main.plugins

type config = {
  conf_file : string;       (* "/home/innocent_user/.why3.conf" *)
  user_rc : Rc.t; (* from .why3.conf without extra_config *)
  main      : main;
  provers   : config_prover Mprover.t;
  prover_shortcuts : prover Mstr.t;
  prover_editors : string Mprover.t;
  editors   : config_editor Meditor.t;
  provers_upgrade_policy : prover_upgrade_policy Mprover.t;
  strategies : config_strategy Mstr.t;
}

let empty_main =
  {
    libdir = Config.libdir;
    datadir = Config.datadir;
    loadpath = [];
    stdlib = true;
    load_default_plugins = true;
    timelimit = 5.;   (* 5 seconds *)
    memlimit = 1000; (* 1 Mb *)
    running_provers_max = 2; (* two provers run in parallel *)
    plugins = [];
    default_editor = Config.editor ^ " %f"
  }

exception ConfigFailure of string (* filename *) * string
exception DuplicateShortcut of string

module RC_load = struct

  let add_prover_shortcuts acc prover shortcuts =
    List.fold_left (fun acc shortcut ->
        if shortcut.[0] = '^' then
          invalid_arg "prover shortcut can't start with a ^";
        Mstr.add_new (DuplicateShortcut shortcut) shortcut prover acc
      ) acc shortcuts


  let load_prover_id section =
    let name = get_string section "name" in
    let version = get_string ~default:"" section "version" in
    let altern = get_string ~default:"" section "alternative" in
    let prover =
      { prover_name = name;
        prover_version = version;
        prover_altern = altern;
      }
    in
    prover

  let load_prover ~config_dir (provers,shortcuts) section =
    try
      let prover = load_prover_id section in
      let info =
        match Mprover.find_opt prover provers with
        | None ->
            let driver = get_string section "driver" in
            Debug.dprintf debug "Loading a new prover with config_dir = %a, driver = %s@."
              (Pp.print_option Pp.print_string) config_dir driver;
            { prover  = prover;
            command = get_string section "command";
	    command_steps = get_stringo section "command_steps";
            driver  = (config_dir,driver);
            in_place = get_bool ~default:false section "in_place";
            editor  = get_string ~default:"" section "editor";
            interactive = get_bool ~default:false section "interactive";
            extra_options = [];
            extra_drivers = [];
          }
        | Some info ->
            let driver =
              match get_stringo section "driver" with
                | None -> info.driver
                | Some d -> (config_dir,d)
            in
            Debug.dprintf debug "Loading a prover extension with config_dir = %a, driver = %s@."
              (Pp.print_option Pp.print_string) (fst driver) (snd driver);
          { prover  = prover;
            command = get_string ~default:info.command section "command";
            command_steps =
              begin match get_stringo section "command_steps" with
              | None -> info.command_steps
              | c -> c end;
            driver  = driver;
            in_place = get_bool ~default:info.in_place section "in_place";
            editor  = get_string ~default:info.editor section "editor";
            interactive = get_bool ~default:info.interactive section "interactive";
            extra_options = info.extra_options;
            extra_drivers = info.extra_drivers;
          }
      in
      let provers = Mprover.add prover info provers in
      let lshort = get_stringl section "shortcut" in
      let shortcuts = add_prover_shortcuts shortcuts prover lshort in
      provers,shortcuts
    with MissingField s ->
      Loc.warning warn_missing_field "Missing field '%s' in [prover] section@." s;
      provers,shortcuts

  let load_shortcut acc section =
    try
      let prover = load_prover_id section in
      let shortcuts = get_stringl section "shortcut" in
      add_prover_shortcuts acc prover shortcuts
    with MissingField s ->
      Loc.warning warn_missing_field "Missing field '%s' in [shortcut] section@." s;
      acc

  let load_prover_editor acc section =
    try
      let prover = load_prover_id section in
      let editor = get_string section "editor" in
      Mprover.add prover editor acc
    with MissingField s ->
      Loc.warning warn_missing_field "Missing field '%s' in [prover_editor] section@." s;
      acc

  let load_editor editors (id, section) =
    try
      let info = match Meditor.find_opt id editors with
      | None ->
          { editor_name = get_string ~default:id section "name";
            editor_command = get_string section "command";
            editor_options = [];
          }
      | Some info ->
          { editor_name = get_string ~default:info.editor_name section "name";
            editor_command = get_string ~default:info.editor_command section "command";
            editor_options = (get_stringl section "options")@info.editor_options;
          }
      in
      Meditor.add id info editors
    with MissingField s ->
      Loc.warning warn_missing_field "Missing field '%s' in [editor] section@." s;
      editors

  let load_policy acc (_,section) =
    try
      let source = load_prover_id section in
      try
        match get_string section "policy" with
        | "keep" -> Mprover.add source CPU_keep acc
        | "remove" -> Mprover.add source CPU_remove acc
        | "upgrade" ->
            let target =
              { prover_name = get_string section "target_name";
                prover_version = get_string section "target_version";
                prover_altern = get_string ~default:"" section "target_alternative";
              }
            in
            Mprover.add source (CPU_upgrade target) acc
        | "duplicate" ->
            let target =
              { prover_name = get_string section "target_name";
                prover_version = get_string section "target_version";
                prover_altern = get_string ~default:"" section "target_alternative";
              }
            in
            Mprover.add source (CPU_duplicate target) acc
        | _ -> raise Not_found
      with Not_found -> acc
    with MissingField s ->
      Loc.warning warn_missing_field "Missing field '%s' in [uninstalled_prover] section@." s;
      acc

  let warn_replaced_space =
    Loc.register_warning "replaced_space" "Warn that a space has been replaced by '_' in a strategy name"

  let load_strategy strategies section =
    try
      let name = get_string section "name" in
      let name =
        try
          let (_:int) = String.index name ' ' in
          Loc.warning warn_replaced_space "Found a space character in strategy name '%s', replaced by '_'@." name;
          String.map (function ' ' -> '_' | c -> c) name
        with Not_found -> name
      in
      let desc = get_string section "desc" in
      let shortcut = get_string ~default:"" section "shortcut" in
      let code = get_string section "code" in
      Mstr.add
        name
        { strategy_name = name;
          strategy_desc = desc;
          strategy_code = code;
          strategy_shortcut = shortcut;
        }
        strategies
    with
      MissingField s ->
        Loc.warning warn_missing_field "Missing field '%s' in [strategy] section@." s;
        strategies

  let load_main old dirname section =
    if get_int ~default:0 section "magic" <> magicnumber then
      raise WrongMagicNumber;
    { libdir    = get_string ~default:old.libdir section "libdir";
      datadir   = get_string ~default:old.datadir section "datadir";
      loadpath  =
        begin match get_stringl section "loadpath" with
        | [] -> old.loadpath
        | l -> List.map (Sysutil.concat dirname) l end;
      stdlib = get_bool ~default:old.stdlib section "stdlib";
      load_default_plugins = get_bool ~default:old.load_default_plugins section "load_default_plugins";
      timelimit = get_float ~default:old.timelimit section "timelimit";
      memlimit  = get_int ~default:old.memlimit section "memlimit";
      running_provers_max = get_int ~default:old.running_provers_max
          section "running_provers_max";
      plugins =
        begin match get_stringl section "plugin" with
        | [] -> old.plugins
        | l -> l end;
      default_editor = get_string ~default:old.default_editor section "default_editor";
    }

  let get_dirname filename =
    Filename.dirname (Sysutil.concat (Sys.getcwd ()) filename)

  let config_from_rc config filename rc =
    Debug.dprintf debug "[Whyconf.config_from_rc] filename=%s@." filename;
    let dirname = get_dirname filename in
    let main =
      match get_section rc "main" with
      | None      -> config.main
      | Some main -> load_main config.main dirname main
    in
    let provers = get_simple_family rc "prover" in
    let provers,shortcuts = List.fold_left (load_prover ~config_dir:None)
        (config.provers,config.prover_shortcuts) provers in
    let fam_shortcuts = get_simple_family rc "shortcut" in
    let shortcuts = List.fold_left load_shortcut shortcuts fam_shortcuts in
    let fam_editors = get_simple_family rc "prover_editor" in
    let prover_editors = List.fold_left load_prover_editor config.prover_editors fam_editors in
    let editors = get_family rc "editor" in
    let editors = List.fold_left load_editor config.editors editors in
    let policy = get_family rc "uninstalled_prover" in
    let policy = List.fold_left load_policy config.provers_upgrade_policy policy in
    let strategies = get_strategies rc in
    let strategies = List.fold_left load_strategy config.strategies strategies in
    { conf_file = filename;
      user_rc    = rc;
      main      = main;
      provers   = provers;
      prover_shortcuts = shortcuts;
      prover_editors = prover_editors;
      editors   = editors;
      provers_upgrade_policy = policy;
      strategies = strategies;
    }

end

module RC_save = struct
  let set_limits ~time ~mem ~j section =
    let section =
      match get_into section "magic" with
      | None -> set_int section "magic" magicnumber
      | _ -> section
    in
    let section = set_float section "timelimit" time in
    let section = set_int section "memlimit" mem in
    let section =
      set_int section "running_provers_max" j in
    section

  let set_default_editor default section =
    set_string section "default_editor" default

  let set_main rc main =
    let section = empty_section in
    let section = set_int section "magic" magicnumber in
    (* FIXME is this needed or not?
       what would be the effect of uncommmenting that code?
       would it make the libdir and datadir saved in the why3.conf ?
       if yes, then in fact we don't want it, cf
       https://gitlab.inria.fr/why3/why3/-/merge_requests/692

    let section = set_string ~default:empty_main.libdir
        section "libdir" main.libdir in
    let section = set_string ~default:empty_main.datadir
        section "datadir" main.datadir in
     *)
    let section = set_bool ~default:empty_main.stdlib section "stdlib" main.stdlib in
    let section = set_bool ~default:empty_main.load_default_plugins
        section "load_default_plugins" main.load_default_plugins in
    let section = set_stringl section "loadpath" main.loadpath in
    let section = set_stringl section "plugin" main.plugins in
    let section = set_default_editor main.default_editor section  in
    let section = set_limits ~time:main.timelimit ~mem:main.memlimit ~j:main.running_provers_max section in
    set_section rc "main" section

  let prover_section prover =
    let section = empty_section in
    let section = set_string section "name" prover.prover_name in
    let section = set_string section "version" prover.prover_version in
    set_string ~default:"" section "alternative" prover.prover_altern

  let set_prover _ (prover,shortcuts) family =
    let section = prover_section prover.prover in
    let section = set_string section "command" prover.command in
    let section = set_stringo section "command_steps" prover.command_steps in
    let section = set_string section "driver" (snd prover.driver) in
    let section = set_string section "editor" prover.editor in
    let section = set_bool section "interactive" prover.interactive in
    let section = set_bool section "in_place" prover.in_place in
    let section = set_stringl section "shortcut" shortcuts in
    section::family

  let set_provers rc provers =
    let family = Mprover.fold set_prover provers [] in
    set_simple_family rc "prover" family

  let set_prover_shortcut prover shortcuts family =
    let section = prover_section prover in
    let section = set_stringl section "shortcut" shortcuts in
    section::family

  let set_prover_shortcuts rc shortcuts =
    let family = Mprover.fold set_prover_shortcut shortcuts [] in
    set_simple_family rc "shortcut" family

  let set_provers_shortcuts rc shortcuts provers =
    (* inverse the shortcut map *)
    let shortcuts = Mstr.fold (fun shortcut prover acc ->
        Mprover.change (function
            | None -> Some [shortcut]
            | Some l -> Some (shortcut::l)) prover acc) shortcuts Mprover.empty in
    (* the shortcut to unknown prover *)
    let shortcuts_prover_unknown = Mprover.set_diff shortcuts provers in
    let rc = set_prover_shortcuts rc shortcuts_prover_unknown in
    (* merge the known *)
    let _,shortcuts_provers_known =
      Mprover.mapi_fold (fun k v acc ->
          let acc = Mprover.next_ge_enum k acc in
          match Mprover.val_enum acc with
          | None -> acc,(v,[])
          | Some (ks,vs) ->
              let c = Prover.compare k ks in
              if c = 0 then acc,(v,vs)
              else (* c < 0 *) acc,(v,[])
        ) provers (Mprover.start_enum shortcuts) in
    let rc = set_provers rc shortcuts_provers_known in
    rc

  let set_prover_editor prover editor family =
    let section = prover_section prover in
    let section = set_string section "editor" editor in
    section::family

  let set_prover_editors rc prover_editors =
    let family = Mprover.fold set_prover_editor prover_editors [] in
    set_simple_family rc "prover_editor" family

  exception NonUniqueId

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
    let section = prover_section prover in
    let section =
      match policy with
      | CPU_keep ->
          set_string section "policy" "keep"
      | CPU_remove ->
          set_string section "policy" "remove"
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

end

let empty_rc =
  RC_save.set_main Rc.empty empty_main

let read_config_rc conf_file =
  let read filename =
    filename,
    if filename = "" then empty_rc
    else Rc.from_file filename
  in
  match conf_file with
  | Some filename -> read filename
  | None -> begin try read (Sys.getenv "WHY3CONFIG") with Not_found ->
      if Sys.file_exists default_conf_file then read default_conf_file
      else default_conf_file, empty_rc
    end

let empty_config conf_file =
  {
    conf_file;
    user_rc = Rc.empty;
    main = empty_main;
    provers = Mprover.empty;
    prover_shortcuts = Mstr.empty;
    prover_editors = Mprover.empty;
    editors = Meditor.empty;
    provers_upgrade_policy = Mprover.empty;
    strategies = Mstr.empty;
  }

let default_config conf_file =
  Debug.dprintf debug "[Whyconf.default_config] filename=%s@." conf_file;
  RC_load.config_from_rc (empty_config conf_file) conf_file empty_rc

let read_config_aux config filename rc =
  try
    Debug.dprintf debug "[Whyconf.read_config_aux] filename=%s@." filename;
    RC_load.config_from_rc config filename rc
  with e when not (Debug.test_flag Debug.stack_trace) ->
    let s = Format.asprintf "%a" Exn_printer.exn_printer e in
    raise (ConfigFailure (filename, s))

let read_config conf_file =
  let filename,rc = read_config_rc conf_file in
  try
    Debug.dprintf debug "[Whyconf.read_config] filename=%s@." filename;
    RC_load.config_from_rc (empty_config filename) filename rc
  with e when not (Debug.test_flag Debug.stack_trace) ->
    let s = Format.asprintf "%a" Exn_printer.exn_printer e in
    raise (ConfigFailure (filename, s))

let rc_of_config { main;
                   provers;
                   prover_shortcuts;
                   prover_editors;
                   editors;
                   provers_upgrade_policy;
                   strategies;
                   conf_file = _;
                   user_rc = _;
                 } =
  let rc = Rc.empty in
  let rc = RC_save.set_main rc main in
  let rc = set_strategies rc strategies in
  let rc = RC_save.set_provers_shortcuts rc prover_shortcuts provers in
  let rc = RC_save.set_prover_editors rc prover_editors in
  let rc = RC_save.set_editors rc editors in
  let rc = RC_save.set_policies rc provers_upgrade_policy in
  rc

(** filter prover *)
type regexp_desc = { reg : Re.Str.regexp; desc : string}

let mk_regexp s = { reg = why3_regexp_of_string s; desc = s}

type filter_prover =
  { filter_name    : regexp_desc;
    filter_version : regexp_desc option;
    filter_altern  : regexp_desc option;
  }

let mk_filter_prover ?version ?altern name =
  begin match version with
  | Some "" -> invalid_arg "mk_filter_prover: version can't be an empty string"
  | _ -> () end;
  { filter_name    = mk_regexp name;
    filter_version = Option.map mk_regexp version;
    filter_altern  = Option.map mk_regexp altern;
  }

let filter_from_prover pr =
    { filter_name    = mk_regexp pr.prover_name ;
      filter_version = Some (mk_regexp pr.prover_version);
      filter_altern  = Some (mk_regexp pr.prover_altern);
    }

let print_filter_prover fmt fp =
  match fp.filter_version, fp.filter_altern with
  | None  , None -> pp_print_string fmt fp.filter_name.desc
  | Some v, None -> fprintf fmt "%s,%s" fp.filter_name.desc v.desc
  | None  , Some a -> fprintf fmt "%s,,%s" fp.filter_name.desc a.desc
  | Some v, Some a -> fprintf fmt "%s,%s,%s" fp.filter_name.desc v.desc a.desc

exception ProverNotFound  of config * filter_prover
exception ProverAmbiguity of config * filter_prover * config_prover  Mprover.t
exception ParseFilterProver of string

let parse_filter_prover s =
  let sl = Strings.rev_split ',' s in
  (* reverse order *)
  match sl with
  | [name] -> mk_filter_prover name
  | [version;name] -> mk_filter_prover ~altern:"" ~version name
  | [altern;"";name] -> mk_filter_prover ~altern name
  | [altern;version;name] -> mk_filter_prover ~version ~altern name
  | _ -> raise (ParseFilterProver s)

let filter_prover fp p =
  let check s schema = Re.Str.string_match schema.reg s 0 in
  check p.prover_name fp.filter_name
  && Option.fold ~some:(fun v -> check p.prover_version v) ~none:true fp.filter_version
  && Option.fold ~some:(fun v -> check p.prover_altern v) ~none:true fp.filter_altern

let filter_prover_with_shortcut whyconf fp =
  if fp.filter_version = None && fp.filter_altern = None then
    try
      let prover = (Mstr.find fp.filter_name.desc whyconf.prover_shortcuts) in
      filter_from_prover prover
    with Not_found -> fp
  else fp


let filter_provers whyconf fp =
  let fp = filter_prover_with_shortcut whyconf fp in
  Mprover.filter (fun p _ -> filter_prover fp p) whyconf.provers

let filter_one_prover whyconf fp =
  let provers = filter_provers whyconf fp in
  if Mprover.is_num_elt 1 provers then
    snd (Mprover.choose provers)
  else if Mprover.is_empty provers then
    raise (ProverNotFound (whyconf,fp))
  else
    raise (ProverAmbiguity (whyconf,fp,provers))


(** add extra config *)

let add_extra_config config filename =
  Debug.dprintf debug "[Whyconf.add_extra_config] filename=%s@." filename;
  let dirname = RC_load.get_dirname filename in
  let rc = Rc.from_file filename in
  (* modify main *)
  let main = match get_section rc "main" with
    | None -> config.main
    | Some rc ->
      let loadpath = (List.map (Sysutil.concat dirname)
        (get_stringl rc "loadpath")) @ config.main.loadpath in
      let plugins =
        (get_stringl rc "plugin") @ config.main.plugins in
      { config.main with loadpath = loadpath; plugins = plugins } in
  (* get more strategies *)
  let more_strategies = get_strategies rc in
  let strategies =
    List.fold_left RC_load.load_strategy config.strategies more_strategies
  in
  (* modify provers *)
  let create_filter_prover section =
    try
      let name = get_string section "name" in
      let version = get_stringo section "version" in
      let altern = get_stringo section "alternative" in
      mk_filter_prover ?version ?altern name
    with MissingField s ->
      Loc.warning warn_missing_field "Missing field '%s' in [prover_modifiers] section@." s;
      mk_filter_prover "none"
  in
  let prover_modifiers = get_simple_family rc "prover_modifiers" in
  let prover_modifiers =
    List.map (fun sec -> create_filter_prover sec, sec) prover_modifiers in
  (* add provers *)
  let provers = List.fold_left
    (fun provers (fp, section) ->
      Debug.dprintf debug "handling prover modifiers for %a@." print_filter_prover fp;
      Mprover.mapi (fun p c  ->
        if not (filter_prover fp p) then c
        else
          begin
            Debug.dprintf debug "prover modifiers found for %a@." print_prover p;
            let opt = get_stringl section "option" in
            let drv = get_stringl section "driver" in
            { c with
            extra_options = opt @ c.extra_options;
            extra_drivers = (dirname,drv) :: c.extra_drivers }
          end)
        provers
    ) config.provers prover_modifiers in
  let provers,shortcuts =
    List.fold_left (RC_load.load_prover ~config_dir:(Some dirname))
      (provers,config.prover_shortcuts) (get_simple_family rc "prover") in
  (* modify editors *)
  let editor_modifiers = get_family rc "editor_modifiers" in
  let editors = List.fold_left
    (fun editors (id, section) ->
      Meditor.change (function
      | None -> None
      | Some c ->
        let opt = get_stringl section "option" in
        Some { c with editor_options = opt @ c.editor_options }) id  editors
    ) config.editors editor_modifiers in
  (* add editors *)
  let editors = List.fold_left RC_load.load_editor editors (get_family rc "editor") in
  { config with main = main; provers = provers; strategies = strategies;
    prover_shortcuts = shortcuts; editors = editors }

let save_config config =
  let filename = config.conf_file in
  if filename <> "" then begin
    Sysutil.backup_file filename;
    to_file filename config.user_rc
  end

let get_main config = config.main
let get_provers config = config.provers
let get_prover_editors config = config.prover_editors
let get_prover_config config prover =
  Mprover.find prover (get_provers config)
let get_prover_shortcuts config = config.prover_shortcuts
let get_policies config = config.provers_upgrade_policy
let get_prover_upgrade_policy config p =
  Mprover.find p config.provers_upgrade_policy

let set_main config main =
  {config with
    main = main;
  }

let get_prover_editor config prover =
  try Mprover.find prover config.prover_editors
  with Not_found ->
    (Mprover.find prover config.provers).editor

module User = struct
  let update_section rc section f =
    Option.value ~default:empty_section (Rc.get_section rc section)
    |> f
    |> Rc.set_section rc section

  let set_prover_editor config prover editor =
    let p = Mprover.find prover config.provers in
    let m =
      if editor = p.editor then
        Mprover.remove prover config.prover_editors
      else
        Mprover.add prover editor config.prover_editors in
    { config with
      user_rc = RC_save.set_prover_editors config.user_rc m;
      prover_editors = m }

  let set_default_editor config editor =
    { config with
      user_rc = update_section config.user_rc "main"
        @@ RC_save.set_default_editor editor;
      main = set_default_editor config.main editor;
    }

  let set_limits ~time ~mem ~j config =
    { config with
      user_rc = update_section config.user_rc "main"
        @@ RC_save.set_limits ~time ~mem ~j;
      main = set_limits config.main time mem j;
    }

  let set_prover_upgrade_policy config prover target =
    (* kept simple because no auto upgrade policy *)
    let m = Mprover.add prover target config.provers_upgrade_policy in
    {config with
     user_rc = RC_save.set_policies config.user_rc m;
     provers_upgrade_policy = m;
    }

  let remove_user_policy config prover =
    (* kept simple because no auto upgrade policy *)
    let m = Mprover.remove prover config.provers_upgrade_policy in
    {config with
     user_rc = RC_save.set_policies config.user_rc m;
     provers_upgrade_policy = m;
    }

  let get_section config name =
    get_section config.user_rc name

  let get_simple_family config name =
    get_simple_family config.user_rc name

  let get_family config name =
    get_family config.user_rc name

  let set_section config name section =
    {config with user_rc = set_section config.user_rc name section}

  let set_simple_family config name section =
    {config with user_rc = set_simple_family config.user_rc name section}

  let set_family config name section =
    {config with user_rc = set_family config.user_rc name section}

end

let set_provers config ?shortcuts provers =
  let shortcuts = Option.value ~default:config.prover_shortcuts shortcuts in
  {config with
   provers = provers;
   prover_shortcuts = shortcuts;
  }

let add_provers config provers shortcuts =
  let provers =
    (* we keep existing provers when already present, as said in the interface *)
    Mprover.union (fun _key x _y -> Some x) config.provers provers
  in
  let prover_shortcuts =
    (* we keep existing shortcuts when already present, as said in the interface *)
    Mstr.union (fun _key x _y -> Some x) config.prover_shortcuts shortcuts
  in
  { config with provers; prover_shortcuts }

let set_prover_shortcuts config shortcuts =
  {config with
    prover_shortcuts = shortcuts;
  }

let set_prover_editors config editors =
  { config with prover_editors = editors }

let set_editors config editors =
  { config with
    editors = editors;
  }

let set_prover_upgrade_policy config prover target =
  let m = Mprover.add prover target config.provers_upgrade_policy in
  {config with
    provers_upgrade_policy = m;
  }


let set_policies config policies =
  { config with
    provers_upgrade_policy = policies }



(*******)

(* dead code
let set_conf_file config conf_file = {config with conf_file = conf_file}
*)
let get_conf_file config           =  config.conf_file

(*******)

let is_prover_known whyconf prover =
  Mprover.mem prover (get_provers whyconf)

let get_editors c = c.editors

let editor_by_id whyconf id =
  Meditor.find id whyconf.editors

let get_strategies config = config.strategies

let add_strategy c strat =
  let f = get_strategies c in
  let strategies = Mstr.add strat.strategy_name strat f in
  { c with strategies = strategies }


(******)

let set_stdlib stdlib config =
  {config with main = {config.main with stdlib}}

let set_load_default_plugins load_default_plugins config =
  {config with main = {config.main with load_default_plugins}}

let () = Exn_printer.register (fun fmt e -> match e with
  | ConfigFailure (f, s) ->
      Format.fprintf fmt "error in config file %s: %s" f s
  | WrongMagicNumber ->
      Format.pp_print_string fmt "outdated config file; rerun 'why3 config'"
  | RC_save.NonUniqueId ->
    Format.pp_print_string fmt "InternalError: two provers share the same id"
  | ProverNotFound (config,fp) ->
    fprintf fmt "No prover in %s corresponds to \"%a\"@."
      (get_conf_file config) print_filter_prover fp
  | ProverAmbiguity (config,fp,provers ) ->
    fprintf fmt "More than one prover@ in %s@ correspond@ to \"%a\":@ %a@."
      (get_conf_file config) print_filter_prover fp
      (Pp.print_iter2 Mprover.iter Pp.comma Pp.nothing print_prover Pp.nothing)
      provers
  | ParseFilterProver s ->
    fprintf fmt
      "Syntax error prover identification '%s': \
       name[,version[,alternative]|,,alternative]" s
  | DuplicateShortcut s ->
    fprintf fmt
      "Shortcut %s appears twice in the configuration file" s
  | _ -> raise e)

let provers_from_detected_provers :
  (config -> Rc.t -> config) ref =
  ref (fun _ _-> invalid_arg
          "provers_from_detected_provers: Must be filled by Autodetection")


let add_builtin_provers config rc =
  !provers_from_detected_provers config rc

let init_config ?(extra_config=[]) ofile =
  let save_to,rc = read_config_rc ofile in
  (* load the user configuration, priority over automatic values *)
  let config = read_config_aux (default_config save_to) save_to rc in
  (* Add the automatic provers, shortcuts, strategy, ... *)
  let config = add_builtin_provers config rc in
  (* Add extra-config *)
  Debug.dprintf debug "@[[Whyconf.init_config] calling extra_configs on@ @[%a@]@]@."
    (Pp.print_list Pp.semi Pp.print_string) extra_config;
  let config = List.fold_left add_extra_config config extra_config in
  config

module type Command = functor () -> sig end

let commands : (module Command) Hstr.t = Hstr.create 1

let register_command s f = Hstr.add commands s f

module Args = struct

  let first_arg = ref 1
  let opt_config = ref None
  let opt_extra = ref []
  let opt_loadpath = ref []
  let opt_stdlib = ref true
  let opt_load_default_plugins = ref true

  let add_command s =
    Getopt.commands := !Getopt.commands @ [s]

  let common_options =
    let open Getopt in
    [ Key ('C', "config"), Hnd1 (AString, fun s -> opt_config := Some s),
      "<file> read configuration from <file>";
      KLong "extra-config", Hnd1 (AString, fun s -> opt_extra := !opt_extra @ [s]),
      "<file> read additional configuration from <file>";
      Key ('L', "library"), Hnd1 (AString, fun s -> opt_loadpath := s :: !opt_loadpath),
      "<dir> add <dir> to the library search path";
      KLong "no-stdlib", Hnd0 (fun () -> opt_stdlib := false),
      " do not add the standard library to the loadpath";
      KLong "no-load-default-plugins", Hnd0 (fun () -> opt_load_default_plugins := false),
      " do not load the plugins from the standard path";
      Debug.Args.desc_debug;
      Debug.Args.desc_debug_all;
      Debug.Args.desc_debug_list;
      Loc.Args.desc_no_warn;
      Loc.Args.desc_warning_list;
    ]

  let do_usage fmt options header footer =
    Printf.fprintf fmt "Usage:";
    List.iter (Printf.fprintf fmt " %s") !Getopt.commands;
    Printf.fprintf fmt " [options]";
    if header <> "" then Printf.fprintf fmt " %s" header;
    if header = "" || header.[String.length header - 1] <> '\n' then
      Printf.fprintf fmt "\n";
    if options <> [] then Printf.fprintf fmt "\n%s" (Getopt.format options);
    if footer <> "" then Printf.fprintf fmt "\n%s" footer;
    Printf.fprintf fmt "%!"

  let all_options options header footer =
    let options = ref (common_options @ options) in
    let help =
      let open Getopt in
      (Key ('h', "help"), Hnd0 (fun () -> do_usage stdout !options header footer; exit 0),
       " display this help and exit") in
    options := help :: !options;
    !options

  let complete_initialization () =
    Debug.Args.set_flags_selected ~silent:true ();
    let config = init_config ~extra_config:(!opt_extra) !opt_config in
    (* Set option if they are false *)
    let apply_not_default f o b = if !o then b else f !o b in
    let config = apply_not_default set_stdlib opt_stdlib config in
    let config = apply_not_default set_load_default_plugins opt_load_default_plugins config in
    let main = get_main config in
    let lp = List.rev_append !opt_loadpath (loadpath main) in
    let config = set_main config (set_loadpath main lp) in
    load_plugins main;
    Debug.Args.set_flags_selected ();
    Loc.Args.set_flags_selected ();
    if Debug.Args.option_list () then exit 0;
    if Loc.Args.option_list () then exit 0;
    config, Env.create_env lp

  let initialize ?(extra_help="") options default usage =
    let options = all_options options usage extra_help in
    Getopt.parse_all ~i:!first_arg options default Sys.argv;
    complete_initialization ()

  let exit_with_usage ?(extra_help="") usage =
    do_usage stderr [] usage extra_help;
    exit 1
end

let unknown_to_known_provers provers pu =
  Mprover.fold (fun pk _ (others,name,version) ->
    match
      pk.prover_name = pu.prover_name,
      pk.prover_version = pu.prover_version,
      pk.prover_altern = pu.prover_altern with
        | false, _, _ -> pk::others, name, version
        | _, false, _ -> others, pk::name, version
        | _           -> others, name, pk::version
  ) provers ([],[],[])
