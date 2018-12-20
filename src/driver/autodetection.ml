(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

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
detected. If a message is not present, we print ", OK." if the version
is good (version_good) and not old, and " (it is an old version)." if
the version is old (version_old).

The field command can be missing in a block, in that case the block
defines a version known to be buggy: no prover config is generated.

The regexp must start with ^.

*)

open Format
open Wstdlib
open Whyconf
module Wc = Whyconf
open Rc

let debug = Debug.register_info_flag "autodetect"
  ~desc:"Print@ debugging@ messages@ about@ auto-detection@ \
         of@ external@ provers."

(* auto-detection of provers *)

type prover_kind = ATP | ITP
type prover_autodetection_data =
    { kind : prover_kind;
      prover_id : string;
      prover_name : string;
      prover_altern : string;
      support_library : string;
      execs : string list;
      version_switch : string;
      version_regexp : string;
      versions_ok : (string * Str.regexp) list;
      versions_old : (string * Str.regexp) list;
      versions_bad : (string * Str.regexp) list;
      (** If none it's a fake prover (very bad version) *)
      prover_command : string option;
      prover_command_steps : string option;
      prover_driver : string;
      prover_editor : string;
      prover_in_place : bool;
      use_at_auto_level : int;
      message : string option;
    }

let prover_keys =
  let add acc k = Sstr.add k acc in
  List.fold_left add Sstr.empty
    ["name";"support_library";
     "exec";"version_switch";"version_regexp";
     "version_ok";"version_old";"version_bad";"command"; "command_steps";
     "editor";"driver";"in_place";"message";"alternative";"use_at_auto_level"]

let load_prover kind (id,section) =
  check_exhaustive section prover_keys;
  let reg_map = List.rev_map (fun s -> (s,why3_regexp_of_string s)) in
  let prover = { kind = kind;
    prover_id = id;
    prover_name = get_string section "name";
    prover_altern = get_string section ~default:"" "alternative";
    support_library = get_string section ~default:"" "support_library";
    execs = get_stringl section "exec";
    version_switch = get_string section ~default:"" "version_switch";
    version_regexp = get_string section ~default:"" "version_regexp";
    versions_ok = reg_map (get_stringl section ~default:[] "version_ok");
    versions_old = reg_map (get_stringl section ~default:[] "version_old");
    versions_bad = reg_map (get_stringl section ~default:[] "version_bad");
    prover_command = get_stringo section "command";
    prover_command_steps = get_stringo section "command_steps";
    prover_driver = get_string section ~default:""  "driver";
    prover_editor = get_string section ~default:"" "editor";
    prover_in_place = get_bool section ~default:false "in_place";
    use_at_auto_level = get_int section ~default:0 "use_at_auto_level";
    message = get_stringo section "message";
  } in
  if prover.prover_command != None && prover.prover_driver = "" then
    invalid_arg
      (sprintf "In section prover %s command specified without driver" id);
  prover

(* dead code
let editor_keys =
  let add acc k = Sstr.add k acc in
  List.fold_left add Sstr.empty
    ["command"]
*)

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
  let tps = List.fold_left (Lists.cons (load_prover ITP)) atps itps in
  tps

let load_prover_shortcut acc (_, section) =
  let name = get_string section "name" in
  let version = get_stringo section "version" in
  let altern = get_stringo section "alternative" in
  let shortcuts = get_stringl section "shortcut" in
  let fp = mk_filter_prover ?version ?altern name in
  List.fold_left (fun acc shortcut ->
    (fp,shortcut)::acc
  ) acc shortcuts

module Hstr2 = Hashtbl.Make(struct
  type t = string * string
  let hash = Hashtbl.hash
  let equal = (=)
end)

type env =
  {
    (* memoization of (exec_name,version_switch)
        -> Some output | None doesn't exists *)
    prover_output : string option Hstr2.t;
    (* existing executable table:
        exec_name -> | Some (priority, id, prover_config)
                                  unknown version (neither good or bad)
                     | None               there is a good version *)
    prover_unknown_version :
      (prover_autodetection_data * int * string * config_prover) option Hstr.t;
    (* string -> priority * prover  *)
    prover_shortcuts : (int * prover) Hstr.t;
    mutable possible_prover_shortcuts : (filter_prover * string) list;
  }

let create_env shortcuts =
{ prover_output = Hstr2.create 10;
  prover_unknown_version = Hstr.create 10;
  prover_shortcuts = Hstr.create 5;
  possible_prover_shortcuts = shortcuts;
 }

let next_priority =
  let r = ref 0 in
  fun () -> decr r; !r

let highest_priority = 0

let read_auto_detection_data main =
  let filename = Filename.concat (Whyconf.datadir main)
    "provers-detection-data.conf" in
  try
    let rc = Rc.from_file filename in
    let shortcuts =
      List.fold_left load_prover_shortcut [] (get_family rc "shortcut") in
    List.rev (load rc), create_env shortcuts
  with
    | Failure "lexing" ->
        Loc.errorm "Syntax error in provers-detection-data.conf@."
    | Not_found ->
        Loc.errorm "provers-detection-data.conf not found at %s@." filename

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

let make_command =
  let cmd_regexp = Str.regexp "%\\(.\\)" in
  fun exec com ->
    let replace s = match Str.matched_group 1 s with
      | "e" -> exec
      | c -> "%"^c
    in
    Str.global_substitute cmd_regexp replace com

(* dead code
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
*)

let ask_prover_version exec_name version_switch =
  let out = Filename.temp_file "out" "" in
  let cmd = sprintf "%s %s" exec_name version_switch in
  let c = sprintf "(%s) > %s 2>&1" cmd out in
  Debug.dprintf debug "Run: %s@." c;
  try
    let ret = Sys.command c in
    let ch = open_in out in
    let c = Sysutil.channel_contents ch in
    close_in ch;
    Sys.remove out;
    if ret <> 0 then begin
      Debug.dprintf debug "command '%s' failed. Output:@\n%s@." cmd c;
      None
    end else Some c
  with Not_found | End_of_file | Sys_error _ ->
    Debug.dprintf debug "command '%s' failed@." cmd;
    None

let ask_prover_version env exec_name version_switch =
  try
    Hstr2.find env.prover_output (exec_name,version_switch)
  with Not_found ->
    let res = ask_prover_version exec_name version_switch in
    Hstr2.add env.prover_output (exec_name,version_switch) res;
    res

let check_version version (_,schema) = Str.string_match schema version 0

let known_version env exec_name =
  Hstr.replace env.prover_unknown_version exec_name None

let unknown_version env exec_name prover_id prover_config data priority =
  if not (Hstr.mem env.prover_unknown_version exec_name)
  then Hstr.replace env.prover_unknown_version exec_name
    (Some (data,priority,prover_id,prover_config))


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
    (* start with 2 in order to have toto_alt, toto_alt2,
       toto_alt3,... and not toto_alt, toto_alt1 which can be
       confusing *)
    aux 2

let add_prover_with_uniq_id prover provers =
  (* find an unique prover triplet *)
  let prover_id = find_prover_altern provers prover.Wc.prover in
  let prover = {prover with Wc.prover = prover_id} in
  Mprover.add prover_id prover provers

let add_prover_shortcuts env prover =
  let rec aux = function
    | [] -> []
    | (fp,s)::l when filter_prover fp prover ->
      Hstr.replace env.prover_shortcuts s (highest_priority,prover);
      aux l
    | a::l -> a::(aux l) in
  env.possible_prover_shortcuts <- aux env.possible_prover_shortcuts

let add_id_prover_shortcut env id prover priority =
  match Hstr.find_opt env.prover_shortcuts id with
  | Some (p,_) when p >= priority -> ()
(*
  | Some _ -> assert false
 *)
  | _ -> Hstr.replace env.prover_shortcuts id (priority,prover)

let prover_auto_levels = Hprover.create 5

let record_prover_for_auto_mode prover level =
  Hprover.replace prover_auto_levels prover (level,false)

let check_prover_auto_level prover =
  try
    let lev,_ = Hprover.find prover_auto_levels prover in
    Hprover.replace prover_auto_levels prover (lev,true)
  with Not_found -> ()

let generate_auto_strategies config =
  eprintf "Generating strategies:@.";
  Hprover.iter
    (fun p (lev,b) ->
     if b then eprintf "  Prover %a will be used in Auto level >= %d@."
                       Whyconf.print_prover p lev) prover_auto_levels;
  (* Split VCs *)
  let code = "t split_vc exit" in
  let split = {
      strategy_name = "Split_VC";
      strategy_desc = "Split@ the@ VC@ into@ subgoals";
      strategy_shortcut = "s";
      strategy_code = code }
  in
  (* Auto level 0 and 1 *)
  let provers_level1 =
    Hprover.fold
      (fun p (lev,b) acc ->
       if b && lev = 1 then
         let name = Whyconf.prover_parseable_format p in name :: acc
       else acc) prover_auto_levels []
  in
  List.iter (fun s -> fprintf str_formatter "c %s 1 1000@\n" s) provers_level1;
  let code = flush_str_formatter () in
  let auto0 = {
      strategy_name = "Auto_level_0";
      strategy_desc = "Automatic@ run@ of@ main@ provers";
      strategy_shortcut = "0";
      strategy_code = code }
  in
  fprintf str_formatter "start:@\n";
  List.iter (fun s -> fprintf str_formatter "c %s 1 1000@\n" s) provers_level1;
  fprintf str_formatter "t split_all_full start@\n";
  List.iter (fun s -> fprintf str_formatter "c %s 10 4000@\n" s) provers_level1;
  let code = flush_str_formatter () in
  let auto1 = {
      strategy_name = "Auto_level_1";
      strategy_desc = "Automatic@ run@ of@ main@ provers";
      strategy_shortcut = "1";
      strategy_code = code }
  in
  (* Auto level 2 *)
  let provers_level2 =
    Hprover.fold
      (fun p (lev,b) acc ->
       if b && lev >= 1 && lev <= 2 then
         let name = Whyconf.prover_parseable_format p in name :: acc
       else acc) prover_auto_levels []
  in
  fprintf str_formatter "start:@\n";
  List.iter (fun s -> fprintf str_formatter "c %s 1 1000@\n" s) provers_level2;
  fprintf str_formatter "t split_all_full start@\n";
  List.iter (fun s -> fprintf str_formatter "c %s 5 2000@\n" s) provers_level2;
  fprintf str_formatter "t introduce_premises afterintro@\n";
  fprintf str_formatter "afterintro:@\n";
  fprintf str_formatter "t inline_goal afterinline@\n";
  fprintf str_formatter "g trylongertime@\n";
  fprintf str_formatter "afterinline:@\n";
  fprintf str_formatter "t split_all_full start@\n";
  fprintf str_formatter "trylongertime:@\n";
  List.iter (fun s -> fprintf str_formatter "c %s 30 4000@\n" s) provers_level2;
  let code = flush_str_formatter () in
  let auto2 = {
      strategy_name = "Auto_level_2";
      strategy_desc = "Automatic@ run@ of@ provers@ and@ most@ useful@ transformations";
      strategy_shortcut = "2";
      strategy_code = code }
  in
  add_strategy
    (add_strategy
       (add_strategy
          (add_strategy config split) auto0) auto1) auto2

let check_support_library data ver =
  let cmd_regexp = Str.regexp "%\\(.\\)" in
  let replace s = match Str.matched_group 1 s with
    | "l" -> Config.libdir
    | "d" -> Config.datadir
    | c -> c in
  let sl = Str.global_substitute cmd_regexp replace data.support_library in
  try
    let f = open_in sl in
    let support_ver = input_line f in
    close_in f;
    if support_ver = ver then true
    else if support_ver = "" then raise Not_found
    else begin
      eprintf
        "Found prover %s version %s, but the compiled Why3 library supports only version %s@."
        data.prover_name ver support_ver;
      false
    end
  with Sys_error _ | Not_found ->
    eprintf
      "Found prover %s version %s, but no Why3 libraries were compiled for it@."
      data.prover_name ver;
    false

exception Skip    (* prover is ignored *)
exception Discard (* prover is recognized, but unusable *)

let detect_exec env data exec_name =
  let s = ask_prover_version env exec_name data.version_switch in
  let s =
    match s with
    | None -> raise Skip
    | Some s -> s in
  let re = Str.regexp data.version_regexp in
  let ver =
    try
      ignore (Str.search_forward re s 0);
      Str.matched_group 1 s
    with Not_found ->
      Debug.dprintf debug "Warning: found prover %s but name/version not \
                       recognized by regexp `%s'@."
        data.prover_name data.version_regexp;
      Debug.dprintf debug "Answer was `%s'@." s;
      ""
  in
  (* bad here means not good, it is not the same thing as a version
     of a prover with known problems *)
  let bad = List.exists (check_version ver) data.versions_bad in
  if bad then raise Discard;
  let good = List.exists (check_version ver) data.versions_ok in
  let old  = List.exists (check_version ver) data.versions_old in
  let prover_command =
    match data.prover_command with
    | None ->
      (* empty prover: a matching version means known problems *)
      if not (good || old) then raise Skip;
      eprintf "Found prover %s version %s%s@."
        data.prover_name ver
        (Opt.get_def
           ". This version of the prover is known to have problems."
           data.message);
      raise Discard
    | Some prover_command -> prover_command
  in
  (* create the prover config *)
  let c = make_command exec_name prover_command in
  let c_steps = Opt.map (make_command exec_name) data.prover_command_steps in
  let prover =
    { Wc.prover_name = data.prover_name;
      prover_version = ver;
      prover_altern = data.prover_altern } in
  let prover_config =
    { prover = prover;
      command = c;
      command_steps = c_steps;
      driver = data.prover_driver;
      editor = data.prover_editor;
      in_place = data.prover_in_place;
      interactive = (match data.kind with ITP -> true | ATP -> false);
      extra_options = [];
      extra_drivers = [];
      configure_build = "";
      build_commands = []
    }
  in
  (* if unknown, temporarily put the prover away *)
  if not (good || old) then begin
    let priority = next_priority () in
    unknown_version env exec_name data.prover_id prover_config data priority;
    raise Skip
  end;
  (* check if this prover needs compile-time support *)
  if data.support_library <> "" && not (check_support_library data ver) then
    raise Discard;
  let priority = next_priority () in
  eprintf "Found prover %s version %s%s@."
    data.prover_name ver
    (Opt.get_def
       (if old then
	   " (old version, please consider upgrading)."
	else
	   if data.prover_altern <> "" then
	     " (alternative: " ^ data.prover_altern ^ ")"
	   else
	     ", OK.")
       data.message);
  add_prover_shortcuts env prover;
  add_id_prover_shortcut env data.prover_id prover priority;
  let level = data.use_at_auto_level in
  if level > 0 then record_prover_for_auto_mode prover level;
  prover_config

let detect_exec env data acc exec_name =
  try
    let prover_config = detect_exec env data exec_name in
    known_version env exec_name;
    add_prover_with_uniq_id prover_config acc
  with
  | Skip -> acc
  | Discard -> known_version env exec_name; acc

let detect_prover env acc data =
  List.fold_left (detect_exec env data) acc data.execs

let pp_versions =
  Pp.print_list Pp.comma
                (Pp.print_pair_delim Pp.nothing Pp.nothing Pp.nothing Pp.string Pp.nothing)

let detect_unknown env pc =
  let (data,priority,prover_id,prover_config) =
    match pc with
    | None -> raise Skip
    | Some pc -> pc in
  let prover = prover_config.prover in
  let ver = prover.prover_version in
  if data.support_library <> "" && not (check_support_library data ver) then raise Skip;
  Warning.emit "@[Prover %s version %s is not known to be supported.@\n\
                Known versions for this prover:@ %a@\n\
                Known old versions for this prover:@ %a@]@."
    prover.Wc.prover_name ver
    pp_versions data.versions_ok
    pp_versions data.versions_old;
  add_id_prover_shortcut env prover_id prover priority;
  prover_config

let detect_unknown env detected =
  Hstr.fold (fun _ pc acc ->
    try add_prover_with_uniq_id (detect_unknown env pc) acc
    with Skip -> acc)
    env.prover_unknown_version detected

let convert_shortcuts env =
  Hstr.fold (fun s (_,p) acc ->
    check_prover_auto_level p; Mstr.add s p acc
  ) env.prover_shortcuts Mstr.empty

let run_auto_detection config =
  let main = get_main config in
  let l,env = read_auto_detection_data main in
  let detected = List.fold_left (detect_prover env) Mprover.empty l in
  let length_recognized = Mprover.cardinal detected in
  let detected = detect_unknown env detected in
  let length_detected = Mprover.cardinal detected in
  if length_detected > length_recognized then
    eprintf
      "%d prover(s) added (including %d prover(s) with an unrecognized version)@."
      length_detected (length_detected - length_recognized)
  else
    eprintf "%d prover(s) added@." length_detected;
  let shortcuts = convert_shortcuts env in
  let config = generate_auto_strategies config in
  let config = set_editors config (read_editors main) in
  let config = set_prover_shortcuts config shortcuts in
  let config = set_provers config detected in
  config

let list_prover_families () =
  let config = default_config "" in
  let main = get_main config in
  let l,_ = read_auto_detection_data main in
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

let add_existing_shortcuts env shortcuts =
  let aux shortcut prover =
    Hstr.replace env.prover_shortcuts shortcut (highest_priority,prover);
    env.possible_prover_shortcuts <-
      List.filter (fun (_,s) -> s = shortcut)
      env.possible_prover_shortcuts
  in
  Mstr.iter aux shortcuts

let add_prover_binary config id shortcut path =
  let main = get_main config in
  let l,env = read_auto_detection_data main in
  let prover_shortcuts = get_prover_shortcuts config in
  if Mstr.mem shortcut prover_shortcuts then
    Loc.errorm "Shortcut %s already in use" shortcut;
  add_existing_shortcuts env prover_shortcuts;
  let l = List.filter (fun p -> p.prover_id = id) l in
  if l = [] then begin
    let list_of_allowed_id =
      Format.asprintf "@[<hov 2>Known prover families:@\n%a@]@\n@."
        (Pp.print_list Pp.newline Pp.string)
        (List.sort String.compare (list_prover_families ())) in
    Loc.errorm "Unknown prover id: %s\n%s" id list_of_allowed_id end;
  let detected = List.fold_left
    (fun acc data -> detect_exec env data acc path) Mprover.empty l in
  let detected = detect_unknown env detected in
  if Mprover.is_empty detected then
    Loc.errorm "File %s does not correspond to the prover id %s" path id;
  let provers = get_provers config in
  let fold _ p provers =
    (* find a prover altern not used *)
    (* Is a prover with this name and version already in config? *)
    let prover_id =
      if not (Mprover.mem p.prover provers) then p.prover else
        let alt = match p.prover.Wc.prover_altern, get_altern id path with
          | "", s -> s | s, "" -> s | s1, s2 -> s1 ^ " " ^ s2 in
        let prover_id = { p.prover with Wc.prover_altern = alt } in
        find_prover_altern provers prover_id in
    let p = {p with prover = prover_id} in
    add_prover_with_uniq_id p provers in
  let provers = Mprover.fold fold detected provers in
  let prover = fst (Mprover.choose detected) in
  let shortcuts = Mstr.add shortcut prover (convert_shortcuts env) in
  let config = set_provers config ~shortcuts provers in
  config
