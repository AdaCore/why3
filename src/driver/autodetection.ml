(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
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

[@@@ocaml.warning "-40-42"]

let debug = Debug.register_info_flag "autodetect"
  ~desc:"Print@ debugging@ messages@ about@ auto-detection@ \
         of@ external@ provers."

let is_config_command = ref false

let print_info fmt =
  if !is_config_command
  then Format.printf fmt
  else Debug.dprintf debug fmt

module Prover_autodetection_data = struct
  (* auto-detection of provers *)
  type prover_kind = ATP | ITP
  type data =
    { kind : prover_kind;
      prover_id : string;
      prover_name : string;
      prover_altern : string;
      support_library : string;
      execs : string list;
      version_switch : string;
      version_regexp : string;
      versions_ok : (string * Re.Str.regexp) list;
      versions_old : (string * Re.Str.regexp) list;
      versions_bad : (string * Re.Str.regexp) list;
      (** If none it's a fake prover (very bad version) *)
      prover_command : string option;
      prover_command_steps : string option;
      prover_driver : string;
      prover_editor : string;
      prover_in_place : bool;
      use_at_auto_level : int;
      message : string option;
    }

  type t = {
    skeletons: data list;
    (** Additional shortcuts *)
    shortcuts: (Whyconf.filter_prover * string) list;
    editors: Whyconf.config_editor Meditor.t;
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

  let read_auto_detection_data main =
    let filename = Filename.concat (Whyconf.datadir main)
        "provers-detection-data.conf" in
    try
      let rc = Rc.from_file filename in
      { skeletons = List.rev (load rc);
        shortcuts =
          List.fold_left load_prover_shortcut [] (get_family rc "shortcut");
        editors =
          List.fold_left (fun editors (id, section) ->
              Meditor.add id (load_editor section) editors
            ) Meditor.empty (get_family rc "editor")
      }
    with
    | Failure _ ->
        Loc.errorm "Syntax error in provers-detection-data.conf@."
    | Not_found ->
        Loc.errorm "provers-detection-data.conf not found at %s@." filename


end

module Detected_binary = struct

  let section_name = "detected_binary"

  type t = {
    exec_name  : string;
    version : string;
    binary : string;
    shortcut : string option;
  }

  let load_one acc section =
    try
      let exec_name = get_string section "exec_name" in
      let v = {
        exec_name;
        version = get_string section "version";
        binary = get_string ~default:exec_name section "binary";
        shortcut = get_stringo section "shortcut";
      } in
      v::acc
    with MissingField s ->
      Warning.emit "[Warning] cannot load a detected_prover section: missing field '%s'@." s;
      acc

  let load_rc rc =
    List.fold_left load_one
      [] (get_simple_family rc section_name)

  let load rc =
    List.fold_left load_one
      [] (Whyconf.User.get_simple_family rc section_name)

  let set_one prover =
    let section = empty_section in
    let section = set_string section "exec_name" prover.exec_name in
    let section = set_string section "version" prover.version in
    let section = set_string ~default:prover.exec_name section "binary" prover.binary in
    let section = set_stringo section "shortcut" prover.shortcut in
    section

  let set config detected_provers =
    let family = List.map set_one detected_provers in
    Whyconf.User.set_simple_family config section_name family

  let add rc m =
    let l = List.filter (fun x -> x.binary <> m.binary) (load rc) in
    set rc (m::l)

end

module Manual_binary = struct

  let section_name = "manual_binary"

  type t = {
    same_as  : string;
    binary : string; (* custom executable *)
    shortcut: string;
  }

  let load_one acc section =
    try
      let v = {
        same_as = get_string section "same_as";
        binary = get_string section "binary";
        shortcut = get_string section "shortcut";
      } in
      v::acc
    with MissingField s ->
      Warning.emit "[Warning] cannot load a manual_prover section: missing field '%s'@." s;
      acc

  let load rc =
    List.fold_left load_one
      [] (Whyconf.User.get_simple_family rc section_name)

  let set_one prover =
    let section = empty_section in
    let section = set_string section "same_as" prover.same_as in
    let section = set_string section "binary" prover.binary in
    let section = set_string section "shortcut" prover.shortcut in
    section

  let set rc detected_provers =
    let family = List.map set_one detected_provers in
    Whyconf.User.set_simple_family rc section_name family

  let add rc m =
    let l = List.filter (fun x -> x.shortcut <> m.shortcut) (load rc) in
    set rc (m::l)

end

type unknown_version = {
  exec_name:string;
  data:Prover_autodetection_data.data;
  priority:int;
  shortcut:string;
  prover_config:config_prover;
}

type env =
  {
    binaries : Detected_binary.t list Mstr.t;
    (* prover_unknown_version:
        exec_name -> | Some unknown_version
                            unknown version (neither good or bad)
                     | None
                            there is a good version *)
    prover_unknown_version : unknown_version option Hstr.t;
    (* string -> priority * prover  *)
    prover_shortcuts : (int * prover) Hstr.t;
    mutable possible_prover_shortcuts : (filter_prover * string) list;
    prover_auto_levels : (int * bool) Hprover.t;
  }

let create_env binaries shortcuts = {
  binaries;
  prover_unknown_version = Hstr.create 10;
  prover_shortcuts = Hstr.create 5;
  possible_prover_shortcuts = shortcuts;
  prover_auto_levels = Hprover.create 5;
}

let next_priority =
  let r = ref 0 in
  fun () -> decr r; !r

let highest_priority = 0

let make_command =
  let cmd_regexp = Re.Str.regexp "%\\(.\\)" in
  fun exec com ->
    let replace s = match Re.Str.matched_group 1 s with
      | "e" -> exec
      | c -> "%"^c
    in
    Re.Str.global_substitute cmd_regexp replace com

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

let check_version version (_,schema) = Re.Str.string_match schema version 0

let known_version env exec_name =
  Hstr.replace env.prover_unknown_version exec_name None

let unknown_version env exec_name binary shortcut prover_config data priority =
  if not (Hstr.mem env.prover_unknown_version binary)
  then Hstr.replace env.prover_unknown_version binary
    (Some {exec_name;data;priority;shortcut;prover_config})


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

let record_prover_for_auto_mode env prover level =
  Hprover.replace env.prover_auto_levels prover (level,false)

let check_prover_auto_level env prover =
  try
    let lev,_ = Hprover.find env.prover_auto_levels prover in
    Hprover.replace env.prover_auto_levels prover (lev,true)
  with Not_found -> ()

let generate_auto_strategies env =
  print_info "Generating strategies:@.";
  Hprover.iter
    (fun p (lev,b) ->
     if b then print_info "  Prover %a will be used in Auto level >= %d@."
                       Whyconf.print_prover p lev) env.prover_auto_levels;
  (* Split VCs *)
  let code = "t split_vc exit" in
  let split = {
      strategy_name = "Split_VC";
      strategy_desc = "Split@ the@ VC@ into@ subgoals";
      strategy_shortcut = "s";
      strategy_code = code }
  in
  (* Auto level 0 and 1 and 2 *)
  let provers_level1 =
    Hprover.fold
      (fun p (lev,b) acc ->
       if b && lev = 1 then
         let name = Whyconf.prover_parseable_format p in name :: acc
       else acc) env.prover_auto_levels []
  in
  List.iter (fun s -> fprintf str_formatter "c %s 1 1000@\n" s) provers_level1;
  let code = flush_str_formatter () in
  let auto0 = {
      strategy_name = "Auto_level_0";
      strategy_desc = "Automatic@ run@ of@ main@ provers";
      strategy_shortcut = "0";
      strategy_code = code }
  in
  List.iter (fun s -> fprintf str_formatter "c %s 5 1000@\n" s) provers_level1;
  let code = flush_str_formatter () in
  let auto1 = {
      strategy_name = "Auto_level_1";
      strategy_desc = "Automatic@ run@ of@ main@ provers for longer times";
      strategy_shortcut = "1";
      strategy_code = code }
  in
  fprintf str_formatter "start:@\n";
  List.iter (fun s -> fprintf str_formatter "c %s 1 1000@\n" s) provers_level1;
  fprintf str_formatter "t split_vc start@\n";
  List.iter (fun s -> fprintf str_formatter "c %s 10 4000@\n" s) provers_level1;
  let code = flush_str_formatter () in
  let auto2 = {
      strategy_name = "Auto_level_2";
      strategy_desc = "Automatic@ run@ of@ main@ provers and splitting";
      strategy_shortcut = "2";
      strategy_code = code }
  in
  (* Auto level 3 *)
  let provers_level3 =
    Hprover.fold
      (fun p (lev,b) acc ->
       if b && lev >= 1 && lev <= 2 then
         let name = Whyconf.prover_parseable_format p in name :: acc
       else acc) env.prover_auto_levels []
  in
  fprintf str_formatter "start:@\n";
  List.iter (fun s -> fprintf str_formatter "c %s 1 1000@\n" s) provers_level3;
  fprintf str_formatter "t split_vc start@\n";
  List.iter (fun s -> fprintf str_formatter "c %s 5 2000@\n" s) provers_level3;
  fprintf str_formatter "t introduce_premises afterintro@\n";
  fprintf str_formatter "afterintro:@\n";
  fprintf str_formatter "t inline_goal afterinline@\n";
  fprintf str_formatter "g trylongertime@\n";
  fprintf str_formatter "afterinline:@\n";
  fprintf str_formatter "t split_all_full start@\n";
  fprintf str_formatter "trylongertime:@\n";
  List.iter (fun s -> fprintf str_formatter "c %s 30 4000@\n" s) provers_level3;
  let code = flush_str_formatter () in
  let auto3 = {
      strategy_name = "Auto_level_3";
      strategy_desc = "Automatic@ run@ of@ provers@ and@ most@ useful@ transformations";
      strategy_shortcut = "3";
      strategy_code = code }
  in
  [split ; auto0 ; auto1 ; auto2 ; auto3]

let check_support_library (data:Prover_autodetection_data.data) ver =
  let cmd_regexp = Re.Str.regexp "%\\(.\\)" in
  let replace s = match Re.Str.matched_group 1 s with
    | "l" -> Config.libdir
    | "d" -> Config.datadir
    | c -> c in
  let sl = Re.Str.global_substitute cmd_regexp replace data.support_library in
  try
    let f = open_in sl in
    let support_ver = input_line f in
    close_in f;
    if support_ver = ver then true
    else if support_ver = "" then raise Not_found
    else begin
      print_info
        "Found prover %s version %s, but the compiled Why3 library supports only version %s@."
        data.prover_name ver support_ver;
      false
    end
  with Sys_error _ | Not_found ->
    print_info
      "Found prover %s version %s, but no Why3 libraries were compiled for it@."
      data.prover_name ver;
    false

exception Skip    (* prover is ignored *)
exception Discard (* prover is recognized, but unusable *)

let detect_exec_skip env (data:Prover_autodetection_data.data) (p:Detected_binary.t) =
  (* bad here means not good, it is not the same thing as a version
     of a prover with known problems *)
  let bad = List.exists (check_version p.version) data.versions_bad in
  if bad then raise Discard;
  let good = List.exists (check_version p.version) data.versions_ok in
  let old  = List.exists (check_version p.version) data.versions_old in
  let pp_shortcut fmt = Opt.iter (Format.fprintf fmt (" (manually added as %s)")) p.shortcut in
  let prover_command =
    match data.prover_command with
    | None ->
      (* empty prover: a matching version means known problems *)
      if not (good || old) then raise Skip;
      print_info "Found prover %s%t version %s%s@."
        data.prover_name
        pp_shortcut
        p.version
        (Opt.get_def
           ". This version of the prover is known to have problems."
           data.message);
      raise Discard
    | Some prover_command -> prover_command
  in
  (* create the prover config *)
  let c = make_command p.binary prover_command in
  let c_steps = Opt.map (make_command p.binary) data.prover_command_steps in
  let prover =
    { Wc.prover_name = data.prover_name;
      prover_version = p.version;
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
    } in
  (* if unknown, temporarily put the prover away *)
  let shortcut = Opt.get_def data.prover_id p.shortcut in
  if not (good || old) then begin
    let priority = next_priority () in
    unknown_version env p.exec_name p.binary shortcut prover_config data priority;
    raise Skip
  end;
  (* check if this prover needs compile-time support *)
  if data.support_library <> "" && not (check_support_library data p.version) then
    raise Discard;
  let priority = next_priority () in
  print_info "Found prover %s%t version %s%s@."
    data.prover_name pp_shortcut p.version
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
  add_id_prover_shortcut env shortcut prover priority;
  let level = data.use_at_auto_level in
  if level > 0 then record_prover_for_auto_mode env prover level;
  prover_config

let detect_exec env data acc exec_name =
  let l = Mstr.find_def [] exec_name env.binaries in
  List.fold_left (fun acc p ->
      try
        let prover_config = detect_exec_skip env data p in
        known_version env exec_name;
        add_prover_with_uniq_id prover_config acc
      with
      | Skip -> acc
      | Discard -> known_version env exec_name; acc
    )
    acc l

let detect_prover env acc data =
  List.fold_left (detect_exec env data) acc data.execs

let pp_versions =
  Pp.print_list Pp.comma
                (Pp.print_pair_delim Pp.nothing Pp.nothing Pp.nothing Pp.string Pp.nothing)

let detect_unknown_skip env uv =
  let prover = uv.prover_config.prover in
  let ver = prover.prover_version in
  if uv.data.support_library <> "" && not (check_support_library uv.data ver) then raise Skip;
  print_info
    "@[<v>@[Prover %s version %s is not known to be supported.@]@ \
     @[Known versions for this prover:@ %a.@]@ \
     @[Known old versions for this prover:@ %a.@]@]@."
    prover.Wc.prover_name ver
    pp_versions uv.data.versions_ok
    pp_versions uv.data.versions_old;
  add_id_prover_shortcut env uv.shortcut prover uv.priority;
  uv.prover_config

let detect_unknown env detected =
  Hstr.fold (fun _ pc acc ->
      match pc with
      | None -> acc
      | Some uv ->
          try
            add_prover_with_uniq_id (detect_unknown_skip env uv) acc
          with Skip -> acc
    ) env.prover_unknown_version detected

let convert_shortcuts env =
  Hstr.fold (fun s (_,p) acc ->
    check_prover_auto_level env p; Mstr.add s p acc
  ) env.prover_shortcuts Mstr.empty

let run_auto_detection' env l =
  let detected = List.fold_left (detect_prover env) Mprover.empty l in
  let length_recognized = Mprover.cardinal detected in
  let detected = detect_unknown env detected in
  let length_detected = Mprover.cardinal detected in
  if length_detected > length_recognized then
    print_info
      "%d prover(s) added (including %d prover(s) with an unrecognized version)@."
      length_detected (length_detected - length_recognized)
  else
    print_info "%d prover(s) added@." length_detected;
  detected

let generate_builtin_config env datas detected config =
  let shortcuts = convert_shortcuts env in
  let config =
    List.fold_left add_strategy config
      (generate_auto_strategies env)
  in
  let config = set_editors config datas.Prover_autodetection_data.editors in
  let config = set_prover_shortcuts config shortcuts in
  let config = set_provers config detected in
  config

let read_auto_detection_data config =
  let main = get_main config in
  Prover_autodetection_data.read_auto_detection_data main

let () =
  let provers_from_detected_provers ~save_to rc =
    let provers_output = Detected_binary.load_rc rc in
    let binaries =
      List.fold_left (fun acc (p:Detected_binary.t) ->
                      Mstr.change (function
                          | None -> Some [p]
                          | Some l -> Some (p::l))
                           p.exec_name acc)
        Mstr.empty provers_output
    in
    let config = Whyconf.default_config save_to in
    let datas = read_auto_detection_data config in
    let env = create_env binaries datas.shortcuts in
    let detected = run_auto_detection' env datas.skeletons in
    generate_builtin_config env datas detected config
  in
  Whyconf.provers_from_detected_provers :=
    provers_from_detected_provers

let list_binaries () =
  let config = default_config "" in
  let datas = read_auto_detection_data config in
  let s = List.fold_left (fun s p ->
      List.fold_right Sstr.add p.Prover_autodetection_data.execs s)
      Sstr.empty datas.skeletons
  in
  Sstr.elements s

let detect_prover exec_name binary version_switch version_regexp =
  let out = Filename.temp_file "out" "" in
  let cmd = sprintf "%s %s" binary version_switch in
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
    end else
      let re = Re.Str.regexp version_regexp in
      let version =
        try
          ignore (Re.Str.search_forward re c 0);
          Re.Str.matched_group 1 c
        with Not_found ->
          Debug.dprintf debug "Warning: found prover %s but name/version not \
                               recognized by regexp `%s'@."
            binary version_regexp;
          Debug.dprintf debug "Answer was `%s'@." c;
          ""
      in
      Some { Detected_binary.exec_name; binary; version; shortcut = None }
  with Not_found | End_of_file | Sys_error _ ->
    Debug.dprintf debug "command '%s' failed@." cmd;
    None

let binaries_of_data data =
  List.fold_left (fun acc (d:Prover_autodetection_data.data) ->
      List.fold_left (fun acc exec_name ->
          Mstr.add exec_name (d.version_switch,d.version_regexp) acc
        ) acc d.execs
    ) Mstr.empty data

let detected_of_manuals ?(detected=Mstr.empty) binaries manuals =
  List.fold_left (fun acc (x:Manual_binary.t) ->
      match Mstr.find_opt x.same_as binaries with
      | Some (switch, regexp) -> begin
          match detect_prover x.same_as x.binary switch regexp with
          | Some r ->
              let r = { r with shortcut = Some x.shortcut } in
              Mstr.add x.same_as
                (r::(Mstr.find_def [] x.same_as detected))
                detected
          | None ->
              Warning.emit "Version detection failed for manually added binary %s"
                x.binary;
              acc
        end
      | None ->
          Warning.emit "No prover %s exists for configuring the manually added binary %s "
            x.same_as x.binary;
          acc
    ) detected manuals

let request_binaries_version config datas =
  let binaries = binaries_of_data datas.Prover_autodetection_data.skeletons in
  let detected =
    Mstr.mapi_filter
      (fun exec_name (switch,regexp) ->
         let r = detect_prover exec_name exec_name switch regexp in
         Opt.map (fun x -> [x]) r)
      binaries
  in
  (** manual prover *)
  let manuals = Manual_binary.load config in
  let detected = detected_of_manuals binaries ~detected manuals in
  (** *)
  detected

let request_manual_binaries_version datas manuals =
  let binaries = binaries_of_data datas.Prover_autodetection_data.skeletons in
  let detected = detected_of_manuals binaries manuals in
  detected

let set_binaries_detected binaries config =
  let fold _ l acc = List.rev_append l acc in
  let detected = Mstr.fold fold binaries [] in
  Detected_binary.set config detected

let update_binaries_detected binaries config =
  let fold _ l acc = List.rev_append l acc in
  let detected = Mstr.fold fold binaries [] in
  List.fold_left Detected_binary.add config detected


let compute_builtin_prover detected datas =
  let env = create_env detected datas.Prover_autodetection_data.shortcuts in
  let _ = run_auto_detection' env datas.skeletons in
  ()
