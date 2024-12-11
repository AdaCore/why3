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
                   versions_ok = reg_map (get_stringl section "version_ok");
                   versions_old = reg_map (get_stringl section "version_old");
                   versions_bad = reg_map (get_stringl section "version_bad");
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

  let from_file filename =
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

  let read_auto_detection_data main =
    let filename = Filename.concat (Whyconf.datadir main)
        "provers-detection-data.conf" in
    from_file filename



end

module Partial = struct

  type t = {
    name : string;
    path : string;
    version : string;
    shortcut : string option;
    manual : bool;
  }

  let section_name = "partial_prover"

  let load_one section =
    try
      let name = get_string section "name" in
      let path = get_string section "path" in
      let version = get_string section "version" in
      let shortcut = get_stringo section "shortcut" in
      let manual = get_bool ~default:false section "manual" in
      Some { name; path; version; shortcut; manual }
    with MissingField s ->
      Loc.warning warn_missing_field "cannot load a %s section: missing field '%s'@." section_name s;
      None

  let load_rc rc =
    List.filter_map load_one (get_simple_family rc section_name)

  let load rc =
    List.filter_map load_one (Whyconf.User.get_simple_family rc section_name)

  let set_one prover =
    let section = empty_section in
    let section = set_bool section "manual" prover.manual ~default:false in
    let section = set_stringo section "shortcut" prover.shortcut in
    let section = set_string section "version" prover.version in
    let section = set_string section "path" prover.path in
    let section = set_string section "name" prover.name in
    section

  let set config detected_provers =
    let family = List.map set_one detected_provers in
    Whyconf.User.set_simple_family config section_name family

  let add rc m =
    let l =
      List.fold_right (fun x acc ->
          let x =
            if x.shortcut = m.shortcut then { x with shortcut = None }
            else x in
          x :: acc
        ) (load rc) [m] in
    set rc l

    let remove_auto rc =
      let l = List.filter (fun x -> x.manual) (load rc) in
      set rc l

end

type unknown_version = {
  data:Prover_autodetection_data.data;
  priority:int;
  shortcut:string;
  prover_config:config_prover;
}

type env =
  {
    binaries: Partial.t list;
    (* prover_unknown_version:
       path -> Some (altern -> unknown_version): neither good or bad version
             | None: there is already a good version *)
    prover_unknown_version : (unknown_version Hstr.t) option Hstr.t;
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
      | "e" -> Filename.quote exec
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

let known_version env path =
  Hstr.replace env.prover_unknown_version path None

let unknown_version env path shortcut prover_config (data:Prover_autodetection_data.data) priority =
  let altern = data.prover_altern in
  match Hstr.find_opt env.prover_unknown_version path with
  | None ->
      let h = Hstr.create 5 in
      Hstr.add h altern {data; priority; shortcut; prover_config};
      Hstr.add env.prover_unknown_version path (Some h)
  | Some None ->
      ()
  | Some (Some h) ->
      if not (Hstr.mem h altern) then
        Hstr.add h altern {data; priority; shortcut; prover_config}

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
  List.iter (fun s -> fprintf str_formatter "c %s 1. 1000@\n" s) provers_level1;
  let code = flush_str_formatter () in
  let auto0 = {
      strategy_name = "Auto_level_0";
      strategy_desc = "Automatic@ run@ of@ main@ provers";
      strategy_shortcut = "0";
      strategy_code = code }
  in
  let alt fmt () = fprintf fmt " | " in
  if provers_level1 <> [] then
    begin
      fprintf str_formatter "c %a@\n"
        (Pp.print_list alt (fun fmt s -> fprintf fmt "%s 5. 1000" s)) provers_level1;
    end;
  let code = flush_str_formatter () in
  let auto1 = {
      strategy_name = "Auto_level_1";
      strategy_desc = "Automatic@ run@ of@ main@ provers for longer times";
      strategy_shortcut = "1";
      strategy_code = code }
  in
  fprintf str_formatter "start:@\n";
  List.iter (fun s -> fprintf str_formatter "c %s 1. 1000@\n" s) provers_level1;
  fprintf str_formatter "t split_vc start@\n";
  if provers_level1 <> [] then
    begin
      fprintf str_formatter "c %a@\n"
        (Pp.print_list alt (fun fmt s -> fprintf fmt "%s 10. 4000" s)) provers_level1;
    end;
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
  List.iter (fun s -> fprintf str_formatter "c %s 1. 1000@\n" s) provers_level3;
  fprintf str_formatter "t split_vc start@\n";
  if provers_level1 <> [] then
    begin
      fprintf str_formatter "c %a@\n"
        (Pp.print_list alt (fun fmt s -> fprintf fmt "%s 5. 2000" s)) provers_level1;
    end;
  fprintf str_formatter "t introduce_premises afterintro@\n";
  fprintf str_formatter "afterintro:@\n";
  fprintf str_formatter "t inline_goal afterinline@\n";
  fprintf str_formatter "g trylongertime@\n";
  fprintf str_formatter "afterinline:@\n";
  fprintf str_formatter "t split_all_full start@\n";
  fprintf str_formatter "trylongertime:@\n";
  if provers_level1 <> [] then
    begin
      fprintf str_formatter "c %a@\n"
        (Pp.print_list alt (fun fmt s -> fprintf fmt "%s 30. 4000" s)) provers_level1;
    end;
  let code = flush_str_formatter () in
  let auto3 = {
      strategy_name = "Auto_level_3";
      strategy_desc = "Automatic@ run@ of@ provers@ and@ most@ useful@ transformations";
      strategy_shortcut = "3";
      strategy_code = code }
  in
  [split ; auto0 ; auto1 ; auto2 ; auto3]

let check_support_library main (data:Prover_autodetection_data.data) ver =
  let cmd_regexp = Re.Str.regexp "%\\(.\\)" in
  let replace s = match Re.Str.matched_group 1 s with
    | "l" -> Whyconf.libdir main
    | "d" -> Whyconf.datadir main
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

let expand_aux env provers prover prover_config shortcut priority (data:Prover_autodetection_data.data) =
  add_prover_shortcuts env prover;
  add_id_prover_shortcut env shortcut prover priority;
  let level = data.use_at_auto_level in
  if level > 0 then record_prover_for_auto_mode env prover level;
  Mprover.add prover { prover_config with prover } provers

let expand_partial env main (data:Prover_autodetection_data.data) provers (p:Partial.t) =
  let binary = p.path in
  (* bad here means not good, it is not the same thing as a version
     of a prover with known problems *)
  let bad = List.exists (check_version p.version) data.versions_bad in
  if bad then begin
    known_version env binary;
    provers
  end else
    let good = List.exists (check_version p.version) data.versions_ok in
    let old  = List.exists (check_version p.version) data.versions_old in
    let pp_shortcut fmt = Option.iter (Format.fprintf fmt (" (manually added as %s)")) p.shortcut in
    match data.prover_command with
    | None ->
        (* an empty prover command is used for forbidding some versions:
           a matching version means known problems *)
        if not (good || old) then begin
          provers
        end else begin
          print_info "Found prover %s%t version %s%s@."
            data.prover_name
            pp_shortcut
            p.version
            (Option.value ~default:
               ". This version of the prover is known to have problems."
               data.message);
          known_version env binary;
          provers
        end
    | Some prover_command ->
        (* create the prover config *)
        let c = make_command binary prover_command in
        let c_steps = Option.map (make_command binary) data.prover_command_steps in
        let prover =
          { Wc.prover_name = data.prover_name;
            prover_version = p.version;
            prover_altern = data.prover_altern } in
        let prover_config =
          { prover = prover;
            command = c;
            command_steps = c_steps;
            driver = (None, data.prover_driver);
            editor = data.prover_editor;
            in_place = data.prover_in_place;
            interactive = (match data.kind with ITP -> true | ATP -> false);
            extra_options = [];
            extra_drivers = [];
          } in
        let shortcut = Option.value ~default:data.prover_id p.shortcut in
        if not (good || old) then begin
          (* Unknown, temporarily put the prover away *)
          let priority = next_priority () in
          unknown_version env binary shortcut prover_config data priority;
          provers
        end
        else if data.support_library <> ""
                && not (check_support_library main data p.version) then begin
          (* The prover needs compile-time support and it is not available *)
          known_version env binary;
          provers
        end else
          (* The prover can be added with a uniq id *)
          let prover = find_prover_altern provers prover in
          let priority = next_priority () in
          print_info "Found prover %s%t version %s%s@."
            data.prover_name pp_shortcut p.version
            (Option.value ~default:
               (if old then
                  " (old version, please consider upgrading)."
                else
                if data.prover_altern <> "" then
                  " (alternative: " ^ data.prover_altern ^ ")"
                else
                  ", OK.")
               data.message);
          known_version env binary;
          expand_aux env provers prover prover_config shortcut priority data

let expand_partial env main acc (data:Prover_autodetection_data.data) =
  List.fold_left (fun acc p ->
      if p.Partial.name = data.prover_name ||
           List.mem p.Partial.name data.execs then
        expand_partial env main data acc p
      else acc
    ) acc env.binaries

let pp_versions =
  Pp.print_list Pp.comma
                (Pp.print_pair_delim Pp.nothing Pp.nothing Pp.nothing Pp.string Pp.nothing)

let expand_unknown env main provers uv =
  let ver = uv.prover_config.prover.prover_version in
  if uv.data.support_library <> ""
     && not (check_support_library main uv.data ver) then begin
    (* The prover needs compile-time support and it is not available *)
    provers
  end else begin
    let prover = find_prover_altern provers uv.prover_config.prover in
    print_info
      "@[<v 2>@[Prover %s%t version %s is not recognized.@]@,\
       @[Known versions for this prover:@ %a.@]%t@]@."
      prover.Wc.prover_name
      (fun fmt ->
        if prover.prover_altern <> "" then
          Format.fprintf fmt " (alternative: %s)" prover.prover_altern)
      ver
      pp_versions uv.data.versions_ok
      (fun fmt ->
        if uv.data.versions_old <> [] then
          Format.fprintf fmt "@,@[Known old versions for this prover:@ %a.@]"
            pp_versions uv.data.versions_old);
    expand_aux env provers prover uv.prover_config uv.shortcut uv.priority uv.data
  end

let detect_unknown env main detected =
  Hstr.fold (fun _ pc acc ->
      match pc with
      | None ->
          (* The prover version appeared in some section *)
          acc
      | Some uv ->
          (* The version never appeared in any section,
             so we take the first not bad section per alternative *)
          Hstr.fold (fun _ uv acc -> expand_unknown env main acc uv) uv acc
    ) env.prover_unknown_version detected

let convert_shortcuts env =
  Hstr.fold (fun s (_,p) acc ->
    check_prover_auto_level env p; Mstr.add s p acc
  ) env.prover_shortcuts Mstr.empty

let run_auto_detection env main skeletons =
  let detected =
    List.fold_left (expand_partial env main) Mprover.empty skeletons
  in
  let length_recognized = Mprover.cardinal detected in
  let detected = detect_unknown env main detected in
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
  let config = add_provers config detected shortcuts in
  config

let read_auto_detection_data config =
  let main = get_main config in
  Prover_autodetection_data.read_auto_detection_data main

let () =
  let provers_from_detected_provers config rc =
    let binaries = Partial.load_rc rc in
    let datas = read_auto_detection_data config in
    let env = create_env binaries datas.shortcuts in
    let main = Whyconf.get_main config in
    let detected = run_auto_detection env main datas.skeletons in
    generate_builtin_config env datas detected config
  in
  Whyconf.provers_from_detected_provers :=
    provers_from_detected_provers

let list_binaries () =
  let config = default_config "" in
  let datas = read_auto_detection_data config in
  let s = List.fold_left (fun s p ->
      Sstr.add p.Prover_autodetection_data.prover_name s)
      Sstr.empty datas.skeletons
  in
  Sstr.elements s

let query_prover_version path version_switch version_regexp =
  let out = Filename.temp_file "out" "" in
  let cmd = sprintf "%s %s" (Filename.quote path) version_switch in
  let c = sprintf "(%s) > %s 2>&1" cmd (Filename.quote out) in
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
            path version_regexp;
          Debug.dprintf debug "Answer was `%s'@." c;
          ""
      in
      Some version
  with Not_found | End_of_file | Sys_error _ ->
    Debug.dprintf debug "command '%s' failed@." cmd;
    None

let locate_exe =
  let binaries = lazy (
    let binaries = Hstr.create 17 in
    let paths = try Sys.getenv "PATH" with Not_found -> "/usr/bin" in
    let sep = if Sys.win32 then ';' else ':' in
    let paths = String.split_on_char sep paths in
    List.iter (fun path ->
        if path <> "" then
          match Sys.readdir path with
          | files ->
              Array.iter (fun f ->
                  if not (Hstr.mem binaries f) then
                    Hstr.add binaries f (Filename.concat path f)
                ) files
          | exception _ -> ()
      ) paths;
    binaries) in
  fun name ->
  let ln = String.length name in
  Hstr.fold (fun p fullpath acc ->
      let lp = String.length p in
      if lp >= ln &&
         Strings.has_prefix name p &&
         (lp = ln ||
            (p.[ln] = '.' && lp = ln + 4 && Strings.(has_suffix "exe" p || has_suffix "bat" p)) ||
            (p.[ln] = '-' && lp >= ln + 2 && '0' <= p.[ln + 1] && p.[ln + 1] <= '9')) then
        fullpath :: acc
      else acc) (Lazy.force binaries) []

let find_prover data name path =
  let binaries = Hashtbl.create 10 in
  List.iter (fun (d:Prover_autodetection_data.data) ->
      if name = d.prover_name || List.mem name d.execs then
        Hashtbl.replace binaries (d.version_switch, d.version_regexp) ()
    ) data.Prover_autodetection_data.skeletons;
  Hashtbl.fold
    (fun (switch, regexp) () acc ->
      if Option.is_some acc then acc
      else query_prover_version path switch regexp
    ) binaries None

let find_provers data =
  let binaries = Hashtbl.create 10 in
  List.iter (fun (d:Prover_autodetection_data.data) ->
      List.iter (fun exec_name ->
          Hashtbl.replace binaries (exec_name, d.version_switch, d.version_regexp) d.prover_name
        ) d.execs
    ) data.Prover_autodetection_data.skeletons;
  let provers =
    Hashtbl.fold (fun (exec_name, switch, regexp) name acc ->
        let binaries = locate_exe exec_name in
        List.fold_left (fun acc exec_name ->
            if Mstr.mem exec_name acc then acc
            else
              let r = query_prover_version exec_name switch regexp in
              Opt.fold (fun acc x -> Mstr.add exec_name (name, x) acc) acc r
          ) acc binaries
      ) binaries Mstr.empty in
  let provers = Mstr.bindings provers in
  let provers = List.map (fun (path, (name, version)) -> (path, name, version)) provers in
  List.sort (fun (_, n1, v1) (_, n2, v2) ->
      let c = String.compare n1 n2 in
      if c <> 0 then c else
      Stdlib.compare (Util.split_version v2) (Util.split_version v1)
    ) provers

let remove_auto_provers config =
  Partial.remove_auto config

let update_provers binaries config =
  List.fold_left Partial.add config binaries

let compute_builtin_prover binaries config datas =
  let env = create_env binaries datas.Prover_autodetection_data.shortcuts in
  let main = Whyconf.get_main config in
  run_auto_detection env main datas.skeletons
