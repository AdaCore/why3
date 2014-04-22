open Why3

type msg =
  { expl   : Gnat_expl.expl;
    result : bool;
    improved_sloc : Gnat_loc.simple_loc option;
    time   : float;
    steps  : int;
    extra_msg : string;
    tracefile : string;
    vc_file : string option;
  }

type status =
  | Everything_Proved
  | Unproved_Checks

let cmp msg1 msg2 = Gnat_expl.expl_compare msg1.expl msg2.expl

let msg_set : msg list ref = ref []

let is_digit c =
  match c with
  | '0' .. '9' -> true
  | _ -> false

let extract_steps s =
  (* extract steps from alt-ergo "valid" output; return None if output is not
     recognized, or no steps information present *)
  (* We simply search for (xxx) at the end of the first line of the  output,
     where all the xxx must be digits. *)
  let s =
    try Strings.slice s 0 (String.index s '\n' )
    with Not_found -> s
  in
  try
    let len = String.length s in
    if len = 0 then None
    else
      let i = ref (len - 1) in
      (* skip spaces *)
      while s.[!i] = ' ' do
        i := !i - 1;
      done;
      if s.[!i] = ')' then begin
        let max = !i in
        while !i > 0 && is_digit s.[!i-1] do
          i := !i - 1;
        done;
        if !i > 0 && s.[!i-1] = '(' then
          let s = Strings.slice s !i max in
          Some (int_of_string s)
        else None
      end else None
  with _ -> None

let extract_steps_fail s =
  if Strings.starts_with s "steps:" then
    try Some (int_of_string (Strings.slice s 6 (String.length s)))
    with _ -> None
  else None

let register expl task result valid ?filename tracefile =
  let time =
    match result with
    | None -> 0.0
    | Some r -> r.Call_provers.pr_time in
  let steps =
    if Gnat_config.report = Gnat_config.Statistics && result <> None then
      let result = Opt.get result in
      match result.Call_provers.pr_answer with
      | Call_provers.Valid ->
          begin match extract_steps result.Call_provers.pr_output with
          | Some steps -> steps
          | None -> 0
          end
      | Call_provers.Failure s ->
          begin match extract_steps_fail s with
          | Some steps -> steps
          | None -> 0
          end
      | _ -> 0
    else 0
  in
  let improved_sloc, msg =
    if valid then None, ""
    else if task = None then None, ""
    else
      let task = Opt.get task in
      let first_sloc = List.hd (Gnat_expl.get_loc expl) in
      let sloc, msg = Gnat_expl.improve_sloc first_sloc task in
      Some sloc, msg in
  let msg =
  { expl          = expl;
    result        = valid;
    improved_sloc = improved_sloc;
    extra_msg     = msg;
    time          = time;
    steps         = steps;
    tracefile     = tracefile;
    vc_file       = filename } in
  msg_set := msg :: !msg_set

let print_msg fmt m =
  if m.result then Format.fprintf fmt "info: " else Format.fprintf fmt "warning: ";
  Format.fprintf fmt "%a" (Gnat_expl.print_reason ~proved:m.result)
    (Gnat_expl.get_reason m.expl);
  (if m.extra_msg <> "" then Format.fprintf fmt ", requires %s" m.extra_msg);
  match m.vc_file with
  | None -> ()
  | Some fn -> Format.fprintf fmt ", VC file: %s" fn

let improve_sloc msg =
  match msg.improved_sloc with
  | None -> List.hd (Gnat_expl.get_loc msg.expl)
  | Some l -> l

let print_with_sloc fmt m =
  match Gnat_expl.get_loc m.expl with
  | [] -> assert false (* the sloc of a VC is never empty *)
  | _ :: secondaries ->
      let sloc = improve_sloc m in
      Format.fprintf fmt "%a: %a" Gnat_loc.simple_print_loc sloc print_msg m;
      List.iter (Gnat_loc.print_line_loc fmt) secondaries

let print_json_entity fmt e =
  let sl = List.hd e.Gnat_expl.subp_loc in
  let file, line, _ = Gnat_loc.explode sl in
  Format.fprintf fmt "{\"name\":\"%s\",\"file\":\"%s\",\"line\":%d}"
  e.Gnat_expl.subp_name file line

let json_escape_msg =
  let b = Buffer.create 150 in
  fun s ->
    Buffer.reset b;
    for i = 0 to String.length s - 1 do
      if s.[i] = '"' then Buffer.add_char b '\\';
      Buffer.add_char b s.[i];
    done;
    Buffer.contents b

(* The function replaces %{f,t,T,m,l,d} to their corresponding values
   in the string cmd.
   This function is based on the Call_provers.actualcommand, for
   some reason not in the Why3 API nor really convenient *)
let actual_editor_cmd ?main filename cmd =
  let m = match main with
    | None -> Whyconf.get_main Gnat_config.config
    | Some m -> m in
  let replace_func s =
    match (Str.matched_string s).[1] with
    | '%' -> "%"
    | 'f' -> filename
    (* Can %t and %T be on an editor command line and have a meaning?
       Is it allowed by Why3config? *)
    | 't' -> string_of_int (Whyconf.timelimit m)
    | 'T' -> string_of_int (succ (Whyconf.timelimit m))
    | 'm' -> string_of_int (Whyconf.memlimit m)
    | 'l' -> Whyconf.libdir m
    | 'd' -> Whyconf.datadir m
    | a ->  Char.escaped a in
  Str.global_substitute (Str.regexp "%.") replace_func cmd

let print_json_msg fmt m =
  let e = m.expl in
  (* ??? what about more complex slocs *)
  let loc = List.hd (Gnat_expl.get_loc e) in
  let file, line, col = Gnat_loc.explode loc in
  let ent = Gnat_expl.get_subp_entity e in
  let msg = Pp.sprintf "%a" print_msg m in
  let msg = json_escape_msg msg in
  let severity = if m.result then "info" else "error" in
  let rule = Gnat_expl.tag_of_reason (Gnat_expl.get_reason e) in
  (* ??? Trace file *)
  Format.fprintf fmt
     "{\"file\":\"%s\",\"line\":%d,\"col\":%d,\"message\":\"%s\",\
       \"rule\":\"%s\",\"severity\":\"%s\",\"tracefile\":\"%s\","
     file line col msg rule severity m.tracefile;
  (match m.vc_file with
  | None -> ()
  | Some name ->
     Format.fprintf fmt "\"vc_file\":\"%s\","
                    (Sys.getcwd () ^ Filename.dir_sep ^ name);
     let editor = Gnat_config.prover_editor () in
     let cmd_line =
       List.fold_left (fun str s -> str ^ " " ^ s) editor.Whyconf.editor_command
                      editor.Whyconf.editor_options in
     Format.fprintf fmt "\"editor_cmd\":\"%s\","
                    (actual_editor_cmd name cmd_line));
     Format.fprintf fmt "\"entity\":%a}@."
                    print_json_entity ent

let print_statistics fmt msg =
  if msg.steps <> 0 && msg.time <> 0.0 then
    Format.fprintf fmt "%.2fs - %d steps" msg.time msg.steps
  else if msg.steps <> 0 then
    Format.fprintf fmt "%d steps" msg.steps
  else if msg.time <> 0.0 then
    Format.fprintf fmt "%.2fs" msg.time

let write_proof_result_file l =
  Pp.print_in_file (fun fmt ->
    Format.fprintf fmt "[@.";
    begin match l with
    | [] -> ()
    | x :: xs ->
        print_json_msg fmt x;
        List.iter (fun m -> Format.fprintf fmt ",%a" print_json_msg m) xs
    end;
    Format.fprintf fmt "]@."
    ) (Gnat_config.unit_name ^ ".proof")

let write_proof_result_file msg =
  write_proof_result_file msg

let print_messages () =
  let l = List.sort cmp !msg_set in
  write_proof_result_file l;
  let success = ref Everything_Proved in
  List.iter (fun msg ->
    if not msg.result then success := Unproved_Checks;
    if not msg.result || Gnat_config.report <> Gnat_config.Fail then begin
      (* we only print the message if asked for *)
      if Gnat_config.ide_progress_bar then begin
        (* special output in IDE mode *)
        print_json_msg Format.std_formatter msg
      end else begin
        print_with_sloc Format.std_formatter msg;
        if Gnat_config.report = Gnat_config.Statistics then
          Format.printf "(%a)" print_statistics msg;
        Format.printf "@.";
      end
    end
  ) l;
  !success
