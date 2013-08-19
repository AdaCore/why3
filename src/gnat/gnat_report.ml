open Why3

type msg =
  { expl   : Gnat_expl.expl;
    result : bool;
    improved_sloc : Gnat_loc.simple_loc option;
    time   : float;
    steps  : int;
    extra_msg : string;
    tracefile : string;
  }

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

let register expl task result valid tracefile =
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
    tracefile     = tracefile } in
  msg_set := msg :: !msg_set

let clear () =
  msg_set := []

let print_msg fmt m =
  if m.result then Format.fprintf fmt "info: ";
  Format.fprintf fmt "%a" Gnat_expl.print_reason (Gnat_expl.get_reason m.expl);
  if m.result then Format.fprintf fmt " proved"
  else Format.fprintf fmt " not proved";
  if m.extra_msg <> "" then Format.fprintf fmt ", requires %s" m.extra_msg

let improve_sloc msg =
  match msg.improved_sloc with
  | None -> List.hd (Gnat_expl.get_loc msg.expl)
  | Some l -> l

let print_with_sloc_and_tag fmt m =
  let reason = Gnat_expl.get_reason m.expl in
  match Gnat_expl.get_loc m.expl with
  | [] -> assert false (* the sloc of a VC is never empty *)
  | _ :: secondaries ->
      let sloc = improve_sloc m in
      Format.fprintf fmt "%a: %a" Gnat_loc.simple_print_loc sloc print_msg m;
      List.iter
         (fun secondary_sloc ->
           Format.fprintf fmt ", in instantiation at %a"
              Gnat_loc.print_line_loc secondary_sloc) secondaries;
      if Gnat_config.show_tag then
        Format.fprintf fmt " [%s]" (Gnat_expl.tag_of_reason reason)

let print_json_entity fmt e =
  let sl = List.hd e.Gnat_expl.subp_loc in
  let file, line, _ = Gnat_loc.explode sl in
  Format.fprintf fmt "{\"name\":\"%s\",\"file\":\"%s\",\"line\":%d}"
  e.Gnat_expl.subp_name file line

let print_json_msg fmt m =
  let e = m.expl in
  (* ??? what about more complex slocs *)
  let loc = List.hd (Gnat_expl.get_loc e) in
  let file, line, col = Gnat_loc.explode loc in
  let ent = Gnat_expl.get_subp_entity e in
  let msg = Pp.sprintf "%a" print_msg m in
  let severity = if m.result then "info" else "error" in
  let rule = Gnat_expl.tag_of_reason (Gnat_expl.get_reason e) in
  (* ??? Trace file *)
  Format.fprintf fmt
     "{\"file\":\"%s\",\"line\":%d,\"col\":%d,\"message\":\"%s\",\
       \"rule\":\"%s\",\"severity\":\"%s\",\"tracefile\":\"%s\",\
       \"entity\":%a}@."
    file line col msg rule severity m.tracefile print_json_entity ent

let print_statistics fmt msg =
  if msg.steps <> 0 && msg.time <> 0.0 then
    Format.fprintf fmt "%.2fs - %d steps" msg.time msg.steps
  else if msg.steps <> 0 then
    Format.fprintf fmt "%d steps" msg.steps
  else if msg.time <> 0.0 then
    Format.fprintf fmt "%.2fs" msg.time

let print_messages_and_clear () =
  let l = List.sort cmp !msg_set in
  clear ();
  List.iter (fun msg ->
    if not msg.result || Gnat_config.report <> Gnat_config.Fail then begin
      (* we only print the message if asked for *)
      if Gnat_config.ide_progress_bar then begin
        (* special output in IDE mode *)
        print_json_msg Format.std_formatter msg
      end else begin
        print_with_sloc_and_tag Format.std_formatter msg;
        if Gnat_config.report = Gnat_config.Statistics then
          Format.printf "(%a)" print_statistics msg;
        Format.printf "@.";
      end
    end
  ) l
