open Why3

type msg =
  { expl   : Gnat_expl.expl;
    result : bool;
    improved_sloc : Gnat_loc.simple_loc option;
    time   : float;
    steps  : int;
    msg    : string;
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

let register expl task result valid =
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
    msg           = msg;
    time          = time;
    steps         = steps } in
  msg_set := msg :: !msg_set

let clear () =
  msg_set := []

let print_simple_proven fmt p =
   match Gnat_expl.get_loc p with
   | [] -> assert false (* the sloc of a VC is never empty *)
   | primary :: _ ->
         Format.fprintf fmt "%a: info: %a proved"
         Gnat_loc.simple_print_loc primary Gnat_expl.print_reason
         (Gnat_expl.get_reason p)

let improve_sloc msg =
  let sloc =
    match msg.improved_sloc with
    | None -> List.hd (Gnat_expl.get_loc msg.expl)
    | Some l -> l
  in
  sloc, msg.msg

let print_msg fmt m =
  let reason = Gnat_expl.get_reason m.expl in
  match Gnat_expl.get_loc m.expl with
  | [] -> assert false (* the sloc of a VC is never empty *)
  | _ :: secondaries ->
      if m.result then print_simple_proven fmt m.expl
      else begin
        let sloc, msg = improve_sloc m in
        Format.fprintf fmt "%a: %a not proved"
          Gnat_loc.simple_print_loc sloc Gnat_expl.print_reason
            reason;
        if msg <> "" then Format.fprintf fmt ", requires %s" msg
      end;
      List.iter
         (fun secondary_sloc ->
           Format.fprintf fmt ", in instantiation at %a"
              Gnat_loc.print_line_loc secondary_sloc) secondaries;
      if Gnat_config.show_tag then
        Format.fprintf fmt " [%s]" (Gnat_expl.tag_of_reason reason)

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
    let do_print = not msg.result || Gnat_config.report <> Gnat_config.Fail in
    if do_print then print_msg Format.std_formatter msg;
    if Gnat_config.report = Gnat_config.Statistics then
      Format.printf "(%a)" print_statistics msg;
    if do_print then Format.printf "@.";
  ) l
