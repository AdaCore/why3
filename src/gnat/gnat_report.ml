open Why3
open Gnat_json

type msg =
  { check         : Gnat_expl.check;
    result        : bool;
    time          : float;
    steps         : int;
    extra_info    : int option;
    tracefile     : string;
    cntexmpfile   : string;
    manual_proof  : (string * string) option
  }

let msg_set : msg list ref = ref []

let warning_list : string list ref = ref []

let add_warning ?loc s =
  let s =
    match loc with
    | Some loc ->
        let file, line, col1, col2 = Loc.get loc in
        Format.sprintf "%s:%d:%d-%d: %s" file line col1 col2 s
    | None -> s
  in
  warning_list := s :: !warning_list

let () = Warning.set_hook add_warning

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

let register check task result valid manual tracefile cntexmpfile =
  let time =
    match result with
    | None -> 0.0
    | Some r -> r.Call_provers.pr_time in
  let steps =
    match result with
    | Some ({Call_provers.pr_answer = Call_provers.Valid } as r) ->
        begin match extract_steps r.Call_provers.pr_output with
        | Some steps -> steps
        | None -> 0
        end
    | Some { Call_provers.pr_answer = Call_provers.Failure s } ->
        begin match extract_steps_fail s with
        | Some steps -> steps
        | None -> 0
        end
    | _ -> 0 in
  let extra_info =
    if valid then None
    else begin match task with
      | None -> None
      | Some t -> Gnat_expl.get_extra_info t
    end in
  let msg =
  { check         = check;
    result        = valid;
    extra_info    = extra_info;
    time          = time;
    steps         = steps;
    tracefile     = tracefile;
    cntexmpfile   = cntexmpfile;
    manual_proof  = manual } in
  msg_set := msg :: !msg_set

let get_info info  =
    match info with
    | None -> 0
    | Some info -> info

let print_trace_file fmt trace  =
  if trace = "" then ()
  else begin
    Format.fprintf fmt ", ";
    print_json_field "tracefile" string fmt trace
  end

let print_cntexmp_file fmt cnt  =
  if cnt = "" then ()
  else begin
    Format.fprintf fmt ", ";
    print_json_field "cntexmpfile" string fmt cnt
  end

let print_manual_proof_info fmt info =
  match info with
  | None -> ()
  | Some (fname, cmd) ->
     Format.fprintf fmt ", %a, %a"
     (print_json_field "vc_file" string)
                   (Sys.getcwd () ^ Filename.dir_sep ^ fname)
     (print_json_field "editor_cmd" string) cmd

let print_json_msg fmt m =
  Format.fprintf fmt "{%a, %a, %a, %a%a%a%a}"
    (print_json_field "id" int) m.check.Gnat_expl.id
    (print_json_field "reason" string)
      (Gnat_expl.reason_to_ada m.check.Gnat_expl.reason)
    (print_json_field "result" bool) m.result
    (print_json_field "extra_info" int) (get_info m.extra_info)
    print_trace_file m.tracefile
    print_cntexmp_file m.cntexmpfile
    print_manual_proof_info m.manual_proof

let print_warning_list fmt l =
  match l with
  | [] -> ()
  | l -> 
    Format.fprintf fmt ", %a" (print_json_field "warnings" (list string)) l

let print_messages () =
  Format.printf "{%a%a}@."
  (print_json_field "results" (list print_json_msg)) !msg_set
  print_warning_list !warning_list
