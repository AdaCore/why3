open Why3
open Why3.Json

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

let register check task result valid manual tracefile cntexmpfile =
  let time =
    match result with
    | None -> 0.0
    | Some r -> r.Call_provers.pr_time in
  let steps = match result with
    | Some r ->
      r.Call_provers.pr_steps
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
