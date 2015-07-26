open Why3
open Why3.Json
open Gnat_objectives.Save_VCs

type msg =
  { check         : Gnat_expl.check;
    result        : bool;
    stats         : stats option;
    extra_info    : int option;
    tracefile     : string;
    cntexmp_vc    : string;
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

let register check task model stats valid manual tracefile cntexmpfile =
  let extra_info =
    if valid then None
    else begin match task with
      | None -> None
      | Some t -> Gnat_expl.get_extra_info t
    end in
  let cntexmp_vc =
    match model with
    | None -> ""
    | Some m ->
      Model_parser.model_vc_term_to_string
	~me_name_trans:spark_counterexample_transform
	~sep:" and "
	m in
  let msg =
  { check         = check;
    result        = valid;
    extra_info    = extra_info;
    stats         = stats;
    tracefile     = tracefile;
    cntexmp_vc    = cntexmp_vc;
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

let print_cntexmp_vc fmt cnt_vc =
  if cnt_vc = "" then ()
  else begin
    Format.fprintf fmt ", ";
    print_json_field "cntexmp_vc" string fmt cnt_vc
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

let print_prover_stats fmt stat =
  Format.fprintf fmt "{ %a, %a, %a }"
   (print_json_field "count" int) stat.count
   (print_json_field "max_steps" int) stat.max_steps
   (print_json_field "max_time" float) stat.max_time

let print_stats fmt stats =
  match stats with
  | None -> ()
  | Some s ->
      let kv_list = Whyconf.Hprover.fold (fun k v acc -> (k,v)::acc) s [] in
      let get_name pr = pr.Whyconf.prover_name in
      Format.fprintf fmt ", ";
      print_json_field "stats"
      (map_bindings get_name print_prover_stats) fmt kv_list

let print_json_msg fmt m =
  Format.fprintf fmt "{%a, %a, %a, %a%a%a%a%a%a}"
    (print_json_field "id" int) m.check.Gnat_expl.id
    (print_json_field "reason" string)
      (Gnat_expl.reason_to_ada m.check.Gnat_expl.reason)
    (print_json_field "result" bool) m.result
    (print_json_field "extra_info" int) (get_info m.extra_info)
    print_stats m.stats
    print_trace_file m.tracefile
    print_cntexmp_vc m.cntexmp_vc
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
