open Why3
open Why3.Json_base

type prover_stat =
  {
    mutable count     : int;
    mutable max_time  : float;
    mutable max_steps : int;
  }

type stats = prover_stat Whyconf.Hprover.t

type result_info =
  | Proved of stats * int
  | Not_Proved of
       Task.task option *
       Model_parser.model option *
       string *
       (string * string) option

type msg =
  { result        : bool;
    stats         : stats option;
    stats_tr      : int;
    check_tree    : Json_base.json;
    extra_info    : int option;
    tracefile     : string;
    cntexmp_model : Model_parser.model option;
    manual_proof  : (string * string) option
  }

let msg_set : msg Gnat_expl.HCheck.t = Gnat_expl.HCheck.create 17

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

let adapt_stats statsopt =
  match statsopt with
  | None -> None
  | Some stats ->
      let newstats = Whyconf.Hprover.create 3 in
      Whyconf.Hprover.iter (fun k v ->
        let name = k.Whyconf.prover_name in
        Whyconf.Hprover.add newstats k {v with max_steps =
          Gnat_config.back_convert_steps ~prover:name v.max_steps}) stats;
      Some newstats

let register check check_tree result =
  let valid, extra_info, stats, tracefile, model, manual =
    match result with
    | Proved (stats, stats_tr) -> true, None, Some (stats, stats_tr), "", None, None
    | Not_Proved (task, model, tracefile, manual) ->
        let extra_info =
          match task with
          | None -> None
          | Some t -> Gnat_expl.get_extra_info t in
        false, extra_info, None, tracefile, model, manual
  in
  if (Gnat_expl.HCheck.mem msg_set check) then assert false
  else begin
    let msg =
    { result        = valid;
      extra_info    = extra_info;
      stats         = adapt_stats (Opt.map fst stats);
      stats_tr      = Opt.get_def 0 (Opt.map snd stats);
      check_tree    = check_tree;
      tracefile     = tracefile;
      cntexmp_model = model;
      manual_proof  = manual } in
    Gnat_expl.HCheck.add msg_set check msg
  end

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

let spark_counterexample_transform me_name =
  (* Just return the name of the model element. Transformation of model
     element names to SPARK syntax is now handled in gnat2why.
     See Flow_Error_Messages.Error_Msg_Proof.Do_Pretty_Cntexmp*)
  me_name.Model_parser.men_name

let print_cntexmp_model fmt model =
  match model with
  | None -> ()
  | Some m ->
    if not (Model_parser.is_model_empty m) then begin
      Format.fprintf fmt ", ";
      print_json_field "cntexmp"
        (Model_parser.print_model_json
           ~me_name_trans:spark_counterexample_transform
           ~vc_line_trans:(fun _ -> "vc_line"))
        fmt
        m
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
   (print_json_field "max_time" standard_float) stat.max_time

let print_stats fmt (stats, stat_tr) =
  (* Print the stats for goal solved by transformations as a fake prover. *)
  let fake_prover_tr =
    Whyconf.{prover_name = "Checker"; prover_version = ""; prover_altern = ""}
  in
  match stats with
  | None -> ()
  | Some s ->
    if stat_tr <> 0 then
      Whyconf.Hprover.add s fake_prover_tr {count = stat_tr; max_steps = 0; max_time = 0.0};
    let kv_list = Whyconf.Hprover.fold (fun k v acc -> (k,v)::acc) s [] in
    let get_name pr = pr.Whyconf.prover_name in
    Format.fprintf fmt ", ";
    print_json_field "stats"
      (map_bindings get_name print_prover_stats) fmt kv_list

let sort_messages (l : (Gnat_expl.check * msg) list) =
  List.sort (fun x y -> compare (fst x).Gnat_expl.id (fst y).Gnat_expl.id) l

let print_json_msg fmt (check, m) =
  Format.fprintf fmt "{%a, %a, %a, %a, %a%a%a%a%a}"
    (print_json_field "id" int) check.Gnat_expl.id
    (print_json_field "reason" string)
      (Gnat_expl.reason_to_ada check.Gnat_expl.reason)
    (print_json_field "result" bool) m.result
    (print_json_field "extra_info" int) (get_info m.extra_info)
    (print_json_field "check_tree" Json_base.print_json) m.check_tree
    print_stats (m.stats, m.stats_tr)
    print_trace_file m.tracefile
    print_cntexmp_model m.cntexmp_model
    print_manual_proof_info m.manual_proof

let print_warning_list fmt l =
  match l with
  | [] -> ()
  | l ->
    Format.fprintf fmt ", %a" (print_json_field "warnings" (list string)) l

let print_timing_entry fmt t =
  (* Timing data is only printed when --debug switch is active *)
  if Gnat_config.debug then
    let l = Hashtbl.fold (fun k v acc -> (k,v)::acc) t [] in
    let get_name s = s in
    Format.fprintf fmt ", ";
    print_json_field "timings" (map_bindings get_name standard_float) fmt l
  else ()

let print_messages () =
  let msg_set = Gnat_expl.HCheck.fold (fun k v acc -> (k,v) :: acc) msg_set []
  in
  Format.printf "{%a%a%a}@."
  (print_json_field "results" (list print_json_msg)) (sort_messages msg_set)
  print_warning_list !warning_list
  print_timing_entry (Util.get_timings ())
