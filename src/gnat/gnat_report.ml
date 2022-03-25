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
       Gnat_expl.extra_info *
       (Model_parser.model * Check_ce.rac_result option) option *
       (string * string) option

type msg =
  { result        : bool;
    stats         : stats option;
    stats_checker : int;
    check_tree    : Json_base.json;
    extra_info    : Gnat_expl.extra_info;
    cntexmp_model : (Model_parser.model * Check_ce.rac_result option) option;
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
  let valid, extra_info, stats, model, manual =
    match result with
    | Proved (stats, stats_checker) ->
        true,
        {Gnat_expl.pretty_node = None; inlined = None},
        Some (stats, stats_checker),
        None,
        None
    | Not_Proved (extra_info, model, manual) ->
        false, extra_info, None, model, manual
  in
  if (Gnat_expl.HCheck.mem msg_set check) then assert false
  else begin
    let stats_g = Opt.map (fun x -> let (stats, _) = x in stats) stats in
    let stats_checker = Opt.map (fun x -> let (_, sc) = x in sc) stats in
    let msg =
    { result        = valid;
      extra_info    = extra_info;
      stats         = adapt_stats stats_g;
      stats_checker = Opt.get_def 0 stats_checker;
      check_tree    = check_tree;
      cntexmp_model = model;
      manual_proof  = manual } in
    Gnat_expl.HCheck.add msg_set check msg
  end

let spark_counterexample_transform me_name =
  (* Just return the name of the model element. Transformation of model
     element names to SPARK syntax is now handled in gnat2why.
     See Flow_Error_Messages.Error_Msg_Proof.Do_Pretty_Cntexmp*)
  me_name.Model_parser.men_name

let print_cntexmp_model fmt = function
  | None -> ()
  | Some (m, r) ->
      let vc_line_trans _ =
        "vc_line" and me_name_trans = spark_counterexample_transform in
      let print_model =
        Model_parser.print_model_json me_name_trans vc_line_trans in
      let json_result_state (state, _log) =
        let more = match state with
          | Check_ce.Res_fail (ctx, t) ->
              let t =
                Ident.Sattr.fold Term.t_attr_add ctx.Pinterp_core.attrs t in
              let check = match Gnat_expl.search_labels t with
                | Some Gnat_expl.{check={id; reason; sloc}} ->
                    let file, line, col =
                      Gnat_loc.explode (Gnat_loc.orig_loc sloc) in
                    Record [
                      "id", Int id;
                      "vc_kind", String (Gnat_expl.reason_to_ada reason);
                      "sloc", Record [
                        "file", String file;
                        "line", Int line;
                        "col", Int col;
                      ]
                    ]
                | None -> Null in
              ["check", check]
          | Check_ce.Res_stuck reason | Check_ce.Res_incomplete reason ->
              ["reason", String reason]
          | _ -> [] in
        let state =
          ["state", String (Check_ce.string_of_rac_result_state state)] in
        Record (state @ more) in
      Format.fprintf fmt ", %a" (print_json_field "cntexmp" print_model) m;
      Opt.iter
        (Format.fprintf fmt ", %a"
           (print_json_field "giant_step_rac_result" print_json))
        (Opt.map json_result_state r)

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

let print_stats fmt (stats, stat_checker) =
  (* Print the stats for goal solved by transformations as a fake prover. *)
  let fake_prover_ch =
    Whyconf.{prover_name = "Checker"; prover_version = ""; prover_altern = ""}
  in
  match stats with
  | None -> ()
  | Some s ->
    if stat_checker <> 0 then
      Whyconf.Hprover.add s fake_prover_ch {count = stat_checker; max_steps = 0; max_time = 0.0};
    let kv_list = Whyconf.Hprover.fold (fun k v acc -> (k,v)::acc) s [] in
    let get_name pr = pr.Whyconf.prover_name in
    Format.fprintf fmt ", ";
    print_json_field "stats"
      (map_bindings_gnat get_name print_prover_stats) fmt kv_list

let sort_messages (l : (Gnat_expl.check * msg) list) =
  List.sort (fun x y -> compare (fst x).Gnat_expl.id (fst y).Gnat_expl.id) l

let opt_int fmt i = int fmt (Opt.get_def 0 i)

let print_extra_info fmt i =
 let print_info fmt (i, inline) =
  Format.fprintf fmt "{%a, %a}"
    (print_json_field "node" opt_int) i
    (print_json_field "inline" opt_int) inline
  in
  match i with
  | { Gnat_expl.pretty_node = i; inlined = inline } ->
    Format.fprintf fmt ", %a" (print_json_field "extra_info" print_info) (i, inline)


let print_json_msg fmt (check, m) =
  Format.fprintf fmt "{%a, %a, %a, %a%a%a%a%a}"
    (print_json_field "id" int) check.Gnat_expl.id
    (print_json_field "reason" string)
      (Gnat_expl.reason_to_ada check.Gnat_expl.reason)
    (print_json_field "result" bool) m.result
    (print_json_field "check_tree" Json_base.print_json) m.check_tree
    print_extra_info m.extra_info
    print_stats (m.stats, m.stats_checker)
    print_cntexmp_model m.cntexmp_model
    print_manual_proof_info m.manual_proof

let print_warning_list fmt l =
  match l with
  | [] -> ()
  | l ->
    Format.fprintf fmt ", %a" (print_json_field "warnings" (list string)) l

let print_timing_entry fmt t =
  let l = Hashtbl.fold (fun k v acc -> (k,v)::acc) t [] in
  let get_name s = s in
  Format.fprintf fmt ", ";
  print_json_field "timings" (map_bindings_gnat get_name standard_float) fmt l

let print_session_dir = print_json_field "session_dir" string

let print_messages () =
  let msg_set = Gnat_expl.HCheck.fold (fun k v acc -> (k,v) :: acc) msg_set []
  in
  Format.printf "{%a, %a%a%a}@."
  print_session_dir Gnat_config.session_dir
  (print_json_field "results" (list print_json_msg)) (sort_messages msg_set)
  print_warning_list !warning_list
  print_timing_entry (Util.get_timings ())
