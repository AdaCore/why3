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
        let file, line1, col1, line2, col2 = Loc.get loc in
        Format.sprintf "%s:(%d:%d)-(%d:%d): %s" file line1 col1 line2 col2 s
    | None -> s
  in
  warning_list := s :: !warning_list

let () = Loc.set_warning_hook add_warning

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

let get_cntexmp_model = function
  | None -> []
  | Some (m, r) ->
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
      let rcd_only_cntexmp_model = [ "cntexmp", (Model_parser.json_model m) ] in
      match r with
      | None -> rcd_only_cntexmp_model
      | Some (Check_ce.RAC_not_done s) -> rcd_only_cntexmp_model
      | Some (Check_ce.RAC_done (state, _log)) ->
          List.append
            rcd_only_cntexmp_model
            [ "giant_step_rac_result", (json_result_state (state, _log)) ]

let get_manual_proof_info info =
  match info with
  | None -> []
  | Some (fname, cmd) ->
      [ "vc_file", String (Sys.getcwd () ^ Filename.dir_sep ^ fname);
        "editor_cmd", String cmd
      ]

let get_prover_stats stat =
  Record [
    "count", Int stat.count;
    "max_steps", Int stat.max_steps;
    "max_time", StandardFloat stat.max_time
  ]

let get_stats (stats, stat_checker) =
  (* Compute the stats for goal solved by transformations as a fake prover. *)
  let fake_prover_ch =
    Whyconf.{prover_name = "Checker"; prover_version = ""; prover_altern = ""}
  in
  match stats with
  | None -> []
  | Some s ->
    if stat_checker <> 0 then
      Whyconf.Hprover.add s fake_prover_ch
        {count = stat_checker; max_steps = 0; max_time = 0.0};
    let kv_list = Whyconf.Hprover.fold (fun k v acc -> (k,v)::acc) s [] in
    let get_name pr = pr.Whyconf.prover_name in
    [ "stats",
      Record (List.map (fun (k,v) -> get_name k, get_prover_stats v) kv_list) ]

let opt_int i = Opt.get_def 0 i

let get_extra_info i =
  match i with
  | { Gnat_expl.pretty_node = i; inlined = inline } ->
      Record [
        "node", Int (opt_int i);
        "inline", Int (opt_int inline)
      ]

let get_msg (check, m) =
  Record (
    List.concat [
      [ "id", Int check.Gnat_expl.id ;
        "reason", String (Gnat_expl.reason_to_ada check.Gnat_expl.reason) ;
        "result", Bool m.result ;
        "check_tree", m.check_tree ;
        "extra_info", get_extra_info m.extra_info
      ] ;
      get_stats (m.stats, m.stats_checker);
      get_cntexmp_model m.cntexmp_model ;
      get_manual_proof_info m.manual_proof
    ]
  )

(* In case several models are returned by Why3, we sort them by id. *)
let sort_messages (l : (Gnat_expl.check * msg) list) =
  List.sort (fun x y -> compare (fst x).Gnat_expl.id (fst y).Gnat_expl.id) l

let get_results () =
  let msg_set =
    Gnat_expl.HCheck.fold (fun k v acc -> (k,v) :: acc) msg_set []
  in
  "results", List (List.map get_msg (sort_messages msg_set))

let get_warnings () =
  match !warning_list with
  | [] -> []
  | l -> [("warnings", List (List.map (fun elem -> String elem) l))]

let get_timings () =
  let l = Hashtbl.fold (fun k v acc -> (k,v)::acc) (Util.get_timings ()) [] in
  let get_name s = s in
  "timings", Record (List.map (fun (k,v) -> get_name k, StandardFloat v) l)

let get_session_dir () =
  "session_dir", String Gnat_config.session_dir

(* The main function, where we build the final Record to be printed using
Why3.Json_base.print_json function. *)
let print_messages () =
  print_json Format.std_formatter (
    Record (
      List.concat [
        [get_session_dir (); get_results (); get_timings ()];
        get_warnings ()
      ]
    )
  )
