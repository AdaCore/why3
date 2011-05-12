

open Why


let includes = ref []
let file = ref None
let opt_version = ref false

let spec = Arg.align [
  ("-I",
   Arg.String (fun s -> includes := s :: !includes),
   "<s> add s to loadpath") ;
(*
  ("-f",
   Arg.String (fun s -> input_files := s :: !input_files),
   "<f> add file f to the project (ignored if it is already there)") ;
*)
  ("-v",
   Arg.Set opt_version,
   " print version information") ;
]

let version_msg = Format.sprintf "Why3 replayer, version %s (build date: %s)"
  Config.version Config.builddate

let usage_str = Format.sprintf
  "Usage: %s [options] [<file.why>|<project directory>]"
  (Filename.basename Sys.argv.(0))

let set_file f = match !file with
  | Some _ ->
      raise (Arg.Bad "only one parameter")
  | None ->
      file := Some f

let () = Arg.parse spec set_file usage_str

let () =
  if !opt_version then begin
    Format.printf "%s@." version_msg;
    exit 0
  end

let fname = match !file with
  | None ->
      Arg.usage spec usage_str;
      exit 1
  | Some f ->
      f

let config = Whyconf.read_config None

let loadpath = (Whyconf.loadpath (Whyconf.get_main config))
  (* @ List.rev !includes *)

let env = Lexer.create_env loadpath

let provers = Whyconf.get_provers config

let provers =
  Util.Mstr.fold (Session.get_prover_data env) provers Util.Mstr.empty

let usleep t = ignore (Unix.select [] [] [] t)


let idle_handler = ref None
let timeout_handler = ref None

module M = Session.Make
  (struct
     type key = int

     let create ?parent () =
       match parent with
         | None -> 0
         | Some  n -> n+1

     let remove _row = ()

     let reset () = ()

     let idle f =
       match !idle_handler with
         | None -> idle_handler := Some f;
         | Some _ -> failwith "Replay.idle: already one handler installed"

     let timeout ~ms f =
       match !timeout_handler with
         | None -> timeout_handler := Some(float ms /. 1000.0 ,f);
         | Some _ -> failwith "Replay.timeout: already one handler installed"

   end)



let main_loop () =
  let last = ref (Unix.gettimeofday ()) in
  while true do
    let time = Unix.gettimeofday () -. !last in
    (* attempt to run timeout handler *)
    let timeout =
      match !timeout_handler with
        | None -> false
        | Some(ms,f) ->
            if time > ms then
              let b = f () in
              if b then true else
                begin
                  timeout_handler := None;
                  true
                end
            else false
    in
    if timeout then
      last := Unix.gettimeofday ()
    else
      (* attempt to run the idle handler *)
      match !idle_handler with
        | None ->
            begin
              let ms =
                match !timeout_handler with
                  | None -> raise Exit
                  | Some(ms,_) -> ms
              in
              usleep (ms -. time)
            end
        | Some f ->
            let b = f () in
            if b then () else
              begin
                idle_handler := None;
              end
  done

open Format

let model_index = Hashtbl.create 257

let init =
  let cpt = ref 0 in
  fun _row any ->
    incr cpt;
    Hashtbl.add model_index !cpt any;
    let name =
      match any with
        | M.Goal g -> M.goal_expl g
        | M.Theory th -> M.theory_name th
        | M.File f -> Filename.basename f.M.file_name
        | M.Proof_attempt a -> let p = a.M.prover in
	  p.Session.prover_name ^ " " ^ p.Session.prover_version
        | M.Transformation tr -> Session.transformation_id tr.M.transf
    in
    printf "Item '%s' loaded@." name

let string_of_result result =
  match result with
    | Session.Undone -> "undone"
    | Session.Scheduled -> "scheduled"
    | Session.Running -> "running"
    | Session.InternalFailure _ -> "internal failure"
    | Session.Done r -> match r.Call_provers.pr_answer with
	| Call_provers.Valid -> "valid"
	| Call_provers.Invalid -> "invalid"
	| Call_provers.Timeout -> "timeout"
	| Call_provers.Unknown _ -> "unknown"
	| Call_provers.Failure _ -> "failure"
	| Call_provers.HighFailure -> "high failure"

let print_result fmt res =
  let t = match res with
    | Session.Done { Call_provers.pr_time = time } ->
	Format.sprintf "(%.2f)" time
    | _ -> ""
  in
  fprintf fmt "%s%s" (string_of_result res) t


let notify any =
  match any with
    | M.Goal g ->
	printf "Goal '%s' proved: %b@." (M.goal_expl g) (M.goal_proved g)
    | M.Theory th ->
	printf "Theory '%s' verified: %b@." (M.theory_name th) (M.verified th)
    | M.File file ->
	printf "File '%s' verified: %b@." (Filename.basename file.M.file_name)
          file.M.file_verified
    | M.Proof_attempt a ->
        let p = a.M.prover in
	printf "Proof with '%s %s' gives %a@."
	  p.Session.prover_name p.Session.prover_version
          print_result a.M.proof_state
    | M.Transformation tr ->
	printf "Transformation '%s' proved: %b@."
          (Session.transformation_id tr.M.transf) tr.M.transf_proved


let project_dir =
  if Sys.file_exists fname then
    begin
      if Sys.is_directory fname then
        begin
          eprintf "Info: found directory '%s' for the project@." fname;
          fname
        end
      else
        begin
          eprintf "Info: found regular file '%s'@." fname;
          let d =
            try Filename.chop_extension fname
            with Invalid_argument _ -> fname
          in
          eprintf "Info: using '%s' as directory for the project@." d;
          d
        end
    end
  else
    failwith "file does not exist"

let main () =
  try
    eprintf "Opening session...@?";
    M.open_session ~env ~provers ~init ~notify project_dir;
    M.maximum_running_proofs :=
      Whyconf.running_provers_max (Whyconf.get_main config);
    eprintf " done@.";
    let files = M.get_all_files () in
    List.iter
      (fun f ->
         eprintf "Replaying file '%s'@." f.M.file_name;
         M.replay ~obsolete_only:false
           ~context_unproved_goals_only:false (M.File f)) files;
    try main_loop ()
    with Exit -> eprintf "Everything done@."
  with e ->
    eprintf "Error while opening session with database '%s'@." project_dir;
    eprintf "Aborting...@.";
    raise e


let () = Printexc.catch main ()
