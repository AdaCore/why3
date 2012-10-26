(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Format
open Why3
open Stdlib
open Whyconf
open Theory
open Task
open Driver

let debug = Debug.register_info_flag
  ~desc:"information on the run of the stategie" "runstrat"

let () = Exn_printer.register Makeproto.print_error

let usage_msg = sprintf
  "Usage: %s [options] [[file|-]"
  (Filename.basename Sys.argv.(0))

let version_msg = sprintf "Why3 personal strat example"

let opt_queue = Queue.create ()

let add_opt_file x =
  Queue.add x opt_queue

let opt_config = ref None
let opt_extra = ref []
let opt_parser = ref None

let opt_provers = ref []
let add_opt_prover x =
  opt_provers := x::!opt_provers

let opt_loadpath = ref []

let opt_timelimit = ref None
let opt_memlimit = ref None

let opt_j = ref None

let option_list = Arg.align [
  "-", Arg.Unit (fun () -> add_opt_file "-"),
      " Read the input file from stdin";
  "-C", Arg.String (fun s -> opt_config := Some s),
      "<file> Read configuration from <file>";
  "--config", Arg.String (fun s -> opt_config := Some s),
      " same as -C";
  "--extra-config", Arg.String (fun s -> opt_extra := !opt_extra @ [s]),
      "<file> Read additional configuration from <file>";
  "-L", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      "<dir> Add <dir> to the library search path";
  "--library", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      " same as -L";
  "-I", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      " same as -L (obsolete)";
  "-P", Arg.String add_opt_prover,
      "<prover> Try to prove the goals with this prover";
  "--prover", Arg.String add_opt_prover,
      " same as -P";
  "-F", Arg.String (fun s -> opt_parser := Some s),
      "<format> Select input format (default: \"why\")";
  "--format", Arg.String (fun s -> opt_parser := Some s),
      " same as -F";
  "-t", Arg.Int (fun i -> opt_timelimit := Some i),
      "<sec> Set the prover's time limit (default=10, no limit=0)";
  "--timelimit", Arg.Int (fun i -> opt_timelimit := Some i),
      " same as -t";
  "-m", Arg.Int (fun i -> opt_memlimit := Some i),
      "<MiB> Set the prover's memory limit (default: no limit)";
  "--memlimit", Arg.Int (fun i -> opt_timelimit := Some i),
      " same as -m";
  "-j", Arg.Int (fun i -> opt_j := Some i),
  "<int> Set the number of worker to use (default:1)";
  Debug.Args.desc_debug_list;
  Debug.Args.desc_debug_all;
  Debug.Args.desc_debug;
]

type runnable_prover =
  { rp_command : string;
    rp_driver : Driver.driver;
    rp_prover : Whyconf.prover }

let env,provers = try
  Arg.parse option_list add_opt_file usage_msg;

  (** Configuration *)
  let config = read_config !opt_config in
  let config = List.fold_left merge_config config !opt_extra in
  let main = get_main config in
  Whyconf.load_plugins main;

  Debug.Args.set_flags_selected ();

  (** listings*)

  let opt_list = ref false in
  opt_list :=  Debug.Args.option_list () || !opt_list;
  if !opt_list then exit 0;

  if Queue.is_empty opt_queue then begin
    Arg.usage option_list usage_msg;
    exit 1
  end;

  opt_loadpath := List.rev_append !opt_loadpath (Whyconf.loadpath main);
  if !opt_timelimit = None then opt_timelimit := Some (Whyconf.timelimit main);
  if !opt_memlimit  = None then opt_memlimit  := Some (Whyconf.memlimit main);

  let env = Env.create_env !opt_loadpath in

  let driver_file s =
    if Sys.file_exists s || String.contains s '/' || String.contains s '.' then
      s
    else
      Filename.concat Config.datadir (Filename.concat "drivers" (s ^ ".drv")) in

  let load_prover s =
    let filter_prover = Whyconf.parse_filter_prover s in
    let prover = Whyconf.filter_one_prover config filter_prover in
    let dfile = driver_file prover.driver in
    {rp_command =
      String.concat " " (prover.command :: prover.extra_options);
     rp_driver =  load_driver env dfile prover.extra_drivers;
     rp_prover = prover.Whyconf.prover } in

  let provers = List.rev_map load_prover !opt_provers in

  env,provers
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

let jobserver =
  match !opt_j with
  | None -> Makeproto.read_makeflags ()
  | Some i when i <= 1 -> Makeproto.Sequential
  | Some i -> Makeproto.Parallel (Makeproto.make_jobserver i)

let timelimit = match !opt_timelimit with
  | None -> 10
  | Some i when i <= 0 -> 0
  | Some i -> i

let memlimit = match !opt_memlimit with
  | None -> 0
  | Some i when i <= 0 -> 0
  | Some i -> i
let fname_printer = ref (Ident.create_ident_printer [])

let split = Trans.lookup_transform_l "split_goal_wp" env

let called_provers = Hint.create 10
let add_prover_call ((call,_) as d) =
  Hint.add called_provers (Call_provers.prover_call_pid call) d

let not_proved = Queue.create ()

let wait_terminate_win32 () =
  match jobserver with
  | Makeproto.Sequential -> ()
  | Makeproto.Parallel pipe ->
    let rec reclaim_proc () =
      let called = Hint.fold (fun _ r l -> r::l)
        called_provers [] in
      Hint.clear called_provers;
      let test ((run,callback) as c) =
        match Call_provers.query_call run with
        | None -> add_prover_call c
        | Some res -> callback (res ())
      in
      List.iter test called;
      if not (Hint.is_empty called_provers)
      then begin
        Makeproto.release_worker pipe;
        (** TODO make call_prover be able to wait on many process at once *)
        ignore (Unix.select [] [] [] 0.3);
        Makeproto.wait_worker pipe;
        reclaim_proc ()
      end
    in
    reclaim_proc ()

let wait_terminate_unix () =
  match jobserver with
  | Makeproto.Sequential -> ()
  | Makeproto.Parallel pipe ->
    let rec reclaim_proc (pid,ret) =
      let (pc,callback) = Hint.find called_provers pid in
      Hint.remove called_provers pid;
      callback (Call_provers.post_wait_call pc ret ());
      if not (Hint.is_empty called_provers) then wait ()
    and wait () =
      Makeproto.release_worker pipe;
      let res_waitpid = Unix.wait () in
      Makeproto.wait_worker pipe;
      reclaim_proc res_waitpid
    in
    wait ()

let wait_terminate =
  if Sys.os_type = "Unix" then wait_terminate_unix else wait_terminate_win32

let run_call ~rp ~name callback task =
  match jobserver with
  | Makeproto.Sequential ->
    let command = rp.rp_command in
    let call =
      Driver.prove_task ~command ~timelimit ~memlimit rp.rp_driver task in
    Debug.dprintf debug "Run %s: %a@." name Whyconf.print_prover rp.rp_prover;
    let res = (Call_provers.wait_on_call (call ())) () in
    callback res
  | Makeproto.Parallel pipe ->
    let command = Pp.sprintf_wnl "makejob %a %a %s"
      Makeproto.print_fd pipe.Makeproto.pin
      Makeproto.print_fd pipe.Makeproto.pout
      rp.rp_command in
    let call =
      Driver.prove_task ~command ~timelimit ~memlimit rp.rp_driver task in
    Debug.dprintf debug "Run %s: %a@." name Whyconf.print_prover rp.rp_prover;
    add_prover_call (call (), callback)

let rec call_prover name task = function
  | [] ->
    begin let tasks = Trans.apply split task in
    match tasks with
    | [ ] -> Debug.dprintf debug "debug %s proved by split" name
    | [_] -> (* can't split *)
      printf "%s not proved@." name;
      Queue.push name not_proved
    | _ ->
      ignore
        (List.fold_left
           (fun i task ->
             let name = sprintf "%s.%i" name i in
             call_prover name task provers;
             succ i)
           0 tasks)
    end
  | rp::l ->
    let callback pr =
      Debug.dprintf debug "Res %s: %a %a@." name
        Whyconf.print_prover rp.rp_prover
        Call_provers.print_prover_result pr;
      match pr.Call_provers.pr_answer with
      | Call_provers.Valid -> ()
      | Call_provers.Invalid -> Queue.push name not_proved;
      | _ -> call_prover name task l
    in
    run_call ~name ~rp callback task

let do_task name (task : Task.task) =
  let name = sprintf "%s.%s" name
    (task_goal task).Decl.pr_name.Ident.id_string in
  call_prover name task provers


let do_theory name th =
  begin
    let tasks = List.rev (split_theory th None None) in
    List.iter (do_task name) tasks
  end

let do_input env f =
      let fname, cin = match f with
        | "-" -> "stdin", stdin
        | f   -> f, open_in f
      in
      begin
        let m = Env.read_channel ?format:!opt_parser env fname cin in
        close_in cin;
        if Debug.test_flag Typing.debug_type_only then ()
        else
          let add_th t th mi = Ident.Mid.add th.th_name (t,th) mi in
          let do_th _ (t,th) =
            let name = sprintf "%s.%s" fname t in
            do_theory name th in
          Ident.Mid.iter do_th (Mstr.fold add_th m Ident.Mid.empty)
      end

let () =
  try
    Queue.iter (do_input env) opt_queue;
    wait_terminate ();
    if Queue.is_empty not_proved
    then printf "runstrat: All proved@."
    else printf "runstrat: %i not proved@." (Queue.length not_proved)
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

(*
Local Variables:
compile-command: "unset LANG; make -C .. byte"
End:
*)
