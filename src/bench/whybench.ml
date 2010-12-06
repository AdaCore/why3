(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
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
open Why
open Util
open Whyconf
open Theory
open Task
open Driver
open Trans
module B = Bench
module C = Call_provers

let usage_msg = sprintf
  "Usage: %s [options] [[file|-] [-T <theory> [-G <goal>]...]...]...
  [-P <prover> ]..."
  (Filename.basename Sys.argv.(0))

let opt_queue = Queue.create ()

let opt_input = ref None
let opt_theory = ref None
let opt_trans = ref []
let opt_metas = ref []
let opt_debug = ref []

let add_opt_file x =
  let tlist = Queue.create () in
  Queue.push (Some x, tlist) opt_queue;
  opt_input := Some tlist

let add_opt_theory =
  let rdot = (Str.regexp "\\.") in fun x ->
  let l = Str.split rdot x in
  let p, t = match List.rev l with
    | t::p -> List.rev p, t
    | _ -> assert false
  in
  match !opt_input, p with
  | None, [] ->
      eprintf "Option '-T'/'--theory' with a non-qualified \
        argument requires an input file.@.";
      exit 1
  | Some tlist, [] ->
      let glist = Queue.create () in
      Queue.push (x, p, t, glist) tlist;
      opt_theory := Some glist
  | _ ->
      let tlist = Queue.create () in
      Queue.push (None, tlist) opt_queue;
      opt_input := None;
      let glist = Queue.create () in
      Queue.push (x, p, t, glist) tlist;
      opt_theory := Some glist

let add_opt_goal x = match !opt_theory with
  | None ->
      eprintf "Option '-G'/'--goal' requires a theory.@.";
      exit 1
  | Some glist ->
      let l = Str.split (Str.regexp "\\.") x in
      Queue.push (x, l) glist

let add_opt_trans x = opt_trans := x::!opt_trans

let add_opt_debug x = opt_debug := x::!opt_debug

let add_opt_meta meta =
  let meta_name, meta_arg =
    let index = String.index meta '=' in
    (String.sub meta 0 index),
    (String.sub meta (index+1) (String.length meta - (index + 1))) in
  opt_metas := (meta_name,meta_arg)::!opt_metas

let opt_config = ref None
let opt_parser = ref None
let opt_prover = ref []
let opt_loadpath = ref []
let opt_output = ref None
let opt_timelimit = ref None
let opt_memlimit = ref None
let opt_task = ref None

let opt_print_theory = ref false
let opt_print_namespace = ref false
let opt_list_transforms = ref false
let opt_list_printers = ref false
let opt_list_provers = ref false
let opt_list_formats = ref false
let opt_list_metas = ref false
let opt_list_flags = ref false

let opt_debug_all = ref false

let option_list = Arg.align [
  "-", Arg.Unit (fun () -> add_opt_file "-"),
      " Read the input file from stdin";
  "-T", Arg.String add_opt_theory,
      "<theory> Select <theory> in the input file or in the library";
  "--theory", Arg.String add_opt_theory,
      " same as -T";
  "-G", Arg.String add_opt_goal,
      "<goal> Select <goal> in the last selected theory";
  "--goal", Arg.String add_opt_goal,
      " same as -G";
  "-C", Arg.String (fun s -> opt_config := Some s),
      "<file> Read configuration from <file>";
  "--config", Arg.String (fun s -> opt_config := Some s),
      " same as -C";
  "-L", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      "<dir> Add <dir> to the library search path";
  "--library", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      " same as -L";
  "-I", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      " same as -L (obsolete)";
  "-P", Arg.String (fun s -> opt_prover := s::!opt_prover),
      "Add <prover> in the bench";
  "--prover", Arg.String (fun s -> opt_prover := s::!opt_prover),
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
  "-a", Arg.String add_opt_trans,
      "<transformation> Apply a transformation to every task";
  "--apply-transform", Arg.String add_opt_trans,
      " same as -a";
  "-M", Arg.String add_opt_meta,
      "<meta_name>=<string> Add a string meta to every task";
  "--meta", Arg.String add_opt_meta,
      " same as -M";
  "-o", Arg.String (fun s -> opt_output := Some s),
      "<dir> Print the selected goals to separate files in <dir>";
  "--output", Arg.String (fun s -> opt_output := Some s),
      " same as -o";
  "--print-theory", Arg.Set opt_print_theory,
      " Print selected theories";
  "--print-namespace", Arg.Set opt_print_namespace,
      " Print namespaces of selected theories";
  "--list-transforms", Arg.Set opt_list_transforms,
      " List known transformations";
  "--list-printers", Arg.Set opt_list_printers,
      " List known printers";
  "--list-provers", Arg.Set opt_list_provers,
      " List known provers";
  "--list-formats", Arg.Set opt_list_formats,
      " List known input formats";
  "--list-metas", Arg.Set opt_list_metas,
      " List known metas";
  "--list-debug-flags", Arg.Set opt_list_flags,
      " List known debug flags";
  "--debug-all", Arg.Set opt_debug_all,
      " Set all debug flags (except parse_only and type_only)";
  "--debug", Arg.String add_opt_debug,
      "<flag> Set a debug flag" ]

let tools = ref []
let probs = ref []

let () =
  try
  Arg.parse option_list add_opt_file usage_msg;

  (** Debug flag *)
  if !opt_debug_all then begin
    List.iter (fun (_,f,_) -> Debug.set_flag f) (Debug.list_flags ());
    Debug.unset_flag Typing.debug_parse_only;
    Debug.unset_flag Typing.debug_type_only
  end;

  List.iter (fun s -> Debug.set_flag (Debug.lookup_flag s)) !opt_debug;

  (** Configuration *)
  let config = try read_config !opt_config with Not_found ->
    option_iter (eprintf "Config file '%s' not found.@.") !opt_config;
    exit 1;
  in

  let main = get_main config in
  Whyconf.load_plugins main;
  Scheduler.maximum_running_proofs := Whyconf.running_provers_max main;
  (** listings*)

  let opt_list = ref false in
  if !opt_list_transforms then begin
    opt_list := true;
    printf "@[<hov 2>Known non-splitting transformations:@\n%a@]@\n@."
      (Pp.print_list Pp.newline Pp.string)
      (List.sort String.compare (Trans.list_transforms ()));
    printf "@[<hov 2>Known splitting transformations:@\n%a@]@\n@."
      (Pp.print_list Pp.newline Pp.string)
      (List.sort String.compare (Trans.list_transforms_l ()));
  end;
  if !opt_list_printers then begin
    opt_list := true;
    printf "@[<hov 2>Known printers:@\n%a@]@\n@."
      (Pp.print_list Pp.newline Pp.string)
      (List.sort String.compare (Printer.list_printers ()))
  end;
  if !opt_list_formats then begin
    opt_list := true;
    let print1 fmt s = fprintf fmt "%S" s in
    let print fmt (p, l) =
      fprintf fmt "%s [%a]" p (Pp.print_list Pp.comma print1) l
    in
    printf "@[<hov 2>Known input formats:@\n%a@]@."
      (Pp.print_list Pp.newline print)
      (List.sort Pervasives.compare (Env.list_formats ()))
  end;
  if !opt_list_provers then begin
    opt_list := true;
    let config = read_config !opt_config in
    let print fmt s prover = fprintf fmt "%s (%s)@\n" s prover.name in
    let print fmt m = Mstr.iter (print fmt) m in
    let provers = get_provers config in
    printf "@[<hov 2>Known provers:@\n%a@]@." print provers
  end;
  if !opt_list_metas then begin
    opt_list := true;
    let print fmt m = fprintf fmt "@[%s %s%a@]"
      (let s = m.meta_name in
        if String.contains s ' ' then "\"" ^ s ^ "\"" else s)
      (if m.meta_excl then "* " else "")
      (Pp.print_list Pp.space Pretty.print_meta_arg_type) m.meta_type
    in
    let cmp m1 m2 = Pervasives.compare m1.meta_name m2.meta_name in
    printf "@[<hov 2>Known metas:@\n%a@]@\n@."
      (Pp.print_list Pp.newline print) (List.sort cmp (Theory.list_metas ()))
  end;
  if !opt_list_flags then begin
    opt_list := true;
    let print fmt (p,_,_) = fprintf fmt "%s" p in
    printf "@[<hov 2>Known debug flags:@\n%a@]@."
      (Pp.print_list Pp.newline print)
      (List.sort Pervasives.compare (Debug.list_flags ()))
  end;
  if !opt_list then exit 0;

  if Queue.is_empty opt_queue then begin
    Arg.usage option_list usage_msg;
    exit 1
  end;

  (* Someting else using rc file intead of driver will be added later *)
  (* if !opt_prover <> None && !opt_driver <> None then begin *)
  (*   eprintf "Options '-P'/'--prover' and \ *)
  (*     '-D'/'--driver' cannot be used together.@."; *)
  (*   exit 1 *)
  (* end; *)

  if !opt_prover = [] then begin
      eprintf "At least one prover is required.@.";
      exit 1 end;

  opt_loadpath := List.rev_append !opt_loadpath (Whyconf.loadpath main);
  if !opt_timelimit = None then opt_timelimit := Some (Whyconf.timelimit main);
  if !opt_memlimit  = None then opt_memlimit  := Some (Whyconf.memlimit main);
  let add_meta task (meta,s) =
    let meta = lookup_meta meta in
    add_meta task meta [MAstr s]
  in
  opt_task := List.fold_left add_meta !opt_task !opt_metas;

  let env = Env.create_env (Lexer.retrieve !opt_loadpath) in
  let map_prover s =
    let prover = try Mstr.find s (get_provers config) with
      | Not_found -> eprintf "Prover %s not found.@." s; exit 1
    in
    { B.tval   = s;
      ttrans   = Trans.identity;
      tdriver  = load_driver env prover.driver;
      tcommand = prover.command;
      tenv     = env;
      tuse     = !opt_task;
      ttime    = of_option !opt_timelimit;
      tmem     = of_option !opt_memlimit;
    } in
  tools := List.map map_prover !opt_prover;

  let transl =
      let lookup acc t = Trans.compose_l
    (try Trans.singleton (Trans.lookup_transform t env) with
       Trans.UnknownTrans _ -> Trans.lookup_transform_l t env) acc
      in
      List.fold_left lookup Trans.identity_l !opt_trans in


  let fold_prob acc = function
    | None, _ -> acc
    | Some f, _ ->
      let gen env task =
        let fwhy () =
          let fname, cin = match f with
            | "-" -> "stdin", stdin
            | f   -> f, open_in f
          in
          let m = Env.read_channel ?format:!opt_parser env fname cin in
          close_in cin;
          let th = Mnm.bindings m in
          let map (name,th) = name,Task.split_theory th None task in
          let fold acc (n,l) =
            List.rev_append (List.map (fun v -> (n,v)) l) acc in
          th |> List.map map |> List.fold_left fold [] in
        Scheduler.do_why_sync fwhy () in
      { B.ptask   = gen;
        ptrans   = transl;
      }::acc in
  probs := Queue.fold fold_prob [] opt_queue

  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

(** valid * timeout * unknown * invalid  *)
type nb_avg = int * float

let add_nb_avg (nb,avg) time =
  (succ nb, ((float nb) *. avg +. time) /. (float (succ nb)))
let empty_nb_avg = (0,0.)
let print_nb_avg fmt (nb,avg) = fprintf fmt "%i : %.2f" nb avg
type tool_res =
    { valid : nb_avg;
      timeout : nb_avg;
      unknown : nb_avg;
      invalid : nb_avg;
      failure : nb_avg}

let empty_tool_res =
  { valid   = empty_nb_avg;
    timeout = empty_nb_avg;
    unknown = empty_nb_avg;
    invalid = empty_nb_avg;
    failure = empty_nb_avg;
  }

let count_result =
  let m = Mnm.empty in
  let fold m res =
    let tr = Mnm.find_default res.B.tool empty_tool_res m in
    let r = res.B.result in
    let tr = match r.C.pr_answer with
      | C.Valid -> {tr with valid = add_nb_avg tr.valid r.C.pr_time}
      | C.Timeout -> {tr with timeout = add_nb_avg tr.timeout r.C.pr_time}
      | C.Invalid -> {tr with invalid = add_nb_avg tr.invalid r.C.pr_time}
      | C.Unknown _ -> {tr with unknown = add_nb_avg tr.unknown r.C.pr_time}
      | C.Failure _ | C.HighFailure ->
        {tr with failure = add_nb_avg tr.failure r.C.pr_time} in
    Mnm.add res.B.tool tr m in
  List.fold_left fold m

let () = Scheduler.async := (fun f v -> ignore (Thread.create f v))


let () =
  let m = Mutex.create () in
  let callback tool prob task i res =
    Mutex.lock m;
    printf "%s %a %i with %s : %a@."
      prob Pretty.print_pr (task_goal task) i tool
      Scheduler.print_pas res;
    Mutex.unlock m
  in
  let l = B.all_list ~callback !tools !probs in
  (* let print_result fmt res = *)
  (*   fprintf fmt "%s %a %i with %s : %a@." *)
  (*     res.B.prob Pretty.print_pr *)
  (*     (task_goal res.B.task) res.B.idtask res.B.tool *)
  (*     C.print_prover_result res.B.result in *)
  (* eprintf "Done :@.%a@." *)
  (*   (Pp.print_list Pp.newline print_result) l *)
  let tool_res = count_result l in
  let print_tool_res tool_name tool_res =
    printf "(%a, %a, %a, %a, %a) - %s@."
      print_nb_avg tool_res.valid
      print_nb_avg tool_res.unknown
      print_nb_avg tool_res.timeout
      print_nb_avg tool_res.invalid
      print_nb_avg tool_res.failure
      tool_name in
  printf "(v,t,u,f,i) - valid, unknown, timeout, invalid, failure@.";
  Mnm.iter print_tool_res tool_res

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/whybench.byte"
End:
*)
