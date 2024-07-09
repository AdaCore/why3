(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Why3
open Pmodule

let usage_msg =
  "<file> <expr>\n\
   Execute the expression in the given file (and --use the necessary modules)."

let opt_file = ref None
let opt_exec = ref ""

let add_opt x =
  if !opt_file = None then opt_file := Some x else opt_exec := x
  (* match Strings.split '.' x with
   * | [m;i] -> Queue.push (m,i) opt_exec
   * | _ ->
   *   Format.eprintf "extra arguments must be of the form 'module.ident'@.";
   *   exit 1 *)

(* Used for real numbers approximation *)
let prec = ref None

let opt_parser = ref None

let opt_metas = ref []
let opt_enable_rac = ref false
let opt_rac_prover = ref None
let opt_rac_timelimit = ref None
let opt_rac_steplimit = ref None
let opt_rac_ignore_incomplete = ref true

let use_modules = ref []

let add_opt_meta meta =
  let meta_name, meta_arg =
    try
      let index = String.index meta '=' in
      (String.sub meta 0 index),
      Some (String.sub meta (index+1) (String.length meta - (index + 1)))
    with Not_found ->
      meta, None
  in
  opt_metas := (meta_name,meta_arg)::!opt_metas

let option_list =
  let open Getopt in
  [ Key ('F', "format"), Hnd1 (AString, fun s -> opt_parser := Some s),
    "<format> select input format (default: \"why\")";
    Key ('M', "meta"), Hnd1 (AString, add_opt_meta),
    "<meta>[=<string>|<int>] add a meta to every task during RAC";
    KLong "real", Hnd1 (APair (',', AInt, APair (',', AInt, AInt)),
      fun (i1, (i2, i3)) -> prec := Some (i1, i2, i3)),
    "<emin>,<emax>,<prec> set format used for real computations (e.g.,\n\
     -148,128,24 for float32)";
    KLong "rac", Hnd0 (fun () -> opt_enable_rac := true),
    " enable runtime assertion checking (RAC)";
    KLong "rac-prover", Hnd1 (AString, fun s -> opt_rac_prover := Some s),
    "<prover> use <prover> to check assertions in RAC when term\n\
     reduction is insufficient, with optional, space-\n\
     separated time and memory limit (e.g. 'cvc4 2 1000')";
    KLong "rac-timelimit", Hnd1 (AInt, fun i -> opt_rac_timelimit := Some i),
    "<sec> set the time limit for RAC (with --rac)";
    KLong "rac-steplimit", Hnd1 (AInt, fun i -> opt_rac_steplimit := Some i),
    "<steps> set the step limit for RAC (with --rac)";
    KLong "rac-fail-cannot-check", Hnd0 (fun () -> opt_rac_ignore_incomplete := false),
    " fail RAC as incomplete when an assertion cannot\nbe checked";
    KLong "use", Hnd1 (AString, fun m -> use_modules := m :: !use_modules),
    "<qualified_module> use module in the execution";
  ]

let config, env =
  Whyconf.Args.initialize option_list add_opt usage_msg

let () =
  if !opt_file = None || !opt_exec = "" then
    Whyconf.Args.exit_with_usage usage_msg

let find_module env file q =
  match List.rev q with
  | [] -> assert false
  | [nm] ->
     (try Wstdlib.Mstr.find nm file with Not_found -> read_module env [] nm)
  | nm :: p -> read_module env (List.rev p) nm

let do_input f =
  let format = !opt_parser in
  let mm = match f with
    | "-" ->
        Env.read_channel mlw_language ?format env "stdin" stdin
    | file ->
        let (mlw_files, _) =
          Env.read_file mlw_language ?format env file in
        mlw_files
  in
  let muc = create_module env (Ident.id_fresh "") in

  (* add modules passed in the --use argument to the muc *)
  let add_module muc m =
    let qualid = String.split_on_char '.' m in
    let qualid_last = List.hd (List.rev qualid) in
    let muc = open_scope muc qualid_last in
    let m = find_module env mm qualid in
    let muc = use_export muc m in
    close_scope muc ~import:true in
  let muc = List.fold_left add_module muc (List.rev !use_modules) in

  (* parse and type check command line expression *)
  let lb = Lexing.from_string !opt_exec in
  Loc.set_file "command line expression to execute" lb;
  let prog_parsed = Lexer.parse_expr lb in
  let expr = Typing.type_expr_in_muc muc prog_parsed in

  let pmod = Pmodule.close_module muc in

  (* execute expression *)
  Option.iter Pinterp.init_real !prec;
  try
    let compute_term = Rac.Why.mk_compute_term_lit env () in
    let why_prover = !opt_rac_prover and metas = !opt_metas in
    let rac = Pinterp.mk_rac ~ignore_incomplete:!opt_rac_ignore_incomplete
        (Rac.Why.mk_check_term_lit config env ~metas ?why_prover ()) in
    let env = Pinterp.mk_empty_env env pmod in
    let ctx = Pinterp.mk_ctx env ~do_rac:!opt_enable_rac ~rac ~giant_steps:false
        ~compute_term ?steplimit:!opt_rac_steplimit
        ?timelimit:(Option.map float_of_int !opt_rac_timelimit) () in
    let res = Pinterp.exec_global_fundef ctx [] None expr in
    printf "%a@." (Pinterp.report_eval_result expr) res;
    exit (match res with Pinterp.Normal _, _, _ -> 0 | _ -> 1);
  with
  | Pinterp_core.Fail (ctx, term) ->
      Pretty.forget_all ();
      eprintf "%a@." Pinterp.report_cntr (ctx, term);
      exit 1
  | Pinterp_core.Stuck (_, l, reason) ->
      (* TODO Remove this case when value origins (default vs model) can be distinguished
         in RAC *)
      eprintf "RAC got stuck %s after %a@." reason
        (Pp.print_option_or_default "unknown location" Loc.pp_position) l;
      exit 2
  | Pinterp_core.Cannot_decide (_,_,reason) ->
      eprintf "Execution terminated because %s@." reason;
      exit 2

let () =
  try
    Option.iter do_input !opt_file
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
