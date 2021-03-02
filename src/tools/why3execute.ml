(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
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

let opt_enable_rac = ref false
let opt_rac_prover = ref None
let opt_rac_try_negate = ref false
let opt_rac_fail_cannot_check = ref false

let use_modules = ref []

let option_list =
  let open Getopt in
  [ Key ('F', "format"), Hnd1 (AString, fun s -> opt_parser := Some s),
    "<format> select input format (default: \"why\")";
    KLong "real", Hnd1 (APair (',', AInt, APair (',', AInt, AInt)),
      fun (i1, (i2, i3)) -> prec := Some (i1, i2, i3)),
    "<emin>,<emax>,<prec> set format used for real computations (e.g.,\n\
     -148,128,24 for float32)";
    KLong "rac", Hnd0 (fun () -> opt_enable_rac := true),
    " enable runtime assertion checking (RAC)";
    KLong "rac-prover", Hnd1 (AString, fun s -> opt_rac_prover := Some s),
    "<prover> use <prover> to check assertions in RAC when term\n\
     reduction is insufficient, with optional, comma-\n\
     separated time and memory limit (e.g. 'cvc4,2,1000')";
    KLong "rac-try-negate", Hnd0 (fun () -> opt_rac_try_negate := true),
    " try checking the negated term using the RAC prover when\n\
     the prover is defined and didn't give a result";
    KLong "rac-fail-cannot-check", Hnd0 (fun () -> opt_rac_fail_cannot_check := true),
    " Fail when a assertion cannot be checked";
    KLong "use", Hnd1 (AString, fun m -> use_modules := m :: !use_modules),
    "<qualified_module> use module in the execution";
  ]

let config, env =
  Whyconf.Args.initialize option_list add_opt usage_msg

let () =
  if !opt_file = None then Whyconf.Args.exit_with_usage option_list usage_msg

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
  let open Pinterp in
  Opt.iter init_real !prec;
  try
    let rac =
      let reduce =
        let trans = "compute_in_goal" and prover = !opt_rac_prover and try_negate = !opt_rac_try_negate in
        rac_reduce_config_lit config env ~trans ?prover ~try_negate () in
      let skip_cannot_compute = not !opt_rac_fail_cannot_check in
      rac_config ~do_rac:!opt_enable_rac ~abstract:false ~skip_cannot_compute ~reduce () in
    let res = eval_global_fundef rac env pmod [] expr in
    printf "%a@." (report_eval_result expr) res;
    exit (match res with Pinterp.Normal _, _, _ -> 0 | _ -> 1);
  with
  | Contr (ctx, term) ->
      Pretty.forget_all ();
      eprintf "%a@." report_cntr (ctx, term);
      exit 1
  | CannotCompute reason ->
      eprintf "Execution terminated because %s@." reason.reason;
      exit 2
  | RACStuck (_, l) ->
      (* TODO Remove this case when value origins (default vs model) can be distinguished
         in RAC *)
      eprintf "RAC cannot continue after %a@."
        (Pp.print_option Pretty.print_loc') l;
      exit 2
  | Failure msg ->
      eprintf "failure: %s@." msg;
      exit 1


let () =
  try
    Opt.iter do_input !opt_file
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
