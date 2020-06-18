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

let usage_msg = sprintf
  "Usage: %s [options] <file> <module>.<ident>...\n\
   Run the interpreter on the given module symbols.\n"
  (Filename.basename Sys.argv.(0))

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

let enable_rac = ref false

let dispatch = ref []

let option_list =
  let open Getopt in
  [ Key ('F', "format"), Hnd1 (AString, fun s -> opt_parser := Some s),
    "<format> select input format (default: \"why\")";
    KLong "real", Hnd1 (APair (',', AInt, APair (',', AInt, AInt)),
      fun (i1, (i2, i3)) -> prec := Some (i1, i2, i3)),
    "<emin>,<emax>,<prec> set format used for real computations\n\
     (e.g., -148,128,24 for float32)";
    KLong "rac", Hnd0 (fun () -> enable_rac := true),
    " enable runtime basic runtime assertion checking";
    KLong "dispatch", Hnd1 (APair ('-', APair ('.', AString, AString),
      APair ('.', AString, AString)), fun arg -> dispatch := arg :: !dispatch),
    ("<f.M> <g.N> Dispatch access to module <f.M> to module <g.N> (useful to\n\
      provide an implementation for a module with abstract types or values)");
  ]

let config, _, env =
  Whyconf.Args.initialize option_list add_opt usage_msg

let () =
  if !opt_file = None then Whyconf.Args.exit_with_usage option_list usage_msg

let prepare_dispatch env l =
  let aux ((p1, m1), (p2, m2)) =
    Pmodule.read_module env [p1] m1,
    Pmodule.read_module env [p2] m2 in
  List.fold_right (fun (source, target) -> Pinterp.add_dispatch env ~source ~target)
    (List.map aux l) Pinterp.empty_dispatch

let do_input f =
  let format = !opt_parser in
  let mm = match f with
    | "-" ->
        Env.read_channel Pmodule.mlw_language ?format env "stdin" stdin
    | file ->
        let (mlw_files, _) =
          Env.read_file Pmodule.mlw_language ?format env file in
        mlw_files
  in
  let muc = Pmodule.create_module env (Ident.id_fresh "") in
  let add_module muc s m =
    let muc = Pmodule.open_scope muc s in
    let muc = Pmodule.use_export muc m in
    Pmodule.close_scope muc false in
  let muc = Why3.Wstdlib.Mstr.fold_left add_module muc mm in
  let prog_parsed = Lexer.parse_expr (Lexing.from_string !opt_exec) in
  let expr = Typing.type_expr_in_muc muc prog_parsed in
  Format.eprintf "%a@." Expr.print_expr expr;

  let known = muc.muc_known in
  let open Pinterp in
  try
    let dispatch = prepare_dispatch env !dispatch in
    let res = eval_global_fundef ~rac:!enable_rac env dispatch known [] expr in
    printf "%a@." (report_eval_result expr) res;
    exit (match res with Pinterp.Normal _, _ -> 0 | _ -> 1);
  with Contr (ctx, term) ->
    printf "%a@." (report_cntr expr) (ctx, term) ;
    exit 1


  (* let do_exec (mod_name, fun_name) =
   *   try
   *     let open Pinterp in
   *     (\* eprintf "Find global symbol %s.%s...@." mod_name fun_name; *\)
   *     let {Pmodule.mod_known= known}, rs = find_global_symbol mm ~mod_name ~fun_name in
   *     (\* eprintf "Find Global fundef %a...@." Expr.print_rs rs; *\)
   *     let locals, body = find_global_fundef known rs in
   *     Opt.iter init_real !prec;
   *     ( try
   *         let dispatch = prepare_dispatch env !dispatch in
   *         let res = eval_global_fundef ~rac:!enable_rac env dispatch known locals body in
   *         printf "%a@." (report_eval_result ~mod_name ~fun_name body) res;
   *         exit (match res with Pinterp.Normal _, _ -> 0 | _ -> 1);
   *       with Contr (ctx, term) ->
   *         printf "%a@." (report_cntr ~mod_name ~fun_name body) (ctx, term) ;
   *         exit 1 )
   *   with Not_found when not (Debug.test_flag Debug.stack_trace) ->
   *     exit 1 in
   * Queue.iter do_exec opt_exec *)

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
