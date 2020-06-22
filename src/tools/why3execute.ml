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

let use_modules = ref []

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
    KLong "use-modules",
    Hnd1 (AString, fun l -> use_modules := String.split_on_char ';' l),
    "<use_declaration> use modules to type given expressions separated by ';'";

  ]

let config, _, env =
  Whyconf.Args.initialize option_list add_opt usage_msg

let () =
  if !opt_file = None then Whyconf.Args.exit_with_usage option_list usage_msg

let prepare_dispatch env l =
  let aux ((p1, m1), (p2, m2)) =
    read_module env [p1] m1,
    read_module env [p2] m2 in
  List.fold_right (fun (source, target) -> Pinterp.add_dispatch env ~source ~target)
    (List.map aux l) Pinterp.empty_dispatch

(* TODO: Functions string_list_of_qualid, find_module and the add_use
   inside do_input are replicated from typing.ml. Can be removed if
   the function Typing.add_decl is exported. *)
let string_list_of_qualid q =
  let open Ptree in
  let rec sloq acc = function
    | Qdot (p, id) -> sloq (id.id_str :: acc) p
    | Qident id -> id.id_str :: acc in
  sloq [] q

let find_module env file q =
  let open Ptree in
  match q with
    | Qident {id_str = nm} ->
        (try Wstdlib.Mstr.find nm file with Not_found -> read_module env [] nm)
    | Qdot (p, {id_str = nm}) -> read_module env (string_list_of_qualid p) nm

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

  (* add all modules declared in the file to the muc *)
  let add_module muc s m =
    let muc = open_scope muc s in
    let muc = use_export muc m in
    close_scope muc ~import:false in

  (* parse use declarations provided in the command line and add them
     to the muc *)
  let muc = Wstdlib.Mstr.fold_left add_module muc mm in
  let add_use muc d =
    let open Ptree in
    let lb = Lexing.from_string d in
    Loc.set_file "command line argument --use-modules" lb;
    let decl = Lexer.parse_mlw_file lb in
    match decl with
    | Decls [Duseexport use] -> use_export muc (find_module env mm use)
    | Decls [Duseimport (_loc,import,uses)] ->
       let qualid_last = function Qident x | Qdot (_, x) -> x in
       let use_as q = function Some x -> x | None -> qualid_last q in
       let add_import muc (m, q) =
         let import = import || q = None in
         let muc = open_scope muc (use_as m q).id_str in
         let m = find_module env mm m in
         let muc = use_export muc m in
         close_scope muc ~import in
       List.fold_left add_import muc uses
    | _ -> eprintf "only use declarations supported in command line \
                    option '--use-modules'@.";
           exit 1 in
  let muc = List.fold_left add_use muc !use_modules in

  (* parse and type check command line expression *)
  let lb = Lexing.from_string !opt_exec in
  Loc.set_file "expression to execute" lb;
  let prog_parsed = Lexer.parse_expr lb in
  let expr = Typing.type_expr_in_muc muc prog_parsed in
  let known = muc.muc_known in

  (* execute expression *)
  let open Pinterp in
  Opt.iter init_real !prec;
  try
    let dispatch = prepare_dispatch env !dispatch in
    let res = eval_global_fundef ~rac:!enable_rac env dispatch known [] expr in
    printf "%a@." (report_eval_result expr) res;
    exit (match res with Pinterp.Normal _, _ -> 0 | _ -> 1);
  with Contr (ctx, term) ->
    printf "%a@." (report_cntr expr) (ctx, term) ;
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
