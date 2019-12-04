open Format

let files    = ref []
let widening = ref None
let domain   = ref None

let options = [
    "--widening", Arg.String (fun s -> widening := Some (int_of_string s)),
      "<value> widening value for fixpoint (default: 3)";
    "--domain", Arg.String (fun s -> domain := Some s),
      "<polyhedra|box|oct> select abstract interpretatino domain (default: polyhedra)"
  ]

let add_file_name f = files := f :: !files

let usage_msg =
  sprintf "Usage: %s [options] file.mlw" (Filename.basename Sys.argv.(0))

let () =
  let open Arg in
  parse (align options) add_file_name usage_msg

open Why3
open Infer_ai

let config : Whyconf.config = Whyconf.read_config None
let main   : Whyconf.main   = Whyconf.get_main config
let env    : Env.env        = Env.create_env (Whyconf.loadpath main)

let parse_file file env =
  try Env.read_file Pmodule.mlw_language env file with
  | Loc.Located(loc, e) ->
     printf "%a: %a@." Loc.gen_report_position loc Exn_printer.exn_printer e;
     exit 1
  | e ->
     printf "unlocated error: %s@." (Printexc.to_string e);
     exit 1

module Domain_dft = Domain.Polyhedra

module MkAbsIntOpt (D: Domain.DOMAIN) : Abs_int_options = struct
  let env = env
  let widening = Opt.get_def 3 !widening
  module Domain = D
end

module MkInvGen (D: Domain.DOMAIN) : Inv_gen = Make(MkAbsIntOpt(D))

let generate_inv m = match !domain with
  | Some "box" ->
     let module InvGen = MkInvGen(Domain.Box) in
     InvGen.infer_loop_invariants m
  | Some "oct" ->
     let module InvGen = MkInvGen(Domain.Oct) in
     InvGen.infer_loop_invariants m
  | _ ->
     let module InvGen = MkInvGen(Domain.Polyhedra) in
     InvGen.infer_loop_invariants m

let run_on_file file =
  (* parse mlw file *)
  let mlw, _ = parse_file file env in
  printf "Syntax OK@.";

  (* generate invariants *)
  let mlw_with_inv = Wstdlib.Mstr.map generate_inv mlw in

  (* print modules to standard output after generating loop invariants *)
  Wstdlib.Mstr.iter (fun s pm ->
      printf "%a@\n" Pmodule.print_module pm) mlw_with_inv;
  exit 0

let () =
  if !files = [] then
    eprintf "no file provided"
  else
    List.iter run_on_file !files
