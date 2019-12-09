open Format


(* Some command line options *)
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

(* Some configurations for parsing and typing WhyML *)
(* BEGIN{buildenv} *)
open Why3

let config : Whyconf.config = Whyconf.read_config None
let main   : Whyconf.main   = Whyconf.get_main config
let env    : Env.env        = Env.create_env (Whyconf.loadpath main)
(* END{buildenv} *)

(* Parses and types a file *)
(* BEGIN{parsefile} *)
let parse_file file env =
  try fst (Env.read_file Pmodule.mlw_language env file) with
  | Loc.Located(loc, e) ->
     printf "%a: %a@." Loc.gen_report_position loc Exn_printer.exn_printer e;
     exit 1
  | e ->
     printf "unlocated error: %s@." (Printexc.to_string e);
     exit 1
(* END{parsefile} *)

(* Logic to use loop invariant inference *)
(* open Infer_ai *)

(* BEGIN{main} *)
(* Select a function according to the chosen domain. *)
let generate_inv domain =
  match domain with
  | Some "box"    -> Infer_ai.InvGenBox.infer_loop_invariants
  | Some "oct"    -> Infer_ai.InvGenOct.infer_loop_invariants
  | _ (*default*) -> Infer_ai.InvGenPolyhedra.infer_loop_invariants

let run_on_file (widening:int) (domain: string option) (file: string) =
  (* parse mlw file *)
  let mlw = parse_file file env in

  (* generate invariants *)
  let infer = (generate_inv domain) ~widening env in
  let mlw_with_inv = Wstdlib.Mstr.map infer mlw in
  printf "Invariants generated successfully@.";

  (* print modules to std output with the inferred loop invariants *)
  Wstdlib.Mstr.iter (fun s pm ->
      printf "%a@\n" Pmodule.print_module pm) mlw_with_inv;
  exit 0
(* END{main} *)

let () =
  let widening = Opt.get_def 3 !widening in
  if !files = [] then
    eprintf "No file provided@\n"
  else
    List.iter (run_on_file widening !domain) !files
