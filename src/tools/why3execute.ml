(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Why3
open Wstdlib

let usage_msg = sprintf
  "Usage: %s [options] file module.ident..."
  (Filename.basename Sys.argv.(0))

let opt_file = ref None
let opt_exec = Queue.create ()

let add_opt x =
  if !opt_file = None then opt_file := Some x else
  match Strings.split '.' x with
  | [m;i] -> Queue.push (m,i) opt_exec
  | _ ->
    Format.eprintf "extra arguments must be of the form 'module.ident'@.";
    exit 1

let opt_parser = ref None

let option_list = [
  "-F", Arg.String (fun s -> opt_parser := Some s),
      "<format> select input format (default: \"why\")";
  "--format", Arg.String (fun s -> opt_parser := Some s),
      " same as -F" ]

let config, _, env =
  Whyconf.Args.initialize option_list add_opt usage_msg

let () =
  if !opt_file = None then Whyconf.Args.exit_with_usage option_list usage_msg

let do_input f =
  let format = !opt_parser in
  let mm = match f with
    | "-" ->
        Env.read_channel Pmodule.mlw_language ?format env "stdin" stdin
    | file ->
        Env.read_file Pmodule.mlw_language ?format env file
  in
  let do_exec (mid,name) =
    let m = try Mstr.find mid mm with Not_found ->
      eprintf "Module '%s' not found.@." mid;
      exit 1 in
    let rs =
      try Pmodule.ns_find_rs m.Pmodule.mod_export [name]
      with Not_found ->
        eprintf "Function '%s' not found in module '%s'.@." name mid;
        exit 1 in
(*
    match Pdecl.find_definition m.Pmodule.mod_known rs with
    | None ->
      eprintf "Function '%s.%s' has no definition.@." mid name;
      exit 1
    | Some d ->
*)
      try
        printf "@[<hov 2>Execution of %s.%s ():@\n%a" mid name
          (Pinterp.eval_global_symbol env m) rs
      with e when Debug.test_noflag Debug.stack_trace ->
        printf "@\n@]@.";
        raise e in
  Queue.iter do_exec opt_exec

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
