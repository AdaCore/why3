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
open Wstdlib

let usage_msg = sprintf
  "Usage: %s [options] <file> <module>.<ident>...\n\
   Run the interpreter on the given module symbols.\n"
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

(* Used for real numbers approximation *)
let real_prec = ref 0
let real_emin = ref 0
let real_emax = ref 0

let precision () =
  (!real_emin, !real_emax, !real_prec)

let opt_parser = ref None

let option_list =
  let open Getopt in
  [ Key ('F', "format"), Hnd1 (AString, fun s -> opt_parser := Some s),
    "<format> select input format (default: \"why\")";
    KLong "real", Hnd1 (APair (',', AInt, APair (',', AInt, AInt)),
      fun (i1, (i2, i3)) -> real_emin := i1; real_emax := i2; real_prec := i3),
    "<emin>,<emax>,<prec> set format used for real computations\n\
     (e.g., -148,128,24 for float32)"
  ]

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
        let (mlw_files, _) =
          Env.read_file Pmodule.mlw_language ?format env file in
        mlw_files
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
        let real_param = precision () in
        let res =
          if real_param <> (0, 0, 0) then
            Pinterp.eval_global_symbol ~real_param env m
          else
            Pinterp.eval_global_symbol env m in
        printf "@[<hov 2>Execution of %s.%s ():@\n%a" mid name
          res rs
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
