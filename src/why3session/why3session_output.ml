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

open Why3
open Why3session_lib
open Session_itp
open Format

(**
   TODO add_transformation,...

   TODO:
    filter_state
    filter_time
    filter_?

**)

let opt_output_dir = ref None

let spec =
  ["--output", Arg.String (fun s -> opt_output_dir := Some s),
   " set the directory where to output the files";
   "-o", Arg.String (fun s -> opt_output_dir := Some s),
   " same as --output"
  ]@
    (force_obsolete_spec @ filter_spec @ common_options)

type action =
  | Copy
  | CopyArchive
  | Mod

let rec interactive to_remove =
  eprintf "Do you want to replace the external proof %a (y/n)@."
    print_external_proof to_remove;
  let answer = read_line () in
  match answer with
    | "y" -> true
    | "n" -> false
    | _ -> interactive to_remove

let fname_printer = Ident.create_ident_printer []

let run_one env config filters dir fname =
  let env_session,_,_ =
    read_update_session ~allow_obsolete:!opt_force_obsolete env config fname in
  iter_session (fun file ->
    let fname = Filename.basename file.file_name in
    let fname = try Filename.chop_extension fname with _ -> fname in
    iter_file (fun th ->
      let tname = th.theory_name.Ident.id_string in
      theory_iter_proof_attempt_by_filter filters
        (fun pr ->
          let task =
            Opt.get (goal_task_option pr.proof_parent) in
          match load_prover env_session pr.proof_prover with
          | None ->
            (* In fact That is a bad reason we can always output know? *)
            eprintf "Can't@ output@ task@ for@ prover@ %a@ not@ installed@."
              Whyconf.print_prover pr.proof_prover
          | Some lp ->
            let dest = Driver.file_of_task lp.prover_driver fname tname task in
            (* Uniquify the filename before the extension if it exists*)
            let i = try String.rindex dest '.' with _ -> String.length dest in
            (* Before extension *)
            let name = (String.sub dest 0 i) in
            let name = Ident.string_unique fname_printer name in
            let ext = String.sub dest i (String.length dest - i) in
            let cout = open_out (Filename.concat dir (name ^ ext)) in
            (* Name table not necessary outside of ITP *)
            Driver.print_task lp.prover_driver
              (formatter_of_out_channel cout) task;
            close_out cout
        ) th
    ) file
  ) env_session.session

let run () =
  let env,config,should_exit1 = read_env_spec () in
  let filters,should_exit2 = read_filter_spec config in
  if should_exit1 || should_exit2 then exit 1;
  (* sanitize --to-prover and --to-known-prover for Copy* *)
  match !opt_output_dir with
  | None ->
    eprintf "The@ option@ --output-dir/-o@ must@ be@ set@.";
    exit 1
  | Some dir ->
    try
      iter_files (run_one env config filters dir)
    with OutdatedSession as e ->
      eprintf "@.%a@ You@ can@ allow@ it@ with@ the@ option@ -F.@."
        Exn_printer.exn_printer e


let cmd =
  { cmd_spec     = spec;
    cmd_desc     = "output file send to the prover";
    cmd_name     = "output";
    cmd_run      = run;
  }
