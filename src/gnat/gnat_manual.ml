open Why3
open Session

type goal = int Session.goal

let is_new_manual_proof goal =
  Gnat_config.prover.Whyconf.interactive
  && match PHprover.find_opt goal.goal_external_proofs
                             Gnat_config.prover.Whyconf.prover with
     | None -> true
     | Some attempt -> attempt.proof_obsolete

let rec find_goal_theory goal =
  match goal.goal_parent with
  | Parent_theory th -> th
  | Parent_transf tr -> find_goal_theory tr.transf_parent
  | Parent_metas meta -> find_goal_theory meta.metas_parent

let get_file_extention filename =
  try
    let name = Filename.chop_extension filename in
    let ext = String.sub filename (String.length name)
                         (String.length filename - String.length name) in
    ext
  with
  | Invalid_argument _ -> ""

let prover_files_dir proj =
  match Gnat_config.proof_dir with
  | None -> ""
  | Some dir ->
     let prover_dir = (Filename.concat
                         dir
                         Gnat_config.prover.Whyconf.prover.Whyconf.prover_name)
     in
     if not (Sys.file_exists prover_dir) then
       Unix.mkdir prover_dir 0o750;
     let punit_dir = Filename.concat prover_dir proj in
     if not (Sys.file_exists punit_dir) then
       Unix.mkdir punit_dir 0o750;
     Sysutil.relativize_filename (Sys.getcwd ()) punit_dir

let compute_filename theory goal expl =
  let why_fn =
    Driver.file_of_task Gnat_config.prover_driver
                        theory.theory_name.Ident.id_string
                        theory.theory_parent.file_name
                        (goal_task goal) in
  let ext = get_file_extention why_fn in
  Pp.sprintf "%a%s" Gnat_expl.to_filename expl ext

let create_prover_file goal expl =
  let th = find_goal_theory goal in
  let proj_name = Filename.basename
                    (get_project_dir (Filename.basename
                                        th.theory_parent.file_name)) in
  let filename = Filename.concat (prover_files_dir proj_name)
                                 (compute_filename th goal expl) in
  let cout = open_out filename in
  let fmt = Format.formatter_of_out_channel cout in
  Driver.print_task Gnat_config.prover_driver filename fmt (goal_task goal);
  close_out cout;
  let _ = add_external_proof ~keygen:Gnat_sched.Keygen.keygen ~obsolete:false
                             ~archived:false ~timelimit:0 ~memlimit:0
                             ~edit:(Some filename) goal
                             Gnat_config.prover.Whyconf.prover
                             Unedited in
  filename

let get_prover_file goal =
  match PHprover.find_opt goal.goal_external_proofs
                                  Gnat_config.prover.Whyconf.prover with
  | Some pa -> pa.proof_edited_as
  | _ -> None

(* This function is needed because when renaming a file from /tmp
   to a file on the home partition causes an exception *)
let mv_file oldf newf =
  let f_in = open_in oldf in
  let f_out = open_out newf in
  try
    let rec print () =
      Printf.fprintf f_out "%s\n" (input_line f_in);
      print () in
    print ()
  with
  | End_of_file -> flush f_out; close_out f_out; close_in f_in

let rewrite_goal g =
  match get_prover_file g with
  | Some fn ->
     let old = open_in fn in
     let tmpfile = Filename.temp_file "tmp__" (Filename.basename fn) in
     let cout = open_out tmpfile in
     let fmt = Format.formatter_of_out_channel cout in
     Driver.print_task ~old Gnat_config.prover_driver
                       tmpfile fmt (Session.goal_task g);
     close_out cout;
     close_in old;
     mv_file tmpfile fn;
     Unix.unlink tmpfile
  | None ->
     Gnat_util.abort_with_message "rewritting goal not edited as a file."
