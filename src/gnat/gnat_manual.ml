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

let split_file_extention filename =
  try
    let name = Filename.chop_extension filename in
    let ext = String.sub filename (String.length name)
                         (String.length filename - String.length name) in
    (name, ext)
  with
  | Invalid_argument _ -> (filename, "")

let prover_files_dir proj =
  match Gnat_config.proof_dir with
  | None -> ""
  | Some dir ->
     let pdir =
       Filename.concat (Filename.concat dir proj)
                       Gnat_config.prover.Whyconf.prover.Whyconf.prover_name
     in
     if not (Sys.file_exists pdir) then
       Unix.mkdir pdir 0o750;
     pdir

let create_prover_file goal =
  let th = find_goal_theory goal in
  let proj_name =
    get_project_dir (Filename.basename th.theory_parent.file_name) in
  (* Driver.file_of_task does *NOT* return a unique filename
     for lack of a smarter or simpler process to have unique filename
     we use the goal key and concatenate it to the filename *)
  let filename = Driver.file_of_task Gnat_config.prover_driver
                                     th.theory_name.Ident.id_string
                                     th.theory_parent.file_name
                                     (goal_task goal) in
  let (name, ext) = split_file_extention filename in
  let filename = (name ^ string_of_int goal.goal_key ^ ext) in
  let filename = Filename.concat (prover_files_dir proj_name) filename in
  let _ = add_external_proof ~keygen:Gnat_sched.Keygen.keygen ~obsolete:false
                              ~archived:false ~timelimit:0 ~memlimit:0
                              ~edit:(Some filename) goal
                              Gnat_config.prover.Whyconf.prover
                              Unedited in
  let cout = open_out filename in
  let fmt = Format.formatter_of_out_channel cout in
  Driver.print_task Gnat_config.prover_driver filename fmt (goal_task goal);
  close_out cout;
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
     mv_file tmpfile fn
     (* Sys.rename tmpfile fn *)
  | None ->
     Gnat_util.abort_with_message "rewritting goal not edited as a file."
