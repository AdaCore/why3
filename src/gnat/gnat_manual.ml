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

let create_prover_file goal =
  let th = find_goal_theory goal in
  let filename = Driver.file_of_task Gnat_config.prover_driver
                                     th.theory_name.Ident.id_string
                                     th.theory_parent.file_name
                                     (goal_task goal) in
  let _ = add_external_proof ~keygen:Gnat_sched.Keygen.keygen ~obsolete:false
                              ~archived:false ~timelimit:0 ~memlimit:0
                              ~edit:(Some filename) goal
                              Gnat_config.prover.Whyconf.prover
                              Unedited in
  let cout = open_out filename in
  let fmt = Format.formatter_of_out_channel cout in
  Driver.print_task Gnat_config.prover_driver filename fmt (goal_task goal);
  filename

let get_prover_file goal =
  match PHprover.find_opt goal.goal_external_proofs
                                  Gnat_config.prover.Whyconf.prover with
  | Some pa -> pa.proof_edited_as
  | _ -> None
