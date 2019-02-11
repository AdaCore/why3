(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(*******************

This file builds some goals using the API and calls
the alt-ergo prover to check them

Note: the comments of the form BEGIN{id} and END{id} are there for automatic extraction
of the chapter "The Why3 API" of the manual
******************)

(* BEGIN{opening} *)
(* opening the Why3 library *)
open Why3

(* a ground propositional goal: true or false *)
let fmla_true : Term.term = Term.t_true
let fmla_false : Term.term = Term.t_false
let fmla1 : Term.term = Term.t_or fmla_true fmla_false
(* END{opening} *)

(* BEGIN{printformula} *)
(* printing it *)
open Format
let () = printf "@[formula 1 is:@ %a@]@." Pretty.print_term fmla1
(* END{printformula} *)


(* a propositional goal: A and B implies A *)

(* BEGIN{declarepropvars} *)
let prop_var_A : Term.lsymbol =
  Term.create_psymbol (Ident.id_fresh "A") []
let prop_var_B : Term.lsymbol =
  Term.create_psymbol (Ident.id_fresh "B") []
(* END{declarepropvars} *)
(* BEGIN{declarepropatoms} *)
let atom_A : Term.term = Term.ps_app prop_var_A []
let atom_B : Term.term = Term.ps_app prop_var_B []
let fmla2 : Term.term =
  Term.t_implies (Term.t_and atom_A atom_B) atom_A
let () = printf "@[formula 2 is:@ %a@]@." Pretty.print_term fmla2
(* END{declarepropatoms} *)

(* BEGIN{buildtask} *)
(* building the task for formula 1 alone *)
let task1 : Task.task = None (* empty task *)
let goal_id1 : Decl.prsymbol = Decl.create_prsymbol (Ident.id_fresh "goal1")
let task1 : Task.task = Task.add_prop_decl task1 Decl.Pgoal goal_id1 fmla1
(* END{buildtask} *)

(* BEGIN{printtask} *)
(* printing the task *)
let () = printf "@[task 1 is:@\n%a@]@." Pretty.print_task task1
(* END{printtask} *)

(* BEGIN{buildtask2} *)
(* task for formula 2 *)
let task2 = None
let task2 = Task.add_param_decl task2 prop_var_A
let task2 = Task.add_param_decl task2 prop_var_B
let goal_id2 = Decl.create_prsymbol (Ident.id_fresh "goal2")
let task2 = Task.add_prop_decl task2 Decl.Pgoal goal_id2 fmla2
let () = printf "@[task 2 created:@\n%a@]@." Pretty.print_task task2
(* END{buildtask2} *)



(* To call a prover, we need to access the Why configuration *)

(* BEGIN{getconf} *)
(* reads the config file *)
let config : Whyconf.config = Whyconf.read_config None
(* the [main] section of the config file *)
let main : Whyconf.main = Whyconf.get_main config
(* all the provers detected, from the config file *)
let provers : Whyconf.config_prover Whyconf.Mprover.t =
  Whyconf.get_provers config
(* END{getconf} *)

(* BEGIN{getanyaltergo} *)
(* One prover named Alt-Ergo in the config file *)
let alt_ergo : Whyconf.config_prover =
  let fp = Whyconf.parse_filter_prover "Alt-Ergo" in
  (** all provers that have the name "Alt-Ergo" *)
  let provers = Whyconf.filter_provers config fp in
  if Whyconf.Mprover.is_empty provers then begin
    eprintf "Prover Alt-Ergo not installed or not configured@.";
    exit 0
  end else
    snd (Whyconf.Mprover.max_binding provers)
(* END{getanyaltergo} *)

(* BEGIN{getaltergo200} *)
(* Specific version 2.0.0 of Alt-Ergo in the config file *)
let alt_ergo_2_0_0 : Whyconf.config_prover =
  let fp = Whyconf.parse_filter_prover "Alt-Ergo,2.0.0" in
  let provers = Whyconf.filter_provers config fp in
  if Whyconf.Mprover.is_empty provers then begin
    eprintf "Prover Alt-Ergo 2.0.0 not installed or not configured@.";
    exit 0
  end else
    snd (Whyconf.Mprover.max_binding provers)
(* END{getaltergo200} *)

(* BEGIN{getdriver} *)
(* builds the environment from the [loadpath] *)
let env : Env.env = Env.create_env (Whyconf.loadpath main)

(* loading the Alt-Ergo driver *)
let alt_ergo_driver : Driver.driver =
  try
    Whyconf.load_driver main env alt_ergo.Whyconf.driver []
  with e ->
    eprintf "Failed to load driver for alt-ergo: %a@."
      Exn_printer.exn_printer e;
    exit 1
(* END{getdriver} *)

(* BEGIN{callprover} *)
(* calls Alt-Ergo *)
let result1 : Call_provers.prover_result =
  Call_provers.wait_on_call
    (Driver.prove_task ~limit:Call_provers.empty_limit
                       ~command:alt_ergo.Whyconf.command
    alt_ergo_driver task1)

(* prints Alt-Ergo answer *)
let () = printf "@[On task 1, Alt-Ergo answers %a@."
  Call_provers.print_prover_result result1
(* END{callprover} *)

(* BEGIN{calltimelimit} *)
let result2 : Call_provers.prover_result =
  Call_provers.wait_on_call
    (Driver.prove_task ~command:alt_ergo.Whyconf.command
    ~limit:{Call_provers.empty_limit with Call_provers.limit_time = 10}
    alt_ergo_driver task2)

let () = printf "@[On task 2, alt-ergo answers %a in %5.2f seconds@."
  Call_provers.print_prover_answer result1.Call_provers.pr_answer
  result1.Call_provers.pr_time
(* END{calltimelimit} *)



(*

An arithmetic goal: 2+2 = 4

*)

(* BEGIN{buildfmla} *)
let two  : Term.term = Term.t_nat_const 2
let four : Term.term = Term.t_nat_const 4
let int_theory : Theory.theory = Env.read_theory env ["int"] "Int"
let plus_symbol : Term.lsymbol =
  Theory.ns_find_ls int_theory.Theory.th_export ["infix +"]
let two_plus_two : Term.term = Term.t_app_infer plus_symbol [two;two]
let fmla3 : Term.term = Term.t_equ two_plus_two four
(* END{buildfmla} *)

(* BEGIN{buildtermalt} *)
let two_plus_two : Term.term = Term.fs_app plus_symbol [two;two] Ty.ty_int
(* END{buildtermalt} *)

(* BEGIN{buildtaskimport} *)
let task3 = None
let task3 = Task.use_export task3 int_theory
let goal_id3 = Decl.create_prsymbol (Ident.id_fresh "goal3")
let task3 = Task.add_prop_decl task3 Decl.Pgoal goal_id3 fmla3
(* END{buildtaskimport} *)

(*
let () = printf "@[task 3 created:@\n%a@]@." Pretty.print_task task3
*)
let () = printf "@[task 3 created@]@."

let result3 =
  Call_provers.wait_on_call
    (Driver.prove_task ~limit:Call_provers.empty_limit
                       ~command:alt_ergo.Whyconf.command
    alt_ergo_driver task3)

let () = printf "@[On task 3, alt-ergo answers %a@."
  Call_provers.print_prover_result result3

(* quantifiers: let's build "forall x:int. x*x >= 0" *)
(* BEGIN{quantfmla1} *)
let zero : Term.term = Term.t_nat_const 0
let mult_symbol : Term.lsymbol =
  Theory.ns_find_ls int_theory.Theory.th_export ["infix *"]
let ge_symbol : Term.lsymbol =
  Theory.ns_find_ls int_theory.Theory.th_export ["infix >="]
(* END{quantfmla1} *)

(* BEGIN{quantfmla2} *)
let var_x : Term.vsymbol =
  Term.create_vsymbol (Ident.id_fresh "x") Ty.ty_int
(* END{quantfmla2} *)

(* BEGIN{quantfmla3} *)
let x : Term.term = Term.t_var var_x
let x_times_x : Term.term = Term.t_app_infer mult_symbol [x;x]
let fmla4_aux : Term.term = Term.ps_app ge_symbol [x_times_x;zero]
(* END{quantfmla3} *)

(* BEGIN{quantfmla4} *)
let fmla4 : Term.term = Term.t_forall_close [var_x] [] fmla4_aux
(* END{quantfmla4} *)

let task4 = None
let task4 = Task.use_export task4 int_theory
let goal_id4 = Decl.create_prsymbol (Ident.id_fresh "goal4")
let task4 = Task.add_prop_decl task4 Decl.Pgoal goal_id4 fmla4

let result4 =
  Call_provers.wait_on_call
    (Driver.prove_task ~limit:Call_provers.empty_limit
                       ~command:alt_ergo.Whyconf.command
    alt_ergo_driver task4)

let () = printf "@[On task 4, alt-ergo answers %a@."
  Call_provers.print_prover_result result4

(* build a theory with all these goals *)

(* create a theory *)
let () = printf "@[creating theory 'My_theory'@]@."

(* BEGIN{buildth1} *)
let my_theory : Theory.theory_uc =
  Theory.create_theory (Ident.id_fresh "My_theory")
(* END{buildth1} *)

(* add declarations of goals *)

let () = printf "@[adding goal 1@]@."
(* BEGIN{buildth2} *)
let decl_goal1 : Decl.decl =
  Decl.create_prop_decl Decl.Pgoal goal_id1 fmla1
let my_theory : Theory.theory_uc = Theory.add_decl my_theory decl_goal1
(* END{buildth2} *)

let () = printf "@[adding goal 2@]@."
(* BEGIN{buildth3} *)
let my_theory : Theory.theory_uc =
  Theory.add_param_decl my_theory prop_var_A
let my_theory : Theory.theory_uc =
  Theory.add_param_decl my_theory prop_var_B
let decl_goal2 : Decl.decl =
  Decl.create_prop_decl Decl.Pgoal goal_id2 fmla2
let my_theory : Theory.theory_uc = Theory.add_decl my_theory decl_goal2
(* END{buildth3} *)

(* BEGIN{buildth4} *)
(* helper function: [use th1 th2] insert the equivalent of a
   "use import th2" in theory th1 under construction *)
let use th1 th2 =
  let name = th2.Theory.th_name in
  Theory.close_scope
    (Theory.use_export (Theory.open_scope th1 name.Ident.id_string) th2)
    ~import:true
(* END{buildth4} *)

let () = printf "@[adding goal 3@]@."
(* use import int.Int *)
(* BEGIN{buildth5} *)
let my_theory : Theory.theory_uc = use my_theory int_theory
let decl_goal3 : Decl.decl =
  Decl.create_prop_decl Decl.Pgoal goal_id3 fmla3
let my_theory : Theory.theory_uc = Theory.add_decl my_theory decl_goal3
(* END{buildth5} *)

let () = printf "@[adding goal 4@]@."
(* BEGIN{buildth6} *)
let decl_goal4 : Decl.decl =
  Decl.create_prop_decl Decl.Pgoal goal_id4 fmla4
let my_theory : Theory.theory_uc = Theory.add_decl my_theory decl_goal4
(* END{buildth6} *)

(* closing the theory *)
(* BEGIN{buildth7} *)
let my_theory : Theory.theory = Theory.close_theory my_theory
(* END{buildth7} *)

(* printing the result *)
(* BEGIN{printtheory} *)
let () = printf "@[my new theory is as follows:@\n@\n%a@]@."
                Pretty.print_theory my_theory
(* END{printtheory} *)

(* getting set of task from a theory *)
(* BEGIN{splittheory} *)
let my_tasks : Task.task list =
  List.rev (Task.split_theory my_theory None None)
(* END{splittheory} *)

(* BEGIN{printalltasks} *)
let () =
  printf "Tasks are:@.";
  let _ =
    List.fold_left
      (fun i t -> printf "Task %d: %a@." i Pretty.print_task t; i+1)
      1 my_tasks
  in ()
(* END{printalltasks} *)







(*
Local Variables:
compile-command: "ocaml -I ../../lib/why3 unix.cma nums.cma str.cma dynlink.cma ../../lib/why3/why3.cma use_api.ml"
End:
*)
