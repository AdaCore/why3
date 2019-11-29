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

This file builds some goals based on logic.ml using the API and calls
the cvc4 to query counterexamples for them

Note: the comments of the form BEGIN{id} and END{id} are there for automatic extraction
of the chapter "The Why3 API" of the manual
******************)

(* opening the Why3 library *)
open Why3

(* a ground propositional goal: true or false *)
let fmla_true : Term.term = Term.t_true
let fmla_false : Term.term = Term.t_false

(* printing it *)
open Format

(* a propositional goal: A implies (A and B) *)

(* BEGIN{ce_declarepropvars} *)
let make_attribute (name: string) : Ident.attribute =
  Ident.create_attribute ("model_trace:" ^ name)
let prop_var_A : Term.lsymbol =
  (* [user_position file line left_col right_col] *)
  let loc = Loc.user_position "myfile.my_ext" 28 0 0  in
  let attrs = Ident.Sattr.singleton (make_attribute "my_A") in
  Term.create_psymbol (Ident.id_fresh ~attrs ~loc "A") []
(* END{ce_declarepropvars} *)
let prop_var_B : Term.lsymbol =
  let loc = Loc.user_position "myfile.my_ext2" 101 0 0  in
  let attrs = Ident.Sattr.singleton (make_attribute "my_B") in
  Term.create_psymbol (Ident.id_fresh ~attrs ~loc "B") []

(* BEGIN{ce_adaptgoals} *)
let atom_A : Term.term = Term.ps_app prop_var_A []
let atom_B : Term.term = Term.ps_app prop_var_B []
(* Voluntarily wrong verification condition *)
let fmla2 : Term.term =
  Term.t_implies atom_A (Term.t_and atom_A atom_B)
(* We add a location and attribute to indicate the start of a goal *)
let fmla2 : Term.term =
  let loc = Loc.user_position "myfile.my_ext" 42 28 91  in
  let attrs = Ident.Sattr.singleton Ity.annot_attr in
  (* Note that this remove any existing attribute/locations on fmla2 *)
  Term.t_attr_set ~loc attrs fmla2
(* END{ce_adaptgoals} *)

let () = printf "@[formula 2 is:@ %a@]@." Pretty.print_term fmla2

let task2 = None
let task2 = Task.add_param_decl task2 prop_var_A
let task2 = Task.add_param_decl task2 prop_var_B
(* BEGIN{ce_nobuiltin} *)
let meta_ce = Theory.register_meta_excl "get_counterexmp" [Theory.MTstring]
  ~desc:"Set@ when@ counter-example@ should@ be@ get."
let task2 = Task.add_meta task2 meta_ce [Theory.MAstr ""]
(* END{ce_nobuiltin} *)
let goal_id2 = Decl.create_prsymbol (Ident.id_fresh "goal2")
let task2 = Task.add_prop_decl task2 Decl.Pgoal goal_id2 fmla2
let () = printf "@[task 2 created:@\n%a@]@." Pretty.print_task task2


(* To call a prover, we need to access the Why configuration *)

(* reads the config file *)
let config : Whyconf.config = Whyconf.read_config None
(* the [main] section of the config file *)
let main : Whyconf.main = Whyconf.get_main config
(* all the provers detected, from the config file *)
let provers : Whyconf.config_prover Whyconf.Mprover.t =
  Whyconf.get_provers config

(* BEGIN{ce_get_cvc4ce} *)
(* One alternative for Cvc4 with counterexamples in the config file *)
let cvc4 : Whyconf.config_prover =
  let fp = Whyconf.parse_filter_prover "CVC4,,counterexamples" in
  (* All provers alternative counterexamples that have the name CVC4 *)
  let provers = Whyconf.filter_provers config fp in
  if Whyconf.Mprover.is_empty provers then begin
    eprintf "Prover Cvc4 not installed or not configured@.";
    exit 0
  end else
    (* Most recent version found *)
    snd (Whyconf.Mprover.max_binding provers)
(* END{ce_get_cvc4ce} *)

(* builds the environment from the [loadpath] *)
let env : Env.env = Env.create_env (Whyconf.loadpath main)

(* loading the Cvc4 driver *)
let cvc4_driver : Driver.driver =
  try
    Whyconf.load_driver main env cvc4.Whyconf.driver []
  with e ->
    eprintf "Failed to load driver for Cvc4: %a@."
      Exn_printer.exn_printer e;
    exit 1

(* calls Cvc4 *)
let result1 : Call_provers.prover_result =
  Call_provers.wait_on_call
    (Driver.prove_task ~limit:Call_provers.empty_limit
                       ~command:(Whyconf.get_complete_command cvc4 ~with_steps:false)
    cvc4_driver task2)

(* BEGIN{ce_callprover} *)
(* prints Cvc4 answer *)
let () = printf "@[On task 1, Cvc4 answers %a@."
  Call_provers.print_prover_result result1

let () = printf "Model is %a@."
    (Model_parser.print_model_json ?me_name_trans:None ?vc_line_trans:None)
    result1.Call_provers.pr_model
(* END{ce_callprover} *)
