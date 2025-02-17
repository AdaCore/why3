(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(*******************

This file builds some goals based on logic.ml using the API and calls
CVC4 to query counterexamples for them

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
  let loc = Loc.user_position "myfile.my_ext" 28 0 28 1  in
  let attrs = Ident.Sattr.singleton (make_attribute "my_A") in
  Term.create_psymbol (Ident.id_fresh ~attrs ~loc "A") []
(* END{ce_declarepropvars} *)
let prop_var_B : Term.lsymbol =
  let loc = Loc.user_position "myfile.my_ext2" 101 0 101 1  in
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
  let loc = Loc.user_position "myfile.my_ext" 42 28 42 91  in
  let attrs = Ident.Sattr.singleton Ity.annot_attr in
  (* Note that this remove any existing attribute/locations on fmla2 *)
  Term.t_attr_set ~loc attrs fmla2
(* END{ce_adaptgoals} *)

let () = printf "@[formula 2 is:@ %a@]@." Pretty.print_term fmla2

let task2 = None
let task2 = Task.add_param_decl task2 prop_var_A
let task2 = Task.add_param_decl task2 prop_var_B
(* BEGIN{ce_nobuiltin} *)
let task2 = Task.add_meta task2 Driver.meta_get_counterexmp [Theory.MAstr ""]
(* END{ce_nobuiltin} *)
let goal_id2 = Decl.create_prsymbol (Ident.id_fresh "goal2")
let task2 = Task.add_prop_decl task2 Decl.Pgoal goal_id2 fmla2
let () = printf "@[task 2 created:@\n%a@]@." Pretty.print_task task2


(* To call a prover, we need to access the Why configuration *)

(* reads the default config file *)
let config = Whyconf.init_config None
(* the [main] section of the config file *)
let main : Whyconf.main = Whyconf.get_main config
(* all the provers detected, from the config file *)
let provers : Whyconf.config_prover Whyconf.Mprover.t =
  Whyconf.get_provers config
(* default resource limits *)
let limits =
  Call_provers.{empty_limits with
                limit_time = Whyconf.timelimit main;
                limit_mem = Whyconf.memlimit main }

(* BEGIN{ce_get_cvc4ce} *)
(* One alternative for CVC4 with counterexamples in the config file *)
let cvc4 : Whyconf.config_prover =
  let fp = Whyconf.parse_filter_prover "CVC4,1.7,counterexamples" in
  (* All provers alternative counterexamples that have the name CVC4 and version 1.7 *)
  let provers = Whyconf.filter_provers config fp in
  if Whyconf.Mprover.is_empty provers then begin
    eprintf "Prover CVC4 1.7 not installed or not configured@.";
    exit 1
  end else
    snd (Whyconf.Mprover.max_binding provers)
(* END{ce_get_cvc4ce} *)

(* builds the environment from the [loadpath] *)
let env : Env.env = Env.create_env (Whyconf.loadpath main)

(* loading the CVC4 driver *)
let cvc4_driver : Driver.driver =
  try
    Driver.load_driver_for_prover main env cvc4
  with e ->
    eprintf "Failed to load driver for CVC4,1.7: %a@."
      Exn_printer.exn_printer e;
    exit 1

(* calls CVC4 *)
let result1 : Call_provers.prover_result =
  Call_provers.wait_on_call
    (Driver.prove_task
       ~limits
       ~config:main
       ~command:(Whyconf.get_complete_command cvc4 ~with_steps:false)
    cvc4_driver task2)

(* BEGIN{ce_callprover} *)
(* prints CVC4 answer *)
let () = printf "@[On task 1, CVC4,1.7 answers %a@."
    (Call_provers.print_prover_result ?json:None) result1

let () = printf "Model is %t@."
    (fun fmt ->
       match Check_ce.last_nonempty_model
                result1.Call_provers.pr_models with
       | Some m -> Json_base.print_json fmt (Model_parser.json_model m)
       | None -> fprintf fmt "unavailable")
(* END{ce_callprover} *)

(* Construct program:
   module M =
     let f (x: int) = assert { x <> 42 }
   end *)
let mlw_file =
  let loc () = (* The counterexample selections requires unique locations *)
    Mlw_printer.id_loc () in
  let open Ptree in
  let open Ptree_helpers in
  let let_f =
    let equ = Qident (ident ~loc:(loc ()) Ident.op_equ) in
    let t_x = tvar ~loc:(loc ()) (Qident (ident "x")) in
    let t_42 = tconst ~loc:(loc ()) 42 in
    let t = term ~loc:(loc ()) (Tidapp (equ, [t_x; t_42])) in
    let t = term ~loc:(loc ()) (Tnot t) in
    let body = expr ~loc:(loc ()) (Eassert (Expr.Assert, t)) in
    let pty_int = PTtyapp (Qident (ident "int"), []) in
    let arg = loc (), Some (ident ~loc:(loc ()) "x"), false, Some pty_int in
    let efun =
      Efun ([arg], None, pat Ptree.Pwild, Ity.MaskVisible, empty_spec, body) in
    let e = expr ~loc:(loc ()) efun in
    Dlet (ident "f", false, Expr.RKnone, e) in
  Decls [let_f]

let pm =
  let pms = Typing.type_mlw_file env [] "myfile.mlw" mlw_file in
  Wstdlib.Mstr.find "" pms

let task =
  match Task.split_theory pm.Pmodule.mod_theory None None with
  | [task] -> task
  | _ -> failwith "Not exactly one task"

let {Call_provers.pr_models= models} =
  Call_provers.wait_on_call
    (Driver.prove_task ~limits
       ~config:main
       ~command:(Whyconf.get_complete_command cvc4 ~with_steps:false)
       cvc4_driver task)

let () = print_endline "\n== Check CE"

(* BEGIN{check_ce} *)
let () =
  let why_prover = Some ("Alt-Ergo,2.5.4",limits) in
  let rac = Pinterp.mk_rac ~ignore_incomplete:false
      (Rac.Why.mk_check_term_lit config env ~why_prover ()) in
  let results = Check_ce.models_from_rac ~limits rac env pm models in
  let model, clsf = Opt.get_exn (Failure "No good model found")
       (Check_ce.best_rac_result results) in
  printf "%a@." (Check_ce.print_model_classification env
                   ?verb_lvl:None ~json:false) (model, clsf)
(* END{check_ce} *)

let () = print_endline "\n== RAC execute giant steps\n"

(* BEGIN{check_ce_giant_step} *)
let () =
  let why_prover = Some ("Alt-Ergo,2.5.4",limits) in
  let rac = Pinterp.mk_rac ~ignore_incomplete:false
    (Rac.Why.mk_check_term_lit config env ~why_prover ()) in
  let rac_results = Check_ce.models_from_giant_step ~limits
    rac env pm models in
  let _,res = Opt.get_exn (Failure "No good model found")
    (Check_ce.best_giant_step_result rac_results) in
  printf "%a@." (Check_ce.print_rac_result ?verb_lvl:None) res
(* END{check_ce_giant_step} *)
