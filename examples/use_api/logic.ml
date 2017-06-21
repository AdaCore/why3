(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(*******************

This file builds some goals using the API and calls
the alt-ergo prover to check them

******************)

(* opening the Why3 library *)
open Why3

(* a ground propositional goal: true or false *)
let fmla_true : Term.term = Term.t_true
let fmla_false : Term.term = Term.t_false
let fmla1 : Term.term = Term.t_or fmla_true fmla_false

(* printing it *)
open Format
let () = printf "@[formula 1 is:@ %a@]@." Pretty.print_term fmla1


(* a propositional goal: A and B implies A *)

let prop_var_A : Term.lsymbol = Term.create_psymbol (Ident.id_fresh "A") []
let prop_var_B : Term.lsymbol = Term.create_psymbol (Ident.id_fresh "B") []
let atom_A : Term.term = Term.ps_app prop_var_A []
let atom_B : Term.term = Term.ps_app prop_var_B []
let fmla2 : Term.term = Term.t_implies (Term.t_and atom_A atom_B) atom_A
let () = printf "@[formula 2 is:@ %a@]@." Pretty.print_term fmla2


(* building the task for formula 1 alone *)
let task1 : Task.task = None (* empty task *)
let goal_id1 : Decl.prsymbol = Decl.create_prsymbol (Ident.id_fresh "goal1")
let task1 : Task.task = Task.add_prop_decl task1 Decl.Pgoal goal_id1 fmla1

(* printing the task *)
let () = printf "@[task 1 is:@\n%a@]@." Pretty.print_task task1

(* task for formula 2 *)
let task2 = None
let task2 = Task.add_param_decl task2 prop_var_A
let task2 = Task.add_param_decl task2 prop_var_B
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

(* calls Alt-Ergo *)
let result1 : Call_provers.prover_result =
  Call_provers.wait_on_call
    (Driver.prove_task ~limit:Call_provers.empty_limit
                       ~command:alt_ergo.Whyconf.command
    alt_ergo_driver task1)

(* prints Alt-Ergo answer *)
let () = printf "@[On task 1, alt-ergo answers %a@."
  Call_provers.print_prover_result result1

let result2 : Call_provers.prover_result =
  Call_provers.wait_on_call
    (Driver.prove_task ~command:alt_ergo.Whyconf.command
    ~limit:{Call_provers.empty_limit with Call_provers.limit_time = 10}
    alt_ergo_driver task2)

let () = printf "@[On task 2, alt-ergo answers %a in %5.2f seconds@."
  Call_provers.print_prover_answer result1.Call_provers.pr_answer
  result1.Call_provers.pr_time



(*

An arithmetic goal: 2+2 = 4

*)

let two  : Term.term = Term.t_nat_const 2
let four : Term.term = Term.t_nat_const 4

let int_theory : Theory.theory = Env.read_theory env ["int"] "Int"

let plus_symbol : Term.lsymbol =
  Theory.ns_find_ls int_theory.Theory.th_export ["infix +"]

let two_plus_two : Term.term = Term.fs_app plus_symbol [two;two] Ty.ty_int
let two_plus_two : Term.term = Term.t_app_infer plus_symbol [two;two]
let fmla3 : Term.term = Term.t_equ two_plus_two four

let task3 = None
let task3 = Task.use_export task3 int_theory
let goal_id3 = Decl.create_prsymbol (Ident.id_fresh "goal3")
let task3 = Task.add_prop_decl task3 Decl.Pgoal goal_id3 fmla3

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
let zero : Term.term = Term.t_nat_const 0

let mult_symbol : Term.lsymbol =
  Theory.ns_find_ls int_theory.Theory.th_export ["infix *"]

let ge_symbol : Term.lsymbol =
  Theory.ns_find_ls int_theory.Theory.th_export ["infix >="]

let var_x : Term.vsymbol =
  Term.create_vsymbol (Ident.id_fresh "x") Ty.ty_int

let x : Term.term = Term.t_var var_x
let x_times_x : Term.term = Term.t_app_infer mult_symbol [x;x]
let fmla4_aux : Term.term = Term.ps_app ge_symbol [x_times_x;zero]
let fmla4 : Term.term = Term.t_forall_close [var_x] [] fmla4_aux

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

let my_theory : Theory.theory_uc =
  Theory.create_theory (Ident.id_fresh "My_theory")

(* add declarations of goals *)

let () = printf "@[adding goal 1@]@."
let decl_goal1 : Decl.decl = Decl.create_prop_decl Decl.Pgoal goal_id1 fmla1
let my_theory : Theory.theory_uc = Theory.add_decl my_theory decl_goal1

let () = printf "@[adding goal 2@]@."
let my_theory : Theory.theory_uc = Theory.add_param_decl my_theory prop_var_A
let my_theory : Theory.theory_uc = Theory.add_param_decl my_theory prop_var_B
let decl_goal2 : Decl.decl =
  Decl.create_prop_decl Decl.Pgoal goal_id2 fmla2
let my_theory : Theory.theory_uc = Theory.add_decl my_theory decl_goal2

(* helper function: [use th1 th2] insert the equivalent of a "use import th2"
   in theory th1 under construction *)
let use th1 th2 =
  let name = th2.Theory.th_name in
  Theory.close_namespace
    (Theory.use_export (Theory.open_namespace th1 name.Ident.id_string) th2)
    true

let () = printf "@[adding goal 3@]@."
(* use import int.Int *)
let my_theory : Theory.theory_uc = use my_theory int_theory
let decl_goal3 : Decl.decl = Decl.create_prop_decl Decl.Pgoal goal_id3 fmla3
let my_theory : Theory.theory_uc = Theory.add_decl my_theory decl_goal3

let () = printf "@[adding goal 4@]@."
let decl_goal4 : Decl.decl = Decl.create_prop_decl Decl.Pgoal goal_id4 fmla4
let my_theory : Theory.theory_uc = Theory.add_decl my_theory decl_goal4

(* closing the theory *)
let my_theory : Theory.theory = Theory.close_theory my_theory

(* printing the result *)

let () = printf "@[theory is:@\n%a@]@." Pretty.print_theory my_theory

(* getting set of task from a theory *)

let my_tasks : Task.task list =
  List.rev (Task.split_theory my_theory None None)


let () =
  printf "Tasks are:@.";
  let _ =
    List.fold_left
      (fun i t -> printf "Task %d: %a@." i Pretty.print_task t; i+1)
      1 my_tasks
  in ()





(* build a whyml program *)

(* start a module named "Program" *)
let m = Mlw_module.create_module env (Ident.id_fresh "Program")

let mul_int : Term.lsymbol =
  Theory.ns_find_ls int_theory.Theory.th_export ["infix *"]

let unit_type = Ty.ty_tuple []

(* declaration of
     let f (_dummy:unit) : unit
        requires { true }
        ensures { true }
      =
        assert { 6*7 = 42 }
 *)
let d =
  let args =
    [Mlw_ty.create_pvsymbol (Ident.id_fresh "_dummy") Mlw_ty.ity_unit]
  in
  let result = Term.create_vsymbol (Ident.id_fresh "result") unit_type in
  let spec = {
    Mlw_ty.c_pre = Term.t_true;
    c_post = Mlw_ty.create_post result Term.t_true;
    c_xpost = Mlw_ty.Mexn.empty;
    c_effect = Mlw_ty.eff_empty;
    c_variant = [];
    c_letrec  = 0;
  }
  in
  let body =
    let c6 = Term.t_nat_const 6 in
    let c7 = Term.t_nat_const 7 in
    let c42 = Term.t_nat_const 42 in
    let p =
      Term.t_equ (Term.t_app_infer mul_int [c6;c7]) c42
    in
    Mlw_expr.e_assert Mlw_expr.Aassert p
  in
  let lambda = {
    Mlw_expr.l_args = args;
    l_expr = body;
    l_spec = spec;
  }
  in
  let def = Mlw_expr.create_fun_defn (Ident.id_fresh "f") lambda in
  Mlw_decl.create_rec_decl [def]

(*

declaration of
     let f (_dummy:unit) : unit
        requires { true }
        ensures { result = 0 }
      =
        let x = ref 0 in
        !x

*)

(* import the ref.Ref module *)

let ref_module : Mlw_module.modul =
  Mlw_module.read_module env ["ref"] "Ref"

let ref_type : Mlw_ty.T.itysymbol =
  Mlw_module.ns_find_its ref_module.Mlw_module.mod_export ["ref"]

(* the "ref" function *)
let ref_fun : Mlw_expr.psymbol =
  Mlw_module.ns_find_ps ref_module.Mlw_module.mod_export ["ref"]

(* the "!" function *)
let get_fun : Mlw_expr.psymbol =
  Mlw_module.ns_find_ps ref_module.Mlw_module.mod_export ["prefix !"]

let d2 =
  let args =
    [Mlw_ty.create_pvsymbol (Ident.id_fresh "_dummy") Mlw_ty.ity_unit]
  in
  let result = Term.create_vsymbol (Ident.id_fresh "result") Ty.ty_int in
  let spec = {
    Mlw_ty.c_pre = Term.t_true;
    c_post = Mlw_ty.create_post result Term.t_true;
    c_xpost = Mlw_ty.Mexn.empty;
    c_effect = Mlw_ty.eff_empty;
    c_variant = [];
    c_letrec  = 0;
  }
  in
  let body =
    (* building expression "ref 0" *)
    let e =
      (* recall that "ref" has polymorphic type "(v:'a) -> ref 'a".
         We need to build an instance of it *)
      (* we build "ref int" with a *fresh* region *)
      let ity = Mlw_ty.ity_app_fresh ref_type [Mlw_ty.ity_int] in
      (* e1 : the appropriate instance of "ref" *)
      let e1 = Mlw_expr.e_arrow ref_fun [Mlw_ty.ity_int] ity in
      (* we apply it to 0 *)
      let c0 = Mlw_expr.e_const
        (Number.ConstInt (Number.int_const_dec "0")) Mlw_ty.ity_int in
      Mlw_expr.e_app e1 [c0]
    in
    (* building the first part of the let x = ref 0 *)
    let letdef, var_x = Mlw_expr.create_let_pv_defn (Ident.id_fresh "x") e in
    (* building expression "!x" *)
    let bang_x =
      (* recall that "!" as type "ref 'a -> 'a" *)
      let e1 = Mlw_expr.e_arrow get_fun [var_x.Mlw_ty.pv_ity] Mlw_ty.ity_int in
      Mlw_expr.e_app e1 [Mlw_expr.e_value var_x]
    in
    (* the complete body *)
    Mlw_expr.e_let letdef bang_x
  in
  let lambda = {
    Mlw_expr.l_args = args;
    l_expr = body;
    l_spec = spec;
  }
  in
  let def = Mlw_expr.create_fun_defn (Ident.id_fresh "f") lambda in
  Mlw_decl.create_rec_decl [def]






(* TODO: continue *)

(*
let () = Printexc.record_backtrace true

let () =
  try
    let _buggy : Mlw_module.module_uc = Mlw_module.add_pdecl ~wp:true m d in
    ()
  with Not_found ->
    Printexc.print_backtrace stderr;
    flush stderr
*)



(*
Local Variables:
compile-command: "ocaml -I ../../lib/why3 unix.cma nums.cma str.cma dynlink.cma ../../lib/why3/why3.cma use_api.ml"
End:
*)
