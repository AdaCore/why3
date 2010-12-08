(***************

This file builds some goals using the API and calls
the alt-ergo prover to check them

******************)

(* opening the Why3 library *)
open Why

(* a ground propositional goal: true or false *)
let fmla_true : Term.fmla = Term.f_true
let fmla_false : Term.fmla = Term.f_false
let fmla1 : Term.fmla = Term.f_or fmla_true fmla_false

(* printing it *)
open Format
let () = printf "@[formula 1 is:@ %a@]@." Pretty.print_fmla fmla1


(* a propositional goal: A and B implies A *)

let prop_var_A : Term.lsymbol = Term.create_psymbol (Ident.id_fresh "A") []
let prop_var_B : Term.lsymbol = Term.create_psymbol (Ident.id_fresh "B") []
let atom_A : Term.fmla = Term.f_app prop_var_A []
let atom_B : Term.fmla = Term.f_app prop_var_B []
let fmla2 : Term.fmla = Term.f_implies (Term.f_and atom_A atom_B) atom_A
let () = printf "@[formula 2 is:@ %a@]@." Pretty.print_fmla fmla2


(* To build tasks and call prover, we need to access the Why configuration *)

(* reads the config file *)
let config = Whyconf.read_config None

(* the [main] section of the config file *)
let main = Whyconf.get_main config

(* builds the environment from the [loadpath] *)
let env = Env.create_env (Lexer.retrieve (Whyconf.loadpath main)) 

(* the [provers] of the config file *)
let provers = Whyconf.get_provers config

(* the [prover alt-ergo] section of the config file *)
let alt_ergo = 
  try
    Util.Mstr.find "alt-ergo" provers 
  with Not_found ->
    eprintf "Prover alt-ergo not installed or not configured@.";
    exit 0

(* loading the Alt-Ergo driver *)
let alt_ergo_driver = Driver.load_driver env alt_ergo.Whyconf.driver

(* building the task for formula 1 alone *)
let task1 = None (* empty task *)
let goal_id1 = Decl.create_prsymbol (Ident.id_fresh "goal1") 
let task1 = Task.add_prop_decl task1 Decl.Pgoal goal_id1 fmla1

(* printing the task *)
let () = printf "@[task 1 is:@\n%a@]@." Pretty.print_task task1

(* call Alt-Ergo *)
let result1 = 
  Driver.prove_task ~command:alt_ergo.Whyconf.command
    alt_ergo_driver task1 () ()

(* prints Alt-Ergo answer *)
let () = printf "@[On task 1, alt-ergo answers %a@."
  Call_provers.print_prover_result result1

let task2 = None
let task2 = Task.add_logic_decl task2 [prop_var_A, None] 
let task2 = Task.add_logic_decl task2 [prop_var_B, None] 
let goal_id2 = Decl.create_prsymbol (Ident.id_fresh "goal2") 
let task2 = Task.add_prop_decl task2 Decl.Pgoal goal_id2 fmla2

let () = printf "@[task 2 created:@\n%a@]@." Pretty.print_task task2

let result2 = 
  Driver.prove_task ~command:alt_ergo.Whyconf.command
    alt_ergo_driver task2 () ()

let () = printf "@[On task 2, alt-ergo answers %a@."
  Call_provers.print_prover_result result2



(*

An arithmetic goal: 2+2 = 4

*)

let two = Term.t_const (Term.ConstInt "2")
let four = Term.t_const (Term.ConstInt "4")

let int_theory = Env.find_theory env ["int"] "Int"

let plus_symbol = Theory.ns_find_ls int_theory.Theory.th_export ["infix +"]

let two_plus_two = Term.t_app plus_symbol [two;two] Ty.ty_int

let fmla3 = Term.f_equ two_plus_two four

let task3 = None
let task3 = Task.use_export task3 int_theory
let goal_id3 = Decl.create_prsymbol (Ident.id_fresh "goal3") 
let task3 = Task.add_prop_decl task3 Decl.Pgoal goal_id3 fmla3

(*
let () = printf "@[task 3 created:@\n%a@]@." Pretty.print_task task3
*)
let () = printf "@[task 3 created@]@." 

let result3 = 
  Driver.prove_task ~command:alt_ergo.Whyconf.command
    alt_ergo_driver task3 () ()

let () = printf "@[On task 3, alt-ergo answers %a@."
  Call_provers.print_prover_result result3


(* build a theory with all these goals *)


