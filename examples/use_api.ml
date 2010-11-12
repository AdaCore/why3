

(*
*)


open Why
open Format

(***************

This file builds some goals using the API and calls
the alt-ergo prover to check them

******************)

(* First, we need to access the Why configuration *)

let config = Whyconf.read_config None
let main = Whyconf.get_main config
let env = Env.create_env (Lexer.retrieve (Whyconf.loadpath main)) 

let provers = Whyconf.get_provers config

let alt_ergo = 
  try
    Util.Mstr.find "alt-ergo" provers 
  with Not_found ->
    eprintf "Prover alt-ergo not installed or not configured@.";
    exit 0

let alt_ergo_driver = Driver.load_driver env alt_ergo.Whyconf.driver


(*

a ground propositional goal: True or False

*)

let fmla_true = Term.f_true
let fmla_false = Term.f_false
let fmla1 = Term.f_or fmla_true fmla_false
let () = printf "@[formula 1 created:@ %a@]@." Pretty.print_fmla fmla1

let task1 = None

let goal_id1 = Decl.create_prsymbol (Ident.id_fresh "goal1") 
let task1 = Task.add_prop_decl task1 Decl.Pgoal goal_id1 fmla1

let () = printf "@[task 1 created:@\n%a@]@." Pretty.print_task task1

let result1 = 
  Driver.prove_task ~command:alt_ergo.Whyconf.command
    alt_ergo_driver task1 ()

let () = printf "@[On task 1, alt-ergo answers %a@."
  Call_provers.print_prover_result result1

(*

a propositional goal: A and B implies B

*)

let prop_var_A = Term.create_psymbol (Ident.id_fresh "A") []
let prop_var_B = Term.create_psymbol (Ident.id_fresh "B") []
let fmla_A = Term.f_app prop_var_A []
let fmla_B = Term.f_app prop_var_B []
let fmla2 = Term.f_implies (Term.f_and fmla_A fmla_B) fmla_B
let () = printf "@[formula 2 created:@ %a@]@." Pretty.print_fmla fmla2

let task2 = None
let task2 = Task.add_logic_decl task2 [prop_var_A, None] 
let task2 = Task.add_logic_decl task2 [prop_var_B, None] 
let goal_id2 = Decl.create_prsymbol (Ident.id_fresh "goal2") 
let task2 = Task.add_prop_decl task2 Decl.Pgoal goal_id2 fmla2

let () = printf "@[task 2 created:@\n%a@]@." Pretty.print_task task2

let result2 = 
  Driver.prove_task ~command:alt_ergo.Whyconf.command
    alt_ergo_driver task2 ()

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
    alt_ergo_driver task3 ()

let () = printf "@[On task 3, alt-ergo answers %a@."
  Call_provers.print_prover_result result3


(* build a theory with all these goals *)


