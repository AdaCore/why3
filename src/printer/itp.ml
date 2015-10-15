
open Why3

(* reads the config file *)
let config : Whyconf.config = Whyconf.read_config None
(* the [main] section of the config file *)
let main : Whyconf.main = Whyconf.get_main config

(* builds the environment from the [loadpath] *)
let env : Env.env = Env.create_env (Whyconf.loadpath main)

open Ident
open Term
open Decl

type element = Formula of string * term | Symbol of lsymbol

type sequent = (Loc.position option * element) list

type itp_state = sequent list

 (* or a tree ? *)

(*

 a "tactic" should be any function of type sequent -> sequent list

 applying a tactic :

 apply state tactic =
  let s = pop first sequnt from state

   not right if the state is a tree

*)

let extract_decl acc d =
  match d.d_node with
  | Dtype _ -> acc
  | Ddata _ -> acc
  | Dparam ls -> (ls.ls_name.id_loc,Symbol ls) :: acc
  | Dlogic ld ->
     List.fold_left (fun acc (ls,_) -> (ls.ls_name.id_loc,Symbol ls) :: acc) acc ld
  | Dind (_,ld) ->
     List.fold_left (fun acc (ls,_) -> (ls.ls_name.id_loc,Symbol ls) :: acc) acc ld
  | Dprop (k,pr,t) ->
     let name = match k with
         | Plemma | Paxiom -> pr.pr_name.id_string
         | Pgoal ->  ""
         | Pskip -> assert false
     in
     (t.t_loc,Formula (name,t)) :: acc


let build_sequent task =
  let task = Trans.apply (Trans.goal Introduction.intros) task in
  let ut = Task.used_symbols (Task.used_theories task) in
  let ld = Task.local_decls task ut in
  List.rev (List.fold_left extract_decl [] ld)


open Format

let print_elem fmt (loc,e) =
  Opt.iter (fprintf fmt "[%a]" Pretty.print_loc) loc;
  match e with
    | Symbol ls -> fprintf fmt "%a@\n" Pretty.print_param_decl ls
    | Formula (n,t) -> fprintf fmt "%s : %a@\n" n Pretty.print_term t

let print_sequent fmt s =
  fprintf fmt "========================@\n";
  List.iter (print_elem fmt) s;
  fprintf fmt "========================@."

let test () =
  let file = Sys.argv.(1) in
  printf "Reading file %s@." file;
  let theories = Env.read_file Env.base_language env file in
  let tasks =
    Stdlib.Mstr.fold
      (fun _k th acc ->
       let tasks = Task.split_theory th None None in
       let tasks =
         List.fold_left
           (fun acc task ->
            let tasks = Trans.apply Split_goal.split_goal_wp task in
            List.fold_left
              (fun acc task ->
               let task = Trans.apply (Trans.goal Introduction.intros) task in
               task :: acc)
              acc (List.rev tasks))
           acc tasks
       in
       tasks) theories []
  in
  let sequents = List.map build_sequent tasks in
  List.iter (print_sequent Format.std_formatter) sequents


let () = Printexc.catch test ()
