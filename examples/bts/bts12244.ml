(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(*******************

This file exposes bug 12244 directly using the API

******************)

open Why
open Format


(* reads the config file *)
let config : Whyconf.config = Whyconf.read_config None

(* the [main] section of the config file *)
let main : Whyconf.main = Whyconf.get_main config

(* builds the environment from the [loadpath] *)
let env : Env.env = Lexer.create_env (Whyconf.loadpath main)


let int_theory : Theory.theory = Env.find_theory env ["int"] "Int"

(*

An arithmetic goal: 1 = 2

*)

let one : Term.term = Term.t_const (Term.ConstInt "1")
let two : Term.term = Term.t_const (Term.ConstInt "2")
let fmla : Term.term = Term.t_equ one two

let task = Task.use_export None int_theory
let goal_id = Decl.create_prsymbol (Ident.id_fresh "G")
let task = Task.add_prop_decl task Decl.Pgoal goal_id fmla

(*
let () = printf "@[task:@\n%a@]@." Pretty.print_task task
*)

let inline = Trans.lookup_transform "inline_goal" env
let split = Trans.lookup_transform_l "split_goal_right" env


let task_inline = Trans.apply inline task

let task_split =
  match Trans.apply split task with
    | [t] -> t
    | _ -> assert false

let task_checksum t =
  fprintf str_formatter "%a@." Pretty.print_task t;
  let s = flush_str_formatter () in
  Digest.to_hex (Digest.string s)

let sum = task_checksum task

let sum_inline = task_checksum task_inline

let sum_split = task_checksum task_split

let () = printf "@[task == task_inline ? %b   same checksums ? %b@]@."
  (Task.task_equal task task_inline) (sum = sum_inline)

let () = printf "@[task == task_split ? %b    same checksums ? %b@]@."
  (Task.task_equal task task_split) (sum = sum_split)


