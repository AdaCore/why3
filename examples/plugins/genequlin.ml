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

(*
*)


open Why3
open Format

(***************

This file builds some goals using the API and calls
the alt-ergo prover to check them

******************)

(* First, we need to access the Why configuration *)

(* let config = Whyconf.read_config None *)
(* let main = Whyconf.get_main config *)
(* let env = Env.create_env (Lexer.retrieve (Whyconf.loadpath main))  *)

(* let provers = Whyconf.get_provers config *)

(* let alt_ergo =  *)
(*   try *)
(*     Util.Mstr.find "alt-ergo" provers  *)
(*   with Not_found -> *)
(*     eprintf "Prover alt-ergo not installed or not configured@."; *)
(*     exit 0 *)

(* let alt_ergo_driver = Driver.load_driver env alt_ergo.Whyconf.driver *)


open Theory
open Term
open Util

open Ident


let read_channel env filename cin =
  let th_int = Env.find_theory env ["int"] "Int" in
  let leq = ns_find_ls th_int.th_export ["infix <"] in
  let plus_symbol = Theory.ns_find_ls th_int.Theory.th_export ["infix +"] in
  let mult_symbol = Theory.ns_find_ls th_int.Theory.th_export ["infix *"] in

(*

  An arithmetic goal: 2+2 = 4

*)

  let zero = t_const (ConstInt "0") in

  let create_lit lvar k lits _ =
    let left = List.fold_left (fun acc e ->
      let const = string_of_int ((Random.int k) - (k/2)) in
      let monome = t_app mult_symbol [e;t_const(ConstInt const)] Ty.ty_int in
      t_app plus_symbol [acc;monome] Ty.ty_int) zero lvar in
    let rconst = string_of_int ((Random.int k) - (k/2)) in
    f_and_simp lits (f_app leq [left;t_const(ConstInt rconst)]) in

  let create_fmla nvar m k =
    let lvar = mapi (fun _ -> create_vsymbol (id_fresh "x") Ty.ty_int)
      1 nvar in
    let lt = List.map t_var lvar in
    let lits = foldi (create_lit lt k) f_true 1 m in
    f_forall_close lvar [] (f_implies_simp lits f_false) in

  (* let create_task nvar m k = *)
  (*   let task = None in *)
  (*   let task = Task.use_export task th_int in *)
  (*   let goal_id = Decl.create_prsymbol (Ident.id_fresh "goal") in *)
  (*   let fmla = create_fmla nvar m k in *)
  (*   let task = Task.add_prop_decl task Decl.Pgoal goal_id fmla in *)
  (*   task in *)

  let seed = input_line cin in
  let line = ref 0 in
  begin try
    Random.init (int_of_string seed)
  with _ ->
    Printf.eprintf "error file %s line 1\n" filename;
    exit 1
  end;
  let th_uc = create_theory (id_fresh "EqLin") in
  let th_uc = Theory.use_export th_uc th_int in
  let fold th_uc s =
    let nvar,m,k =
      try
        incr line;
        Scanf.sscanf s "%i %i %i" (fun nvar m k -> nvar,m,k)
    with _ -> Printf.eprintf "Error file %s line %i" filename !line;exit 1 in
    let goal_id = Decl.create_prsymbol
      (Ident.id_fresh (Printf.sprintf "goal%i" !line)) in
    let fmla = create_fmla nvar m k in
    let th_uc = Theory.add_prop_decl th_uc Decl.Pgoal goal_id fmla in
    th_uc in
  let th_uc = Sysutil.fold_channel fold th_uc cin in
  Mnm.add "EqLin" (close_theory th_uc) Mnm.empty



let () = Env.register_format "EquLin" ["equlin"] read_channel
