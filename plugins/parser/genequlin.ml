(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(*
*)


open Why3

(**************)
(*

  This plugin generate randomly linear arithmetic problems from a
  source file.Here an exemple :
========
2
5 5 5
15 5 5
5 15 5
5 5 15
========

  The first line give the seed to use. Each other lines corresond to one goal :
    - the first number give the number of variables
    - the second the number of equation
    - the third the absolute maximun of the constants used

  For compiling it :
   make example_plugins.opt
   cp examples/plugins/genequlin.cmxs plugins
   bin/why3config --detect-plugins

  For testing it :
   bin/why3ide examples/plugins/test.equlin

*)

open Theory
open Term
open Wstdlib

open Ident

(** read one line *)
let scanf s =
  let invar = String.index_from s 0 ' ' in
  let im = String.index_from s (invar+1) ' ' in
  int_of_string (String.sub s 0 invar),
  int_of_string (String.sub s (invar+1) (im-(invar+1))),
  int_of_string (String.sub s (im+1) ((String.length s) - (im+1)))


(** the main function *)
let read_channel env path filename cin =
  (* Find the int theory and the needed operation *)
  let th_int = Env.read_theory env ["int"] "Int" in
  let leq = ns_find_ls th_int.th_export [op_infix "<"] in
  let plus_symbol = ns_find_ls th_int.th_export [op_infix "+"] in
  let neg_symbol = ns_find_ls th_int.th_export [op_prefix "-"] in
  let mult_symbol = ns_find_ls th_int.th_export [op_infix "*"] in

  let zero = t_nat_const 0 in
  let t_int_const n =
    if n >= 0 then t_nat_const n else
      t_app_infer neg_symbol [t_nat_const (-n)]
  in

  (* create a contraint : polynome <= constant *)
  let create_lit lvar k lits _ =
    let left = List.fold_left (fun acc e ->
      let const = (Random.int k) - (k/2) in
      let monome = t_app mult_symbol [e;t_int_const const]
        (Some Ty.ty_int) in
      t_app plus_symbol [acc;monome] (Some Ty.ty_int)) zero lvar in
    let rconst = (Random.int k) - (k/2) in
    t_and_simp lits (t_app leq [left;t_int_const rconst] None) in

  (* create a set of constraints *)
  let create_fmla nvar m k =
    let lvar = Util.mapi (fun _ -> create_vsymbol (id_fresh "x") Ty.ty_int)
      1 nvar in
    let lt = List.map t_var lvar in
    let lits = Util.foldi (create_lit lt k) t_true 1 m in
    t_forall_close lvar [] (t_implies_simp lits t_false) in

  (* read the first line *)
  let line = ref 0 in
  begin try
    let seed = input_line cin in
    Random.init (int_of_string seed)
  with _ ->
    Printf.eprintf "error file %s line 1\n" filename;
    exit 1
  end;
  (* Create the theory *)
  let th_uc_loc = Loc.user_position filename 1 0 0 in
  let th_uc = create_theory ~path (id_user "EqLin" th_uc_loc) in
  let th_uc = Theory.use_export th_uc th_int in
  (* Read one line and add it to the theory *)
  let fold th_uc s =
    let nvar,m,k =
      try
        incr line;
        (* Dont use scanf because I don't know how to link it in plugin
            (without segfault) *)
        (* Scanf.sscanf s "%i %i %i" (fun nvar m k -> nvar,m,k) *)
        scanf s
    with _ -> Printf.eprintf "Error file %s line %i" filename !line;exit 1 in
    let loc = Loc.user_position filename (!line+1) 0 (String.length s) in
    let goal_id = Decl.create_prsymbol
      (Ident.id_user (Printf.sprintf "goal%i" !line) loc) in
    let fmla = create_fmla nvar m k in
    let th_uc = Theory.add_prop_decl th_uc Decl.Pgoal goal_id fmla in
    th_uc in
  (* Read all the file *)
  let th_uc = Sysutil.fold_channel fold th_uc cin in
  (* Return the map with the theory *)
  Mstr.singleton "EquLin" (close_theory th_uc)

let () = Env.register_format Env.base_language "equlin" ["equlin"] read_channel
  ~desc:"@[<hov>Generate@ random@ linear@ arithmetic@ problems.@ \
    The@ first@ line@ gives@ the@ seed.@ Each@ other@ line@ \
    describes@ a@ goal@ and@ contains@ three@ numbers:@]@\n  \
    @[- @[the@ number@ of@ variables@]@\n\
      - @[the@ number@ of@ equations@]@\n\
      - @[the@ maximum@ absolute@ value@ of@ coefficients.@]@]"
