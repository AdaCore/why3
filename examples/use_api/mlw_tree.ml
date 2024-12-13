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

This file builds some MLW modules, using parse trees instead of direct
API calls

******************)

(* BEGIN{buildenv} *)
open Why3
let config : Whyconf.config = Whyconf.init_config None
let main : Whyconf.main = Whyconf.get_main config
let env : Env.env = Env.create_env (Whyconf.loadpath main)
open Ptree
open Ptree_helpers
(* END{buildenv} *)

(* declaration of
  BEGIN{source1}
module M1
  use int.Int
  goal g : 2 + 2 = 4
end
  END{source1}
 *)

(* BEGIN{code1} *)
let mod_M1 =
  (* use int.Int *)
  let use_int_Int = use ~import:false (["int";"Int"]) in
  (* goal g : 2 + 2 = 4 *)
  let g =
    let two = tconst 2 in
    let four = tconst 4 in
    let add_int = qualid ["Int";Ident.op_infix "+"] in
    let two_plus_two = tapp add_int [two ; two] in
    let eq_int = qualid ["Int";Ident.op_infix "="] in
    let goal_term = tapp eq_int  [four ; two_plus_two] in
    Dprop(Decl.Pgoal, ident "g", goal_term)
  in
  (ident "M1",[use_int_Int ; g])
(* END{code1} *)


(* declaration of
  BEGIN{source2}
module M2
  let f (x:int) : int
    requires { x=6 }
    ensures { result=42 }
   = x*7
end
  END{source2}
 *)

(* BEGIN{code2} *)
let eq_symb = qualid [Ident.op_infix "="]
let int_type_id = qualid ["int"]
let int_type = PTtyapp(int_type_id,[])
let mul_int = qualid ["Int";Ident.op_infix "*"]

let mod_M2 =
  (* use int.Int *)
  let use_int_Int = use ~import:false (["int";"Int"]) in
  (* f *)
  let f =
    let id_x = ident "x" in
    let pre = tapp eq_symb [tvar (Qident id_x); tconst 6] in
    let result = ident "result" in
    let post = tapp eq_symb [tvar (Qident result); tconst 42] in
    let spec = {
      sp_pre = [pre];
      sp_post = [Loc.dummy_position,[pat_var result,post]];
      sp_xpost = [];
      sp_reads = [];
      sp_writes = [];
      sp_alias = [];
      sp_variant = [];
      sp_checkrw = false;
      sp_diverge = false;
      sp_partial = false;
    }
    in
    let body = eapp mul_int [evar (Qident id_x); econst 7] in
    let f =
      Efun(one_binder ~pty:int_type "x", None, pat Pwild,
           Ity.MaskVisible, spec, body)
    in
    Dlet(ident "f",false,Expr.RKnone, expr f)
  in
  (ident "M2",[use_int_Int ; f])
(* END{code2} *)


(* declaration of
  BEGIN{source3}
module M3
  let f() : int
     requires { true }
     ensures { result >= 0 }
   = let x = ref 42 in !x
end
  END{source3}
 *)

(* BEGIN{code3} *)
let ge_int = qualid ["Int";Ident.op_infix ">="]

let mod_M3 =
  (* use int.Int *)
  let use_int_Int = use ~import:false (["int";"Int"]) in
  (* use ref.Ref *)
  let use_ref_Ref = use ~import:false (["ref";"Ref"]) in
  (* f *)
  let f =
    let result = ident "result" in
    let post = term(Tidapp(ge_int,[tvar (Qident result);tconst 0])) in
    let spec = {
      sp_pre = [];
      sp_post = [Loc.dummy_position,[pat_var result,post]];
      sp_xpost = [];
      sp_reads = [];
      sp_writes = [];
      sp_alias = [];
      sp_variant = [];
      sp_checkrw = false;
      sp_diverge = false;
      sp_partial = false;
    }
    in
    let body =
      let e1 = eapply (evar (qualid ["Ref";"ref"])) (econst 42) in
      let id_x = ident "x" in
      let qid = qualid ["Ref";Ident.op_prefix "!"] in
      let e2 = eapply (evar qid) (evar (Qident id_x)) in
      expr(Elet(id_x,false,Expr.RKnone,e1,e2))
    in
    let f = Efun(unit_binder (),None,pat Pwild,Ity.MaskVisible,spec,body)
    in
    Dlet(ident "f",false,Expr.RKnone, expr f)
  in
  (ident "M3",[use_int_Int ; use_ref_Ref ; f])
(* END{code3} *)

(* declaration of
  BEGIN{source4}
module M4
  let f (a:array int) : unit
    requires { a.length >= 1 }
    writes { a }
    ensures { a[0] = 42 }
   = a[0] <- 42
end
  END{source4}
 *)

(* BEGIN{code4} *)

let array_int_type = PTtyapp(qualid ["Array";"array"],[int_type])

let length = qualid ["Array";"length"]

let array_get = qualid ["Array"; Ident.op_get ""]

let array_set = qualid ["Array"; Ident.op_set ""]

let mod_M4 =
  (* use int.Int *)
  let use_int_Int = use ~import:false (["int";"Int"]) in
  (* use array.Array *)
  let use_array_Array = use ~import:false (["array";"Array"]) in
  (* decl f *)
  let f =
    let id_a = ident "a" in
    let pre =
      tapp ge_int [tapp length [tvar (Qident id_a)]; tconst 1]
    in
    let post =
      tapp eq_symb [tapp array_get [tvar (Qident id_a); tconst 0];
                       tconst 42]
    in
    let spec = {
      sp_pre = [pre];
      sp_post = [Loc.dummy_position,[pat Pwild,post]];
      sp_xpost = [];
      sp_reads = [];
      sp_writes = [tvar (Qident id_a)];
      sp_alias = [];
      sp_variant = [];
      sp_checkrw = false;
      sp_diverge = false;
      sp_partial = false;
    }
    in
    let body =
      eapp array_set [evar (Qident id_a); econst 0; econst 42]
    in
    let f = Efun(one_binder ~pty:array_int_type "a",
                 None,pat Pwild,Ity.MaskVisible,spec,body)
    in
    Dlet(ident "f", false, Expr.RKnone, expr f)
  in
  (ident "M4",[use_int_Int ; use_array_Array ; f])
(* END{code4} *)

(* The following example is not in the manual
 * it shows how to use Ptree API for global variable declaration
module Mglob
  use int.Int
  val ref x : int
  let f () : unit = x <- x+1
end
*)

let mod_Mglob =
  (* use int.Int *)
  let use_int_Int = use ~import:false (["int";"Int"]) in
  (* x *)
  let id_x,decl_x = global_var_decl int_type "x" in
  (* f *)
  let decl_f =
    let spec = {
      sp_pre = [];
      sp_post = [];
      sp_xpost = [];
      sp_reads = [];
      sp_writes = [tvar (Qident id_x)];
      sp_alias = [];
      sp_variant = [];
      sp_checkrw = false;
      sp_diverge = false;
      sp_partial = false;
    }
    in
    let add_int = qualid ["Int";Ident.op_infix "+"] in
    let xp1 = eapp add_int [evar (Qident id_x) ; econst 1 ] in
    let body = expr (Eassign [ expr (Easref (Qident id_x)), None, xp1  ]) in
    let f = Efun(unit_binder (),None,pat Pwild,Ity.MaskVisible,spec,body) in
    Dlet(ident "f", false, Expr.RKnone, expr f)

  in
  (ident "Mglob",[use_int_Int ; decl_x; decl_f])

(* The following example is not in the manual
 * it shows how to use Ptree API for scope/import declarations
module Mscope
  scope S
      function f (x : int) : int = x
  end

  import S
  goal g : f 2 = 2
end
*)

let mod_Mscope =
  (* use int.Int *)
  let use_int_Int = use ~import:false (["int";"Int"]) in
  (* scope S *)
  let scope_S =
    (* f *)
    let f =
      let logic = {
        ld_loc = Loc.dummy_position;
        ld_ident = ident "f";
        ld_params = [(Loc.dummy_position,Some (ident "x"),false,int_type)] ;
        ld_type = Some int_type;
        ld_def = Some (tvar (Qident (ident "x"))) ;
      } in
      Dlogic([logic])
    in
    Dscope(Loc.dummy_position,false,ident "S",[f])
  in
  (* import S *)
  let import_S = Dimport (qualid ["S"]) in
  (* goal g : f 2 = 2 *)
  let g =
    let two = tconst 2 in
    let eq_int = qualid ["Int";Ident.op_infix "="] in
    let f_of_two = tapp (qualid ["f"]) [two] in
    let goal_term = tapp eq_int [f_of_two ; two] in
    Dprop(Decl.Pgoal,ident "g",goal_term)
  in
  (ident "Mscope",[use_int_Int ; scope_S ; import_S ; g])

(* BEGIN{getmodules} *)
let mlw_file = Modules [mod_M1 ; mod_M2 ; mod_M3 ; mod_M4]
(* END{getmodules} *)
let mlw_file_others = Modules [mod_Mglob ; mod_Mscope]

open Format

(* Printing back the mlw file *)
(* BEGIN{mlwprinter} *)
let () = printf "%a@." (Mlw_printer.pp_mlw_file ~attr:true) mlw_file
(* END{mlwprinter} *)

let () = printf "%a@." (Mlw_printer.pp_mlw_file ~attr:true) mlw_file_others

(* BEGIN{topdownf} *)
let mlw_file_F =
  let uc = F.create () in
  let uc = F.begin_module uc "M5" in
  let uc = F.use uc ~import:false ["int";"Int"] in
  let uc = F.use uc ~import:false ["array";"Array"] in
  let uc = F.begin_let uc "f" (one_binder ~pty:array_int_type "a") in
  let id_a = Qident (ident "a") in
  let pre = tapp ge_int [tapp length [tvar id_a]; tconst 1] in
  let uc = F.add_pre uc pre in
  let uc = F.add_writes uc [tvar id_a] in
  let post =
    tapp eq_symb [tapp array_get [tvar id_a; tconst 0];
                  tconst 42]
  in
  let uc = F.add_post uc post in
  let body = eapp array_set [evar id_a; econst 0; econst 42] in
  let uc = F.add_body uc body in
  let uc = F.end_module uc in
  F.get_mlw_file uc
(* END{topdownf} *)

let () = printf "%a@." (Mlw_printer.pp_mlw_file ~attr:true) mlw_file_F

(* BEGIN{topdowni} *)
let mlw_file_I =
  I.begin_module "M6";
  I.use ~import:false ["int";"Int"];
  I.use ~import:false ["array";"Array"];
  I.begin_let "f" (one_binder ~pty:array_int_type "a");
  let id_a = Qident (ident "a") in
  let pre = tapp ge_int [tapp length [tvar id_a]; tconst 1] in
  I.add_pre pre;
  I.add_writes [tvar id_a];
  let post =
    tapp eq_symb [tapp array_get [tvar id_a; tconst 0];
                  tconst 42]
  in
  I.add_post post;
  let body = eapp array_set [evar id_a; econst 0; econst 42] in
  I.add_body body;
  I.end_module ();
  I.get_mlw_file ()
(* END{topdowni} *)

let () = printf "%a@." (Mlw_printer.pp_mlw_file ~attr:true) mlw_file_I

(* BEGIN{typemodules} *)
let mods = Typing.type_mlw_file env [] "myfile.mlw" mlw_file
(* END{typemodules} *)
let mod_F = Typing.type_mlw_file env [] "myFfile.mlw" mlw_file_F
let mod_I = Typing.type_mlw_file env [] "myIfile.mlw" mlw_file_I
let mods_others = Typing.type_mlw_file env [] "myotherfile.mlw" mlw_file_others

(* BEGIN{typemoduleserror} *)
let _mods =
  try
    Typing.type_mlw_file env [] "myfile.mlw" mlw_file
  with Loc.Located (loc, e) -> (* A located exception [e] *)
    let msg = asprintf "%a" Exn_printer.exn_printer e in
    printf "%a@."
      (Mlw_printer.with_marker ~msg loc (Mlw_printer.pp_mlw_file ~attr:true))
      mlw_file;
    exit 1
(* END{typemoduleserror} *)

(* Checking the VCs *)

(* BEGIN{checkingvcs} *)
let my_tasks : Task.task list =
  let mods =
    Wstdlib.Mstr.fold
      (fun _ m acc ->
       List.rev_append
         (Task.split_theory m.Pmodule.mod_theory None None) acc)
      mods []
  in List.rev mods



let provers : Whyconf.config_prover Whyconf.Mprover.t =
  Whyconf.get_provers config

(* default resource limits *)
let limits =
  Call_provers.{empty_limits with
                limit_time = Whyconf.timelimit main;
                limit_mem = Whyconf.memlimit main }

let alt_ergo : Whyconf.config_prover =
  let fp = Whyconf.parse_filter_prover "Alt-Ergo" in
  let provers = Whyconf.filter_provers config fp in
  if Whyconf.Mprover.is_empty provers then begin
    eprintf "Prover Alt-Ergo not installed or not configured@.";
    exit 1
  end else
    snd (Whyconf.Mprover.max_binding provers)

let alt_ergo_driver : Driver.driver =
  try
    Driver.load_driver_for_prover main env alt_ergo
  with e ->
    eprintf "Failed to load driver for alt-ergo: %a@."
      Exn_printer.exn_printer e;
    exit 1

let () =
  List.iteri (fun i t ->
      let call =
        Driver.prove_task ~limits ~config:main
          ~command:alt_ergo.Whyconf.command alt_ergo_driver t in
      let r = Call_provers.wait_on_call call in
      printf "@[On task %d, alt-ergo answers %a@." (succ i)
        (Call_provers.print_prover_result ?json:None) r)
    my_tasks
(* END{checkingvcs} *)

(*
Local Variables:
compile-command: "make -C ../.. test-api-mlw_tree"
End:
*)
