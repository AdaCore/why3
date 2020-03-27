(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
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
let config : Whyconf.config = Whyconf.read_config None
let main : Whyconf.main = Whyconf.get_main config
let env : Env.env = Env.create_env (Whyconf.loadpath main)
open Ptree
(* END{buildenv} *)

(* BEGIN{helper1} *)
let mk_ident s = { id_str = s; id_ats = []; id_loc = Loc.dummy_position }

let mk_qualid l =
  let rec aux l =
    match l with
      | [] -> assert false
      | [x] -> Qident(mk_ident x)
      | x::r -> Qdot(aux r,mk_ident x)
  in
  aux (List.rev l)

let use_import l =
  let qid_id_opt = (mk_qualid l, None) in
  Duseimport(Loc.dummy_position,false,[qid_id_opt])

let mk_expr e = { expr_desc = e; expr_loc = Loc.dummy_position }

let mk_term t = { term_desc = t; term_loc = Loc.dummy_position }

let mk_pat p = { pat_desc = p; pat_loc = Loc.dummy_position }
let pat_var id = mk_pat (Pvar id)

let mk_var id = mk_term (Tident (Qident id))

let param0 = [Loc.dummy_position, None, false, Some (PTtuple [])]
let param1 id ty = [Loc.dummy_position, Some id, false, Some ty]

let mk_const i =
  Constant.(ConstInt Number.{ il_kind = ILitDec; il_int = BigInt.of_int i })

let mk_tconst i = mk_term (Tconst (mk_const i))

let mk_econst i = mk_expr (Econst (mk_const i))

let mk_tapp f l = mk_term (Tidapp(f,l))

let mk_eapp f l = mk_expr (Eidapp(f,l))

let mk_evar x = mk_expr(Eident(Qident x))
(* END{helper1} *)

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
  let use_int_Int = use_import (["int";"Int"]) in
  (* goal g : 2 + 2 = 4 *)
  let g =
    let two = mk_tconst 2 in
    let four = mk_tconst 4 in
    let add_int = mk_qualid ["Int";Ident.op_infix "+"] in
    let two_plus_two = mk_tapp add_int [two ; two] in
    let eq_int = mk_qualid ["Int";Ident.op_infix "="] in
    let goal_term = mk_tapp eq_int  [four ; two_plus_two] in
    Dprop(Decl.Pgoal,mk_ident "g",goal_term)
  in
  (mk_ident "M1",[use_int_Int ; g])
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
let eq_symb = mk_qualid [Ident.op_infix "="]
let int_type_id = mk_qualid ["int"]
let int_type = PTtyapp(int_type_id,[])
let mul_int = mk_qualid ["Int";Ident.op_infix "*"]

let mod_M2 =
  (* use int.Int *)
  let use_int_Int = use_import (["int";"Int"]) in
  (* f *)
  let f =
    let id_x = mk_ident "x" in
    let pre = mk_tapp eq_symb [mk_var id_x; mk_tconst 6] in
    let result = mk_ident "result" in
    let post = mk_tapp eq_symb [mk_var result; mk_tconst 42] in
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
    let body = mk_eapp mul_int [mk_evar id_x; mk_econst 7] in
    let f =
      Efun(param1 id_x int_type, None, mk_pat Pwild,
           Ity.MaskVisible, spec, body)
    in
    Dlet(mk_ident "f",false,Expr.RKnone, mk_expr f)
  in
  (mk_ident "M2",[use_int_Int ; f])
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
let ge_int = mk_qualid ["Int";Ident.op_infix ">="]

let mod_M3 =
  (* use int.Int *)
  let use_int_Int = use_import (["int";"Int"]) in
  (* use ref.Ref *)
  let use_ref_Ref = use_import (["ref";"Ref"]) in
  (* f *)
  let f =
    let result = mk_ident "result" in
    let post = mk_term(Tidapp(ge_int,[mk_var result;mk_tconst 0])) in
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
      let e1 = mk_eapp (mk_qualid ["Ref";"ref"]) [mk_econst 42] in
      let id_x = mk_ident "x" in
      let qid = mk_qualid ["Ref";Ident.op_prefix "!"] in
      let e2 = mk_eapp qid [mk_evar id_x] in
      mk_expr(Elet(id_x,false,Expr.RKnone,e1,e2))
    in
    let f = Efun(param0,None,mk_pat Pwild,Ity.MaskVisible,spec,body)
    in
    Dlet(mk_ident "f",false,Expr.RKnone, mk_expr f)
  in
  (mk_ident "M3",[use_int_Int ; use_ref_Ref ; f])
(* END{code3} *)

(* declaration of
  BEGIN{source4}
module M4
  let f (a:array int) : unit
    requires { a.length >= 1 }
    ensures { a[0] = 42 }
   = a[0] <- 42
end
  END{source4}
 *)

(* BEGIN{code4} *)

let array_int_type = PTtyapp(mk_qualid ["Array";"array"],[int_type])

let length = mk_qualid ["Array";"length"]

let array_get = mk_qualid ["Array"; Ident.op_get ""]

let array_set = mk_qualid ["Array"; Ident.op_set ""]

let mod_M4 =
  (* use int.Int *)
  let use_int_Int = use_import (["int";"Int"]) in
  (* use array.Array *)
  let use_array_Array = use_import (["array";"Array"]) in
  (* use f *)
  let f =
    let id_a = mk_ident "a" in
    let pre =
      mk_tapp ge_int [mk_tapp length [mk_var id_a]; mk_tconst 1]
    in
    let post =
      mk_tapp eq_symb [mk_tapp array_get [mk_var id_a; mk_tconst 0];
                       mk_tconst 42]
    in
    let spec = {
      sp_pre = [pre];
      sp_post = [Loc.dummy_position,[mk_pat Pwild,post]];
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
      mk_eapp array_set [mk_evar id_a; mk_econst 0; mk_econst 42]
    in
    let f = Efun(param1 id_a array_int_type,
                 None,mk_pat Pwild,Ity.MaskVisible,spec,body)
    in
    Dlet(mk_ident "f", false, Expr.RKnone, mk_expr f)
  in
  (mk_ident "M4",[use_int_Int ; use_array_Array ; f])
(* END{code4} *)

(* The following example is not in the manual
 * it shows how to use Ptree API for scope/import declarations
module M5
  scope S
      function f (x : int) : int = x
  end

  import S
  goal g : f 2 = 2
end
*)

let mod_M5 =
  (* use int.Int *)
  let use_int_Int = use_import (["int";"Int"]) in
  (* scope S *)
  let scope_S =
    (* f *)
    let f =
      let logic = {
        ld_loc = Loc.dummy_position;
        ld_ident = mk_ident "f";
        ld_params = [(Loc.dummy_position,Some (mk_ident "x"),false,int_type)] ;
        ld_type = Some int_type;
        ld_def = Some (mk_var (mk_ident "x")) ;
      } in
      Dlogic([logic])
    in
    Dscope(Loc.dummy_position,false,mk_ident "S",[f])
  in
  (* import S *)
  let import_S = Dimport (mk_qualid ["S"]) in
  (* goal g : f 2 = 2 *)
  let g =
    let two = mk_tconst 2 in
    let eq_int = mk_qualid ["Int";Ident.op_infix "="] in
    let f_of_two = mk_tapp (mk_qualid ["f"]) [two] in
    let goal_term = mk_tapp eq_int [f_of_two ; two] in
    Dprop(Decl.Pgoal,mk_ident "g",goal_term)
  in
  (mk_ident "M5",[use_int_Int ; scope_S ; import_S ; g])

(* BEGIN{getmodules} *)
let mlw_file = Modules [mod_M1 ; mod_M2 ; mod_M3 ; mod_M4]
(* END{getmodules} *)

(* Printing back the mlw file *)

let () = Format.printf "%a@." Mlw_printer.pp_mlw_file mlw_file

(* BEGIN{typemodules} *)
let mods = Typing.type_mlw_file env [] "myfile.mlw" mlw_file
(* END{typemodules} *)

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

open Format

let () =
  printf "Tasks are:@.";
  let _ =
    List.fold_left
      (fun i t -> printf "Task %d: %a@." i Pretty.print_task t; i+1)
      1 my_tasks
  in ()

let provers : Whyconf.config_prover Whyconf.Mprover.t =
  Whyconf.get_provers config

let alt_ergo : Whyconf.config_prover =
  let fp = Whyconf.parse_filter_prover "Alt-Ergo" in
  (** all provers that have the name "Alt-Ergo" *)
  let provers = Whyconf.filter_provers config fp in
  if Whyconf.Mprover.is_empty provers then begin
    eprintf "Prover Alt-Ergo not installed or not configured@.";
    exit 0
  end else
    snd (Whyconf.Mprover.max_binding provers)

let alt_ergo_driver : Driver.driver =
  try
    Whyconf.load_driver main env alt_ergo.Whyconf.driver []
  with e ->
    eprintf "Failed to load driver for alt-ergo: %a@."
      Exn_printer.exn_printer e;
    exit 1

let () =
  let _ =
    List.fold_left
      (fun i t ->
       let r =
         Call_provers.wait_on_call
           (Driver.prove_task ~limit:Call_provers.empty_limit
                              ~command:alt_ergo.Whyconf.command
                              alt_ergo_driver t)
       in
       printf "@[On task %d, alt-ergo answers %a@."
              i (Call_provers.print_prover_result ~json_model:false) r;
       i+1
      )
      1 my_tasks
  in ()
(* END{checkingvcs} *)

(*
Local Variables:
compile-command: "ocamlfind ocaml ../../lib/why3/why3.cma mlw_tree.ml"
End:
*)
