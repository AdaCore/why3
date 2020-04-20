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

open Why3
let config : Whyconf.config =
  Whyconf.(load_default_config_if_needed (read_config None))
let main : Whyconf.main = Whyconf.get_main config
let env : Env.env = Env.create_env (Whyconf.loadpath main)
open Ptree

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

let mk_var id = mk_term (Tident (Qident id))

let param1 id ty = [Loc.dummy_position, Some id, false, Some ty]

let mk_const i =
  Constant.(ConstInt Number.{ il_kind = ILitDec; il_int = BigInt.of_int i })

let mk_tconst i = mk_term (Tconst (mk_const i))

let mk_econst i = mk_expr (Econst (mk_const i))

let mk_tapp f l = mk_term (Tidapp(f,l))

let mk_eapp f l = mk_expr (Eidapp(f,l))

let mk_evar x = mk_expr(Eident(Qident x))

(*BEGIN{helper2}*)
(* ... *)
let pat_wild = mk_pat Pwild

let mk_ewhile e1 i v e2 = mk_expr (Ewhile (e1,i,v,e2))
(*END{helper2}*)

(* declaration of
  BEGIN{source1}
module M1
  use int.Int
  use ref.Refint
  let f [@infer] (x:ref int) : unit
    requires { !x <= 100 }
    ensures  { !x = 100 }
  = while (!x < 100) do
      variant { 100 - !x }
      incr x
    done
end
  END{source1}
 *)

(* BEGIN{code1} *)
let int_type_id  = mk_qualid ["int"]
let int_type     = PTtyapp(int_type_id,[])
let ref_int_type = PTtyapp (mk_qualid ["ref"], [int_type])
let ref_access   = mk_qualid ["Refint"; Ident.op_prefix "!"]
let ref_assign   = mk_qualid ["Refint"; Ident.op_infix ":="]
let ref_int_incr = mk_qualid ["Refint"; "incr"]
let l_int        = mk_qualid ["Int";Ident.op_infix "<"]
let le_int       = mk_qualid ["Int";Ident.op_infix "<="]
let plus_int     = mk_qualid ["Int";Ident.op_infix "+"]
let minus_int    = mk_qualid ["Int";Ident.op_infix "-"]
let eq_symb      = mk_qualid [Ident.op_infix "="]

let mod_M1 =
  (* use int.Int *)
  let use_int_Int    = use_import (["int";"Int"]) in
  let use_ref_Refint = use_import (["ref";"Refint"]) in
  (* f *)
  let f =
    let id_x  = mk_ident "x" in
    let var_x = mk_var id_x in
    let t_x   = mk_tapp ref_access [var_x] in
    let pre   = mk_tapp le_int [t_x; mk_tconst 100] in
    let post  = mk_tapp eq_symb [t_x; mk_tconst 100] in
    let spec  = {
      sp_pre     = [pre];
      sp_post    = [Loc.dummy_position,[pat_wild, post]];
      sp_xpost   = [];
      sp_reads   = [];
      sp_writes  = [];
      sp_alias   = [];
      sp_variant = [];
      sp_checkrw = false;
      sp_diverge = false;
      sp_partial = false;
    }
    in
    let var_x      = mk_evar id_x in
    (* !x *)
    let e_x        = mk_eapp ref_access [var_x] in
    (* !x < 100 *)
    let while_cond = mk_eapp l_int [e_x; mk_econst 100] in
    (* 100 - !x *)
    let while_vari = mk_tapp minus_int [mk_tconst 100; t_x], None in
    (* incr x *)
    let incr       = mk_eapp ref_int_incr [var_x] in
    (* while (!x < 100) do variant { 100 - !x } incr x done *)
    let while_loop = mk_ewhile while_cond [] [while_vari] incr in
    let f =
      Efun(param1 id_x ref_int_type, None, mk_pat Pwild,
           Ity.MaskVisible, spec, while_loop)
    in
    let attr = ATstr (Ident.create_attribute "infer") in
    let id = { (mk_ident "f") with id_ats = [attr] } in
    Dlet(id,false,Expr.RKnone, mk_expr f)
  in
  (mk_ident "M1",[use_int_Int; use_ref_Refint; f])
(* END{code1} *)

(*BEGIN{flags}*)
(* let () = Debug.set_flag Infer_cfg.infer_print_ai_result *)
(* let () = Debug.set_flag Infer_cfg.infer_print_cfg *)
(* let () = Debug.set_flag Infer_loop.print_inferred_invs *)
(*END{flags}*)

let mlw_file = Modules [ mod_M1 ]

(* Printing back the mlw file *)

let () = Format.printf "%a@." Mlw_printer.pp_mlw_file mlw_file

let mods =
  try
    Typing.type_mlw_file env [] "myfile.mlw" mlw_file
  with Loc.Located (loc, e) -> (* A located exception [e] *)
    let msg = Format.asprintf "%a" Exn_printer.exn_printer e in
    Format.printf "%a@."
      (Mlw_printer.with_marker ~msg loc Mlw_printer.pp_mlw_file)
      mlw_file;
    exit 1

(* Checking the VCs *)

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
    exit 1
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

(* make sure the why3 lib is installed: do "make install-lib"
   in the why3 root directory *)
(*
Local Variables:
compile-command: "ocamlfind ocamlopt -linkpkg -package why3 mlw_tree1.ml"
End:
*)
