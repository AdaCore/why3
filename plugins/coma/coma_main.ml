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

open Why3
open Wstdlib
open Term
open Coma_logic
open Coma_syntax
open Coma_typing
open Ptree
open Pmodule

let debug = Debug.register_flag "coma" ~desc:"[coma] plugin debug flag"

let coma_language = Env.register_language Pmodule.mlw_language (Mstr.map snd)

let read_module env path s =
  let path = if path = [] then ["why3"; s] else path in
  try let mm = Env.read_library coma_language env path in
      Mstr.find_exn (Pmodule.ModuleNotFound (path, s)) s mm
  with Env.InvalidFormat _ ->
      let mm = Env.read_library Pmodule.mlw_language env path in
      c_empty, Mstr.find_exn (Pmodule.ModuleNotFound (path, s)) s mm

let find_module env cenv q = match q with
  | Qident {id_str = nm} ->
      (try Mstr.find nm cenv with Not_found -> read_module env [] nm)
  | Qdot (p, {id_str = nm}) ->
      read_module env (Typing.string_list_of_qualid p) nm

let eval_match = let pr = Decl.create_prsymbol (Ident.id_fresh "dummy'pr") in
  fun muc vl f -> try Eval_match.eval_match ~keep_trace:false muc.muc_known f
    with Not_found -> (* make a throwout muc with the required imports *)
      let muc = Pmodule.add_pdecl ~vc:false muc @@ Pdecl.create_pure_decl @@
        Decl.create_prop_decl Decl.Pgoal pr @@ Term.t_forall_close vl [] f in
      Eval_match.eval_match ~keep_trace:false muc.muc_known f

let add_def (c,muc) (flat,dfl) =
  Debug.dprintf debug "\n@[%a@]@." Coma_syntax.PP.pp_def_block dfl;
  let c, gl = vc_defn c flat dfl in
  let add muc ({hs_name = {Ident.id_string = s}}, f) =
    let pr = Decl.create_prsymbol (Ident.id_fresh ("vc_" ^ s)) in
    let d = Decl.create_prop_decl Decl.Pgoal pr (eval_match muc [] f) in
    Pmodule.add_pdecl ~vc:false muc (Pdecl.create_pure_decl d) in
  let muc = List.fold_left add muc gl in
  let add muc (id, vl, f) =
    let ls = create_psymbol id (List.map (fun v -> v.vs_ty) vl) in
    let d = Decl.make_ls_defn ls vl (eval_match muc vl f) in
    let d = Decl.create_logic_decl [d] in
    Pmodule.add_pdecl ~vc:false muc (Pdecl.create_pure_decl d) in
  let add muc (h,_,_,_) = List.fold_left add muc (vc_spec c h) in
  c, List.fold_left add muc dfl

let add_def c muc flat bl =
  let muc, dfl = type_defn_list muc flat bl in
  List.fold_left add_def (c, muc) dfl

let add_top env cenv menv (c, muc) = function
  | Blo b -> add_def c muc false b
  | Mlw d ->
      c, Typing.Unsafe.add_decl muc env menv d
  | Use (Puseexport q) ->
      let n,m = find_module env cenv q in
      c_merge c n, Pmodule.use_export muc m
  | Use (Puseimport (import, q, a)) ->
      let n,m = find_module env cenv q in
      let import = import || a = None in
      let id = match a,q with
        | Some id, _
        | None, Qident id
        | None, Qdot (_, id) -> id in
      let muc = Pmodule.open_scope muc id.id_str in
      let muc = Pmodule.use_export muc m in
      c_merge c n, Pmodule.close_scope ~import muc

let read_module env path (cenv, menv) (nm, dl) =
  let id = Typing.Unsafe.create_user_id nm in
  let muc = Pmodule.create_module env ~path id in
  let add_top = add_top env cenv menv in
  let c,muc = List.fold_left add_top (c_empty, muc) dl in
  let m = Pmodule.close_module muc and nm = nm.id_str in
  Mstr.add nm (c,m) cenv, Mstr.add nm m menv

let read_channel_coma env path file c =
  let ast = Coma_lexer.parse_channel file c in
  if Debug.test_flag Typing.debug_parse_only then Mstr.empty else
  fst (List.fold_left (read_module env path) (Mstr.empty, Mstr.empty) ast)

let () = Env.register_format coma_language "coma" ["coma"] read_channel_coma
  ~desc:"Continuation Machine language"
