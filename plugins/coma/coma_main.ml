(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
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

let debug = Debug.register_flag "coma" ~desc:"[coma] plugin debug flag"

let add_def ctx c muc flat bl =
  let ctx, dfl = type_defn_list muc.Pmodule.muc_theory ctx flat bl in
  Debug.dprintf debug "\n@[%a@]@." Coma_syntax.PP.pp_def_block dfl;
  let c, gl = vc_defn c flat dfl in
  let add muc ({hs_name = {Ident.id_string = s}},f) =
    let pr = Decl.create_prsymbol (Ident.id_fresh ("vc_" ^ s)) in
    let d = Decl.create_prop_decl Decl.Pgoal pr f in
    let d = Pdecl.create_pure_decl d in
    Pmodule.add_pdecl ~vc:false muc d in
  let muc = List.fold_left add muc gl in
  let add muc (id,vl,f) =
    let ls = create_psymbol id (List.map (fun v -> v.vs_ty) vl) in
    let d = Decl.create_logic_decl [Decl.make_ls_defn ls vl f] in
    let d = Pdecl.create_pure_decl d in
    Pmodule.add_pdecl ~vc:false muc d in
  let add muc (h,w,pl,_) = List.fold_left add muc (vc_spec c h w pl) in
  ctx, c, List.fold_left add muc dfl

let add_top env menv (ctx,c,muc) = function
  | Blo b -> add_def ctx c muc false b
  | Def d -> add_def ctx c muc true [d]
  | Pld d ->
      ctx, c, Typing.Unsafe.add_decl muc env menv d
  | Use (loc, u) ->
      let d = match u with
        | Puseexport q -> Ptree.Duseexport q
        | Puseimport (i,q,a) -> Ptree.Duseimport (loc,i,[q,a]) in
      ctx, c, Typing.Unsafe.add_decl muc env menv d

let read_module env path menv (nm,dl) =
  let id = Typing.Unsafe.create_user_id nm in
  let muc = Pmodule.create_module env ~path id in
  let ini = ctx0, c_empty, muc in
  let _,_,muc = List.fold_left (add_top env menv) ini dl in
  Mstr.add nm.id_str (Pmodule.close_module muc) menv

let read_channel_coma env path file c =
  let ast = Coma_lexer.parse_channel file c in
  if Debug.test_flag Typing.debug_parse_only then Mstr.empty else
  List.fold_left (read_module env path) Mstr.empty ast

let () = Env.register_format Pmodule.mlw_language "coma" ["coma"] read_channel_coma
  ~desc:"Continuation Machine language"
