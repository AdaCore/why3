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

let qualid_last = function Qident x | Qdot (_, x) -> x
let use_as q = function Some x -> x | None -> qualid_last q

let read_thy env lenv qualid = match qualid with
  | Qdot (q, {id_str = n}) ->
      Env.read_theory env (Typing.string_list_of_qualid q) n
  | Qident {id_str = n} ->
      try Mstr.find n lenv with Not_found -> Env.read_theory env [] n

let parse_simpl_use env lenv tuc = function
  | Puseexport q ->
      Theory.use_export tuc (read_thy env lenv q)
  | Puseimport (import, q, idas) ->
      let import = import || idas = None in
      let tuc = Theory.open_scope tuc (use_as q idas).id_str in
      let tuc = Theory.use_export tuc (read_thy env lenv q) in
      Theory.close_scope ~import tuc

let add_def ctx c tuc muc flat bl =
  let ctx, dfl = type_defn_list tuc ctx flat bl in
  Debug.dprintf debug "\n@[%a@]@." Coma_syntax.PP.pp_def_block dfl;
  let c, gl = vc_defn c flat dfl in
  let add tuc ({hs_name = {Ident.id_string = s}},f) =
    let pr = Decl.create_prsymbol (Ident.id_fresh ("vc_" ^ s)) in
    Theory.add_prop_decl tuc Decl.Pgoal pr f in
  let tuc = List.fold_left add tuc gl in
  let add tuc (id,vl,f) =
    let ls = create_psymbol id (List.map (fun v -> v.vs_ty) vl) in
    Theory.add_logic_decl tuc [Decl.make_ls_defn ls vl f] in
  let add tuc (h,w,pl,_) = List.fold_left add tuc (vc_spec c h w pl) in
  ctx, c, List.fold_left add tuc dfl, muc

let add_top env lenv menv (ctx,c,tuc,muc) = function
  | Blo b -> add_def ctx c tuc muc false b
  | Def d -> add_def ctx c tuc muc true [d]
  | Pld d ->
      let td0 = muc.Pmodule.muc_theory.Theory.uc_decls in
      let muc = Typing.Unsafe.add_decl muc env menv d in
      let rec catch tuc tdl = if tdl == td0 then tuc else match tdl with
        | {Theory.td_node = Theory.Decl d}::tdl ->
            Theory.add_decl ~warn:false (catch tuc tdl) d
        | {Theory.td_node = Theory.Use th}::tdl ->
            Theory.use_export (catch tuc tdl) th
        | {Theory.td_node = Theory.Meta (m,al)}::tdl ->
            Theory.add_meta (catch tuc tdl) m al
        | {Theory.td_node = Theory.Clone _}::_ | [] ->
            assert false in
      ctx, c, catch tuc muc.Pmodule.muc_theory.Theory.uc_decls, muc
  | Use (loc, u) ->
      let d = match u with
        | Puseexport q -> Ptree.Duseexport q
        | Puseimport (i,q,a) -> Ptree.Duseimport (loc,i,[q,a]) in
      let muc = Typing.Unsafe.add_decl muc env menv d in
      ctx, c, parse_simpl_use env lenv tuc u, muc

let read_module env path (lenv,menv) (nm,dl) =
  let id = Typing.Unsafe.create_user_id nm in
  let muc = Pmodule.create_module env ~path id in
  let ini = ctx0, c_empty, muc.Pmodule.muc_theory, muc in
  let _,_,tuc,muc = List.fold_left (add_top env lenv menv) ini dl in
  Mstr.add nm.id_str (Theory.close_theory tuc) lenv,
  Mstr.add nm.id_str (Pmodule.close_module muc) menv

let read_channel_coma env path file c =
  let ini = Mstr.empty, Mstr.empty in
  let ast = Coma_lexer.parse_channel file c in
  if Debug.test_flag Typing.debug_parse_only then Mstr.empty else
  fst (List.fold_left (read_module env path) ini ast)

let () = Env.register_format Env.base_language "coma" ["coma"] read_channel_coma
  ~desc:"Continuation Machine language"
