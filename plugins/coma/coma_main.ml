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
open Term
open Coma_logic
open Coma_syntax
open Coma_typing
open Coma_vc
open Ptree

let debug = Debug.register_flag "coma" ~desc:"[coma] plugin debug flag"

let qualid_last = function Qident x | Qdot (_, x) -> x
let use_as q = function Some x -> x | None -> qualid_last q

let read_thy env qualid = match qualid with
  | Qdot (q, id) ->
      Env.read_theory env (Typing.string_list_of_qualid q) id.id_str
  | Qident id ->
      Env.read_theory env [] id.id_str

let parse_simpl_use env tuc = function
  | Puseexport q ->
      let th = read_thy env q in
      Theory.use_export tuc th
  | Puseimport (import, q, idas) ->
      let import = import || idas = None in
      let tuc = Theory.open_scope tuc (use_as q idas).id_str in
      let th = read_thy env q in
      let tuc = Theory.use_export tuc th in
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

let add_top env (ctx,c,tuc,muc) = function
  | Blo b -> add_def ctx c tuc muc false b
  | Def d -> add_def ctx c tuc muc true [d]
  | Pld d ->
      let td0 = muc.Pmodule.muc_theory.Theory.uc_decls in
      let muc = Typing.Unsafe.add_decl muc env Wstdlib.Mstr.empty d in
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
      let muc = Typing.Unsafe.add_decl muc env Wstdlib.Mstr.empty d in
      ctx, c, parse_simpl_use env tuc u, muc

let read_channel_coma env path file c =
  let ast = Coma_lexer.parse_channel file c in
  let muc = Pmodule.create_module env ~path (Ident.id_fresh "Coma") in
  let ini = ctx0, c_empty, muc.Pmodule.muc_theory, muc in
  let _,_,tuc,_ = List.fold_left (add_top env) ini ast in
  Wstdlib.Mstr.singleton "Coma" (Theory.close_theory tuc)

let () = Env.register_format Env.base_language "coma" ["coma"] read_channel_coma
  ~desc:"Continuation Machine language"
