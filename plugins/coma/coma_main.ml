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
  | _ -> assert false

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

let add_def (c,tuc) (s,flat,dfl) =
  let c,f = vc_defn c flat dfl in
  let prs = Decl.create_prsymbol (Ident.id_fresh ("vc_" ^ s)) in
  c, Theory.add_prop_decl tuc Decl.Pgoal prs f

let read_channel_coma env path file c =
  let uses, ast = Coma_lexer.parse_channel file c in
  let tuc = Theory.create_theory ~path (Ident.id_fresh "Coma") in
  let tuc = Theory.use_export tuc Theory.bool_theory in
  let tuc = List.fold_left (parse_simpl_use env) tuc uses in
  let _, ast =
    List.fold_left_map
      (fun ctx ->
         function Blo b -> type_defn_list tuc ctx false b
                | Def d -> type_defn_list tuc ctx true [d])
      ctx0 ast in
  List.iter (Debug.dprintf debug "\n@[%a@]@." Coma_syntax.PP.pp_def_block) ast;
  let ast =
    List.map
      (fun d ->
        let {hs_name}, _, _, _ = List.hd d in
        hs_name.Ident.id_string, false, d)
      ast in
  let _, tuc = List.fold_left add_def (c_empty, tuc) ast in
  Wstdlib.Mstr.singleton "Coma" (Theory.close_theory tuc)

let () = Env.register_format Env.base_language "coma" ["coma"] read_channel_coma
  ~desc:"Continuation Machine language"
