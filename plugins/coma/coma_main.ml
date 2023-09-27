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

let debug = Debug.register_flag "coma" ~desc:"coma plugin debug flag"

let mk_goal tuc s e =
  let prs = Decl.create_prsymbol (Ident.id_fresh ("vc_" ^ s)) in
  Theory.add_prop_decl tuc Decl.Pgoal prs (vc e)

(* let add_vc tuc (s, _, _, d) = mk_goal tuc s.hs_name.id_string d *)

let add_vcf tuc name d = mk_goal tuc name d

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

let read_channel env path file c =

  let uses, ast = Coma_lexer.parse_channel file c in

  let tuc = Theory.create_theory ~path (Ident.id_fresh "Coma") in
  let tuc = Theory.use_export tuc Theory.bool_theory in
  let tuc = List.fold_left (parse_simpl_use env) tuc uses in

  let factor def e = {
    pexpr_desc = PEdef (e, false, [def]);
    pexpr_loc  = def.pdefn_loc;
  } in

  let eany = { pexpr_loc = Loc.dummy_position ; pexpr_desc = PEany } in
  let astf = List.fold_right factor ast eany in

  let astf = type_prog tuc ctx0 astf in

  Debug.dprintf debug "\n@.@[%a@]\n@." Coma_syntax.pp_expr astf;

  (* let _ctx, ast = Lists.map_fold_left (type_defn tuc) ctx0 ast in
     let ast = (create_hsymbol (id_fresh "dummy"), [], [], _expr2) :: ast in
     let tuc = List.fold_left add_vc tuc ast in *)

  let tuc = add_vcf tuc file astf in

  (* let tuc = mk_goal tuc "expr1" expr1 in
     let tuc = mk_goal tuc "expr2" expr2 in *)

  Wstdlib.Mstr.singleton "Coma" (Theory.close_theory tuc)

let () = Env.register_format Env.base_language "coma" ["coma"] read_channel
  ~desc:"Continuation Machine language"
