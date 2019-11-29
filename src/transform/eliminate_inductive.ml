(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ident
open Term
open Decl

let log acc (ps,_) = create_param_decl ps :: acc
let axm acc (pr,f) = create_prop_decl Paxiom pr f :: acc
let imp acc (_,al) = List.fold_left axm acc al

let exi vl (_,f) =
  let rec descend f = match f.t_node with
    | Tquant (Tforall,f) ->
        let vl,tl,f = t_open_quant f in
        t_exists_close vl tl (descend f)
    | Tbinop (Timplies,g,f) ->
        t_and g (descend f)
    | Tapp (_,tl) ->
        let marry acc v t = t_and_simp acc (t_equ v t) in
        List.fold_left2 marry t_true vl tl
    | Tlet (t, tb) ->
        let v, f = t_open_bound tb in
        t_let_close v t (descend f)
    | _ ->
        assert false (* ensured by Decl.create_ind_decl *)
  in
  descend f

let inv acc (ps,al) =
  let vl = List.map (create_vsymbol (id_fresh "z")) ps.ls_args in
  let tl = List.map t_var vl in
  let hd = ps_app ps tl in
  let dj = Lists.map_join_left (exi tl) t_or al in
  let hsdj =
    Simplify_formula.fmla_remove_quant ~keep_model_vars:false (t_implies hd dj)
  in
  let ax = t_forall_close vl [] hsdj in
  let nm = id_derive (ps.ls_name.id_string ^ "_inversion") ps.ls_name in
  create_prop_decl Paxiom (create_prsymbol nm) ax :: acc

let elim d = match d.d_node with
  | Dind (_, il) ->
      let dl = List.fold_left log [] il in
      let dl = List.fold_left imp dl il in
      let dl = List.fold_left inv dl il in
      List.rev dl
  | _ -> [d]

let eliminate_inductive = Trans.decl elim None

let () = Trans.register_transform "eliminate_inductive" eliminate_inductive
  ~desc:"Replace@ inductive@ predicates@ by@ (incomplete)@ axiomatic@ \
         definitions,@ i.e.@ construction@ axioms@ and@ an@ inversion@ axiom."
