open Domain
open Infer_why3
open Term
open Ity

module Make(S:sig
    module      TDom : TERM_DOMAIN
    module Infer_why3 : INFERWHY3
  end): TERM_DOMAIN = struct

  module TDom = S.TDom

  include TDom

  let quant_var, pv =
    let ident_ret = Ident.id_fresh "w" in
    let v = create_pvsymbol ident_ret ity_int in
    t_var v.pv_vs, v

  let create_manager () =
    let man = create_manager () in
    TDom.add_variable_to_env man pv;
    man

  let is_in t myt =
    (* FIX ME *)
    let found = ref false in
    let rec is_in myt =
      if t_equal t myt then found := true;
      t_map is_in myt
    in
    is_in myt |> ignore;
    !found

  let rec descend_quantifier q t =
    match t.t_node with
    | Tbinop (Tand, a, b) ->
       let ia = is_in q a
       and ib = is_in q b in
       if ia && ib then
         let var = match q.t_node with
           | Tvar v  -> v
           | _ -> assert false
         in
         t_quant Tforall (t_close_quant [var] [] t)
       else if ia && not ib then
         t_and_simp (descend_quantifier q a) b
       else if not ia && ib then
         t_and_simp a (descend_quantifier q b)
       else
         t_and_simp a b
    | _ ->
       let var = match q.t_node with
         | Tvar v -> v
         | _ -> assert false
       in
       t_quant Tforall (t_close_quant [var] [] t)

  let to_term man t =
    let t = TDom.to_term man t in
    descend_quantifier quant_var t

  let rec meet_term man term elt =
    match term.t_node with
    | Tbinop (Tor, a, b) ->
       join man (meet_term man a elt) (meet_term man b elt)
    | Tbinop (Tand, a, b) ->
       meet_term man b (meet_term man a elt)
    | Tbinop (Timplies, a, b) ->
       meet_term man (t_or (t_not a) b) elt
    | Tbinop (Tiff, a, b) ->
       meet_term man (t_and (t_implies a b) (t_implies b a)) elt
    | Tquant (Tforall, tq) ->
      begin
        match t_open_quant tq with
        | [a], _, t when (Ty.ty_equal a.vs_ty Ty.ty_int) ->
          let t = S.Infer_why3.t_push_negation t in
          let t = t_subst_single a quant_var t in
          meet_term man t elt
        | _ -> TDom.meet_term man term elt
      end
    | _ -> TDom.meet_term man term elt
end
