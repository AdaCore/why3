open Domain

module Make(S:sig
    module A:TERM_DOMAIN
    val env: Env.env
    val pmod: Pmodule.pmodule
  end) = struct
  module A = S.A

  open Ai_logic
  module Ai_logic = Ai_logic.Make(struct
      let env = S.env
      let pmod = S.pmod
    end)
  open Ai_logic

  include A

  let quant_var, pv =
    let open Term in
    let ident_ret = Ident.{pre_name = "w"; pre_attrs = Ident.Sattr.empty; pre_loc = None; } in
    let v  = Ity.create_pvsymbol ident_ret Ity.ity_int in
    t_var Ity.(v.pv_vs), v

  let create_manager () =
    let man = A.create_manager () in
    A.add_variable_to_env man pv;
    man

  let to_term man t =
    A.to_term man t
    |> descend_quantifier quant_var

  let rec meet_term man term elt =
    let open Term in
    match term.t_node with
    | Tbinop(Tor, a, b) ->
      join man (meet_term man a elt) (meet_term man b elt)
    | Tbinop(Tand, a, b) ->
      meet_term man a elt |> meet_term man b
    | Tbinop(_) -> assert false
    | Tquant(Tforall, tq) ->
      begin
        match t_open_quant tq with
        | [a], _, t when (Ty.ty_equal a.vs_ty Ty.ty_int) ->
          let t = t_descend_nots t in
          let t = t_subst_single a quant_var t in
          meet_term man t elt
        | _ -> A.meet_term man term elt
      end
    | _ -> A.meet_term man term elt
end
