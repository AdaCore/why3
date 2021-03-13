(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Close_epsilon
open Term
open Theory
open Task

type lift_kind =
(*   | Goal (* prove the existence of a witness *) *)
  | Implied (* require the existence of a witness in an axiom *)
  | Implicit (* do not require a witness *)

let lift kind =
  let rec term acc t =
    match t.t_node with
    | Teps fb ->
        let fv = Mvs.keys (t_vars t) in
        let x, f = t_open_bound fb in
        let acc, f = form acc f in
        let tys = List.map (fun x -> x.vs_ty) fv in
        let xs = Ident.id_derive "epsilon" x.vs_name in
        let xl = create_fsymbol xs tys x.vs_ty in
        let acc = add_decl acc (Decl.create_param_decl xl) in
        let axs =
          Decl.create_prsymbol (Ident.id_derive ("epsilon_def") x.vs_name) in
        let xlapp = t_app xl (List.map t_var fv) t.t_ty in
        let f =
          match kind with
          (* assume that lambdas always exist *)
          | Implied when not (is_lambda t) ->
              t_forall_close_merge fv
                (t_implies (t_exists_close [x] [] f)
                   (t_subst_single x xlapp f))
          | _ -> t_subst_single x xlapp f
        in
        let acc = add_decl acc (Decl.create_prop_decl Decl.Paxiom axs f) in
        acc, xlapp
    | _ -> TermTF.t_map_fold term form acc t
  and form acc f = TermTF.t_map_fold term form acc f in
  fun th acc ->
    let th = th.task_decl in
    match th.td_node with
    | Decl d ->
        let acc, d = Decl.DeclTF.decl_map_fold term form acc d in
        add_decl acc d
    | _ -> add_tdecl acc th

let lift_epsilon kind = Trans.fold (lift kind) None

let meta_epsilon = Theory.register_meta_excl "lift_epsilon" [MTstring]
  ~desc:"Specify@ whether@ the@ existence@ of@ a@ witness@ for@ the@ \
    formula@ under@ epsilon@ is@ assumed:@;  \
    @[\
      - @[<hov 2>implicit:@ implicitly@ assume@ existence@]@\n\
      - @[<hov 2>implied:@ @ do@ not@ assume@ the@ existence@ \
          of@ a@ witness.@]\
    @]"

let lift_epsilon = Trans.on_meta_excl meta_epsilon
  (fun alo ->
    let kind = match alo with
      | Some [MAstr "implicit"] -> Implicit
      | Some [MAstr "implied"] | None -> Implied
      | _ -> failwith "lift_epsilon accepts only 'implicit' and 'implied'"
    in
    lift_epsilon kind)

let () = Trans.register_transform "lift_epsilon" lift_epsilon
  ~desc:"Move@ epsilon-terms@ into@ separate@ function@ definitions."
