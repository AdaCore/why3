module type Abs_int_options = sig
    val env       : Env.env
    val widening  : int
    module Domain : Domain.DOMAIN
end

module type Inv_gen = sig
  val infer_loop_invariants: Pmodule.pmodule -> Pmodule.pmodule
end

module Make (S: Abs_int_options) = struct

  let env = S.env

  open Pmodule
  open Pdecl
  open Expr
  open Ity

  let infer_loop_invariants pmod =
    let module AI = Ai_cfg.Make (struct
        let env = env
        let pmod = pmod
        let widening = S.widening
        module D = S.Domain
      end)
    in

    let rec reconstruct_expr cfg context fixp e =
      let r = reconstruct_expr cfg context fixp in
      match e.e_node with
      | Elet(LDvar(pv, e), e2) ->
        (let_var_raw pv (r e)
        |> e_let) (r e2)
      | Evar(_) | Econst(_) | Eassign(_)
      | Eabsurd | Epure (_) | Eassert(_) | Eexec(_) | Elet(_)
        -> e
      | Eif(e1, e2, e3) ->
        e_if (r e1) (r e2) (r e3)
      | Ematch (e,  pats, exns) ->
        let pats = List.map (fun (p, e) -> p, r e) pats in
        let exns = Mxs.map (fun (pvs, e) -> pvs, r e) exns in
        e_match (r e) pats exns
      | Ematch (e,  pats, m) -> assert false
      | Eraise(x, e_) ->
        e_raise x e_ e.e_ity
      | Eghost(e) ->
        e_ghostify true (r e)
      | Ewhile(e_cond, inv, vari, e_loop) ->
        begin
          let _, new_inv =
            try
              List.find (fun (e_, _) -> e == e_) fixp
            with
            | Not_found ->
              Format.eprintf "while loop not found (available loops: %d)@." (List.length fixp);
              Expr.print_expr Format.err_formatter e;
              Format.eprintf "@.";
              raise Not_found
          in
          let t = AI.domain_to_term cfg context new_inv in
          let t = Term.t_attr_add (Ident.create_attribute "expl:loop invariant via abstract interpretation") t in
          Pretty.print_term Format.err_formatter t;
          let inv = t :: inv in
          let e_cond = r e_cond in
          let e_loop = r e_loop in
          let e = e_while e_cond inv vari e_loop in
          e
        end
      | Efor(pv, (f, d, to_), pv2, inv, e_loop) ->
        let _, new_inv = List.find (fun (e_, _) -> e == e_) fixp in
        let t = AI.domain_to_term cfg context new_inv in
        let t = Term.t_attr_add (Ident.create_attribute "expl:loop invariant via abstract interpretation") t in
        let inv = t :: inv in
        e_for pv (e_var f) d (e_var to_) pv2 inv (r e_loop)
      | _ -> assert false
    in

    let clone_infer_pdecl pdecl =
      match pdecl.pd_node with
      | PDexn(e) -> Some (create_exn_decl e)
      | PDtype(t) ->
          begin match create_type_decl t with
        | [a] -> Some a
        | _ -> assert false
          end
      | PDpure -> begin
          let t = match pdecl.pd_pure with [t] -> t | _ -> assert false in
          let open Decl in
          match t.d_node with
          | Dprop(Pgoal, _, _) -> None
          | _ -> Some (create_pure_decl t)
        end
      | PDlet(l) ->
        begin
        match l with
        | LDvar(_) -> Some (create_let_decl l)
        | LDsym(rs, cexp) ->
          begin
          match cexp.c_node with
          | Cfun(e) ->
            let open Ity in
            let preconditions = Ity.(cexp.c_cty.cty_pre) in
            let cfg = AI.start_cfg rs in
            let context = AI.empty_context () in
            List.iter (AI.add_variable cfg context) Ity.(cexp.c_cty.cty_args);
            Expr.print_expr Format.err_formatter e;
            Format.eprintf "@.";
            ignore (AI.put_expr_with_pre cfg context e preconditions);
            (* will hold the diffrent file offsets (useful when writing multiple invariants) *)
            let fixp = AI.eval_fixpoints cfg context in
            let new_e = reconstruct_expr cfg context fixp e in
            let ce = c_fun cexp.c_cty.cty_args cexp.c_cty.cty_pre cexp.c_cty.cty_post cexp.c_cty.cty_xpost
              cexp.c_cty.cty_oldies new_e
            in
            let let_expr = let_sym_raw rs ce in
            Some (create_let_decl let_expr)
          | _ ->
            Some (create_let_decl l)
          end
        | _ ->
          Some (create_let_decl l)
        end
    in


    let rec add_to_pmod pmod_uc decl =
      match decl with
      | Udecl(pdecl) ->
        begin
        match clone_infer_pdecl pdecl with
        | Some d -> add_pdecl ~vc:true pmod_uc d
        | None -> pmod_uc
        end
      | Uclone(mod_inst) -> add_clone pmod_uc mod_inst
      | Umeta(m, margs) -> add_meta pmod_uc m margs
      | Uscope(s, mis) -> List.fold_left add_to_pmod (open_scope pmod_uc s) mis
                             |> fun p -> close_scope p ~import:true
      | Uuse(pmod) -> use_export pmod_uc pmod
    in

    let theory = pmod.mod_theory in
    let preid = Ident.id_clone Theory.(theory.th_name) in
    let preid = Ident.{ preid with pre_name = preid.pre_name ^ "infer.mlw" } in
    let pmod_uc = create_module env preid
                  |> fun p -> List.fold_left add_to_pmod p pmod.mod_units in
    Format.eprintf "Invariants inferred.@.";
    close_module pmod_uc

end
