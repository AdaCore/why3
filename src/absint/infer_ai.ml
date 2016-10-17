module Make(S:sig
    val env: Env.env
  end) = struct

  let env = S.env

  open Pmodule
  open Pdecl
  open Expr
  open Ity

  let infer_loop_invariants pmod =
    let module AI = Abstract_interpreter.Abstract_interpreter(struct
        let env = env
        let pmod = pmod
      end)
    in

    let rec reconstruct_expr cfg fixp e =
      let r = reconstruct_expr cfg fixp in
      match e.e_node with
      | Elet(LDvar(pv, e), e2) ->
        (let_var_raw pv (r e)
        |> fst
        |> e_let) (r e2)
      | Evar(_) | Econst(_) | Eassign(_)
      | Eabsurd | Epure (_) | Eassert(_) | Eexec(_) | Elet(_)
        -> e
      | Eif(e1, e2, e3) ->
        e_if (r e1) (r e2) (r e3)
      | Ecase(e,  pats) ->
        List.map (fun (p, e) ->
            p, r e) pats
        |> e_case (r e)
      | Eraise(x, e) ->
        e_raise x e e.e_ity
      | Etry(e, pv) ->
        Mexn.map (fun (pvs, e) ->
            pvs, r e) pv 
        |> e_try (r e)
      | Eghost(e) ->
        e_ghostify true (r e)
      | Ewhile(e_cond, inv, vari, e_loop) ->
        begin
        try
        let _, new_inv = List.find (fun (e_, dom) -> e == e_) fixp in
        let t = AI.domain_to_term cfg new_inv in
        let t = Term.t_label_add (Ident.create_label "expl:loop invariant via abstract interpretation") t in
        let inv = t :: inv in
        e_while (r e_cond) inv vari (r e_loop)
        with
        | Not_found ->
          Format.eprintf "loop not found@.";
          Expr.print_expr Format.err_formatter e;
          raise Not_found
        end
      | Efor(pv, (f, d, t), inv, e_loop) ->
        let _, new_inv = List.find (fun (e_, dom) -> e == e_) fixp in
        let inv = (AI.domain_to_term cfg new_inv) :: inv in
        e_for pv (e_var f) d (e_var t) inv (r e_loop)
    in

    let clone_infer_pdecl pdecl =
      match pdecl.pd_node with
      | PDexn(e) -> Some (create_exn_decl e)
      | PDtype(t) -> Some (create_type_decl t)
      | PDpure ->
        let [t] = pdecl.pd_pure in
        begin
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
            let local_ty = AI.empty_local_ty  in
            let local_ty = List.fold_left (AI.add_variable cfg) local_ty
                Ity.(cexp.c_cty.cty_args) in
            Expr.print_expr Format.err_formatter e;
            Format.eprintf "@.";
            ignore (AI.put_expr_with_pre cfg local_ty e preconditions);
            (* will hold the diffrent file offsets (useful when writing multiple invariants) *)
            let fixp = AI.eval_fixpoints cfg in
            let new_e = reconstruct_expr cfg fixp e in
            let ce = c_fun cexp.c_cty.cty_args cexp.c_cty.cty_pre cexp.c_cty.cty_post cexp.c_cty.cty_xpost
              cexp.c_cty.cty_oldies new_e
            in
            let let_expr = let_sym_raw rs ce |> fst in
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
      | Uscope(s, t, mis) -> List.fold_left add_to_pmod (open_scope pmod_uc s) mis
                             |> fun p -> close_scope p t
      | Uuse(pmod) -> use_export pmod_uc pmod
    in

    let theory = pmod.mod_theory in
    let preid = Ident.id_clone Theory.(theory.th_name) in
    let preid = Ident.{ preid with pre_name = preid.pre_name ^ "infer.mlw" } in
    let pmod_uc = create_module env preid
                  |> fun p -> List.fold_left add_to_pmod p pmod.mod_units in
    Format.eprintf "done@.";
    close_module pmod_uc

end
