

(* TODO move it deeper in the abstract interpretation mechanism (as needed) *)
let infer_debug  = Debug.register_flag "infer_debug"
                     ~desc:"Debug messages about loop inference using \
                            abstract interpretation."

module type Inv_gen = sig
  val infer_loop_invariants:
    ?widening:int -> Env.env -> Pmodule.pmodule -> Pmodule.pmodule
end

module Make (D: Domain.DOMAIN) = struct

  open Pmodule
  open Pdecl
  open Expr
  open Ity

  let infer_loop_invariants ?(widening=3) env pmod =
    let module AI = Ai_cfg.Make (struct
        let env = env
        let pmod = pmod
        let widening = widening
        module D = D
      end)
    in

    let rec reconstruct_expr cfg context fixp e =
      let r = reconstruct_expr cfg context fixp in
      let expl = "expl:loop invariant via abstract interpretation" in
      match e.e_node with
      | Elet (LDvar (pv, e), e2) ->
        e_let (let_var_raw pv (r e)) (r e2)
      | Evar _ | Econst _ | Eassign _ | Eabsurd | Epure _
      | Eassert _ | Eexec _ | Elet _ -> e
      | Eif (e1, e2, e3) -> e_if (r e1) (r e2) (r e3)
      | Ematch (e,  pats, exns) ->
        let pats = List.map (fun (p, e) -> p, r e) pats in
        let exns = Mxs.map (fun (pvs, e) -> pvs, r e) exns in
        e_match (r e) pats exns
      | Eraise (x, e_) -> e_raise x e_ e.e_ity
      | Eghost e -> e_ghostify true (r e)
      | Ewhile (e_cond, inv, vari, e_loop) ->
          let _, new_inv = List.find (fun (e_, _) -> e == e_) fixp in
          let t = AI.domain_to_term cfg context new_inv in
          let t = Term.t_attr_add (Ident.create_attribute expl) t in
          if Debug.test_flag infer_debug then
            Pretty.print_term Format.std_formatter t;
          e_while (r e_cond) (t :: inv) vari (r e_loop)
      | Efor(pv, (f, d, to_), pv2, inv, e_loop) ->
         let _, new_inv = List.find (fun (e_, _) -> e == e_) fixp in
         let t = AI.domain_to_term cfg context new_inv in
         let t = Term.t_attr_add (Ident.create_attribute expl) t in
         e_for pv (e_var f) d (e_var to_) pv2 (t :: inv) (r e_loop)
      | Eexn (xs,e) -> e_exn xs e (* TODO check if we need something
                                     "raw" as in Evar *)
    in


    (* TODO as I understand this, everything should be kept. So, I
       don't think that the function should return an option. Also the
       assert false should be fixed and removed. *)
    let clone_infer_pdecl pdecl =
      match pdecl.pd_node with
      | PDexn e -> Some (create_exn_decl e)
      | PDtype tl ->
         begin match create_type_decl tl with
         (* TODO fix this *)
         | [a] -> Some a
         | _ -> assert false end
      | PDpure -> begin
          let t = match pdecl.pd_pure with
              (* TODO fix this *)
              | [t] -> t
              | _ -> assert false in
          match t.d_node with
          (* TODO don't understand why goals are being droped *)
          | Dprop (Pgoal, _, _) -> None
          | _ -> Some (create_pure_decl t) end
      | PDlet (LDsym (rs, cexp) as l) -> begin
          match cexp.c_node with
          | Cfun e ->
            let open Ity in
            let preconditions = cexp.c_cty.cty_pre in
            let cfg = AI.start_cfg rs in
            let context = AI.empty_context () in
            List.iter (AI.add_variable cfg context) cexp.c_cty.cty_args;
            if Debug.test_flag infer_debug then
              Format.printf "%a@." Expr.print_expr e;
            ignore (AI.put_expr_with_pre cfg context e preconditions);
            (* will hold the diffrent file offsets (useful when writing
               multiple invariants) *)
            let fixp = AI.eval_fixpoints cfg context in
            let new_e = reconstruct_expr cfg context fixp e in
            let ce = c_fun cexp.c_cty.cty_args cexp.c_cty.cty_pre
                       cexp.c_cty.cty_post cexp.c_cty.cty_xpost
                       cexp.c_cty.cty_oldies new_e
            in
            let let_expr = let_sym_raw rs ce in
            Some (create_let_decl let_expr)
          | _ ->
            Some (create_let_decl l)
          end
      | PDlet l -> Some (create_let_decl l)
    in

    let rec add_to_pmod pmod_uc decl =
      match decl with
      | Udecl pdecl ->
        begin
        match clone_infer_pdecl pdecl with
        | Some d -> add_pdecl ~vc:true pmod_uc d
        | None -> pmod_uc
        end
      | Uclone mod_inst -> add_clone pmod_uc mod_inst
      | Umeta (m, margs) -> add_meta pmod_uc m margs
      | Uscope (s, mis) ->
         let s = List.fold_left add_to_pmod (open_scope pmod_uc s) mis in
         close_scope s ~import:true
      | Uuse pmod -> use_export pmod_uc pmod
    in

    let theory = pmod.mod_theory in
    let preid = Ident.id_clone Theory.(theory.th_name) in
    let pmuc = create_module env preid in
    let pmuc = List.fold_left add_to_pmod pmuc pmod.mod_units in
    if Debug.test_flag infer_debug then
      Format.eprintf "Invariants inferred.@.";
    close_module pmuc

end


module InvGenPolyhedra : Inv_gen = Make (Domain.Polyhedra)
module InvGenBox       : Inv_gen = Make (Domain.Box)
module InvGenOct       : Inv_gen = Make (Domain.Oct)
