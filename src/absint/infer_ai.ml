
module type Inv_gen = sig
  val infer_loop_invariants:
    widening:int -> Env.env -> Pmodule.pmodule -> Pmodule.pmodule
end

module Make (D: Domain.DOMAIN) = struct

  open Pmodule
  open Pdecl
  open Expr
  open Ity
  open Term

  type smap = {
    sm_vs : vsymbol Mvs.t;
    sm_pv : pvsymbol Mvs.t;
    (* sm_xs : xsymbol Mxs.t; not needed*)
    sm_rs : rsymbol Mrs.t
  }

  let sm_empty = {sm_vs = Mvs.empty; sm_pv = Mvs.empty; sm_rs = Mrs.empty }

  let sm_save_vs sm v v' = {
    sm_vs = Mvs.add v v'.pv_vs sm.sm_vs;
    sm_pv = Mvs.add v v' sm.sm_pv;
    sm_rs = sm.sm_rs }

  let sm_save_pv sm v v' = {
    sm_vs = Mvs.add v.pv_vs v'.pv_vs sm.sm_vs;
    sm_pv = Mvs.add v.pv_vs v' sm.sm_pv;
    sm_rs = sm.sm_rs }

  let sm_save_rs sm s s' =
    { sm with sm_rs = Mrs.add s s' sm.sm_rs }

  let sm_find_pv sm v = Mvs.find_def v v.pv_vs sm.sm_pv

  let sm_find_rs sm rs = Mrs.find_def rs rs sm.sm_rs

  let t_subst sm t =
    let m = Mvs.map (fun v -> t_var v) sm.sm_vs in (* TODO can this be simplified *)
    t_subst m t

  let infer_loop_invariants ~widening env pmod =
    let module AI = Ai_cfg.Make (struct
        let env = env
        let pmod = pmod
        let widening = widening
        module D = D
      end)
    in

    let rec reconstruct_expr cfg context fixp sm e =
      let reconstruct_e = reconstruct_expr cfg context fixp in
      let reconstruct_l = reconstruct_let_defn cfg context fixp in
      let reconstruct_ce = reconstruct_cexp cfg context fixp in
      let expl = "expl:loop invariant via abstract interpretation" in
      match e.e_node with
      | Elet (ld,e2) ->
         let sm,ld = reconstruct_l sm ld in
         let e = reconstruct_e sm e2 in
         e_let ld e
      | Evar v -> e_var (sm_find_pv sm v)
      | Econst c -> e_const c e.e_ity
      | Eassign asl -> let conv (r,f,v) =
            e_var (sm_find_pv sm r), f, e_var (sm_find_pv sm v) in
          e_assign (List.map conv asl)
      | Eabsurd -> e_absurd e.e_ity
      | Epure t -> e_pure (t_subst sm t)
      | Eassert (k,t) -> e_assert k (t_subst sm t)
      | Eexec (ce,_) -> e_exec (reconstruct_ce sm ce)
      | Eif (e1, e2, e3) ->
          e_if (reconstruct_e sm e1) (reconstruct_e sm e2) (reconstruct_e sm e3)
      | Ematch (e,  pats, exns) ->
          let pats = List.map (fun (p, e) -> p, reconstruct_e sm e) pats in
          let exns = Mxs.map (fun (pvs, e) -> pvs, reconstruct_e sm e) exns in
          e_match (reconstruct_e sm e) pats exns
       | Eraise (x, e_) -> e_raise x (reconstruct_e sm e_) e.e_ity
       | Eghost e -> e_ghostify true (reconstruct_e sm e)
       | Ewhile (e_cond, inv, var, e_loop) ->
           let _, new_inv = List.find (fun (e_, _) -> e == e_) fixp in
           let t = AI.domain_to_term cfg context new_inv in
           let t = Term.t_attr_add (Ident.create_attribute expl) t in
           if Debug.test_flag Uf_domain.infer_debug then
             Pretty.print_term Format.std_formatter t;
           let inv = List.map (t_subst sm) (t::inv) in
           let var = List.map (fun (t,ls) -> (t_subst sm t, ls)) var in
           e_while (reconstruct_e sm e_cond) inv var (reconstruct_e sm e_loop)
       | Efor (pv, (f, d, to_), pv2, inv, e_loop) ->
           let _, new_inv = List.find (fun (e_, _) -> e == e_) fixp in
           let t = AI.domain_to_term cfg context new_inv in
           let t = Term.t_attr_add (Ident.create_attribute expl) t in
           let inv = List.map (t_subst sm) (t::inv) in
           e_for pv (e_var f) d (e_var to_) pv2 inv (reconstruct_e sm e_loop)
       | Eexn (xs,e) -> e_exn xs (reconstruct_e sm e)

    and reconstruct_let_defn cfg context fixp sm ld =
      let reconstruct = reconstruct_expr cfg context fixp in
      match ld with
      | LDvar (v, e)->
         let e = reconstruct sm e in
         let id = Ident.id_clone v.pv_vs.vs_name in
         let ld, v' = let_var id ~ghost:v.pv_ghost e in
         sm_save_pv sm v v', ld
      | LDsym _ ->
         Warning.emit "invariants are not yet generated for inner let functions";
         assert false
      | LDrec _ ->
         Warning.emit "invariants are not yet generated for inner let rec";
         assert false

(* and clone_cexp cl sm c = match c.c_node with *)

    and reconstruct_cexp cfg context fixp sm c =
      let reconstruct = reconstruct_expr cfg context fixp in
      match c.c_node with
      | Capp (s,vl) ->
         let vl = List.map (fun v -> sm_find_pv sm v) vl in
         let al = List.map (fun v -> v.pv_ity) c.c_cty.cty_args in
         c_app (sm_find_rs sm s) vl al c.c_cty.cty_result
      | Cpur (s,vl) ->
         let vl = List.map (fun v -> sm_find_pv sm v) vl in
         let al = List.map (fun v -> v.pv_ity) c.c_cty.cty_args in
         c_pur s vl al c.c_cty.cty_result
      | Cfun e ->
         let cty = c.c_cty in
         c_fun ~mask:cty.cty_mask cty.cty_args cty.cty_pre
           cty.cty_post cty.cty_xpost cty.cty_oldies (reconstruct sm e)
      | Cany ->
         c_any c.c_cty
    in

    let clone_infer_pdecl pdecl sm =
      let open Ident in
      match pdecl.pd_node with
      | PDpure ->
         create_pure_decl_l pdecl.pd_pure, sm
      | PDlet (LDsym (rs1, {c_node = Capp (rs2,pvl)})) ->
         (* TODO not sure what these pvl are. *)
         let rs2 = sm_find_rs sm rs2 in
         let ityl = List.map (fun pv -> pv.pv_ity) rs1.rs_cty.cty_args in
         let ity  = rs1.rs_cty.cty_result in
         let cexp = c_app rs2 pvl ityl ity in
         let id = id_clone rs1.rs_name in
         let let_defn, new_rs =
           let_sym id ~ghost:(rs_ghost rs1) ~kind:(rs_kind rs1) cexp in
         create_let_decl let_defn, sm_save_rs sm rs1 new_rs
      | PDlet (LDsym (rs, ({c_node = Cfun e} as cexp))) ->
         (* TODO: check that rs is not a "function" *)
         let open Ity in
         let preconditions = cexp.c_cty.cty_pre in
         let cfg = AI.start_cfg rs in
         let context = AI.empty_context () in
         List.iter (AI.add_variable cfg context) cexp.c_cty.cty_args;
         if Debug.test_flag Uf_domain.infer_debug then
           Format.printf "%a@." Expr.print_expr e;
         ignore (AI.put_expr_with_pre cfg context e preconditions);
         (* will hold the different file offsets (useful when writing
               multiple invariants) *)
         let fixp = AI.eval_fixpoints cfg context in
         let new_e = reconstruct_expr cfg context fixp sm e in
         let ce = c_fun cexp.c_cty.cty_args cexp.c_cty.cty_pre
                    cexp.c_cty.cty_post cexp.c_cty.cty_xpost
                    cexp.c_cty.cty_oldies new_e in
         let id = id_clone rs.rs_name in
         let let_defn, new_rs =
           let_sym id ~ghost:(rs_ghost rs) ~kind:(rs_kind rs) ce in
         create_let_decl let_defn, sm_save_rs sm rs new_rs
      | PDlet (LDsym (_, {c_node = Cpur _}))
      | PDlet (LDsym (_, {c_node = Cany; _})) -> pdecl, sm
      | PDlet (LDvar (pv, e)) ->
         Warning.emit "invariants are not yet generated for let var";
         let e = e_rs_subst sm.sm_rs e in
         let id = id_clone pv.pv_vs.vs_name in
         let let_defn, new_pv = let_var id ~ghost:pv.pv_ghost e in
         create_let_decl let_defn, sm_save_pv sm pv new_pv
      | PDlet (LDrec lrd) ->
         Warning.emit "invariants are not yet generated for let rec";
         let rec_defn {rec_rsym;rec_fun;rec_varl} =
           rec_rsym,c_rs_subst sm.sm_rs rec_fun,rec_varl,rs_kind rec_rsym in
         let let_defn, new_lrd = let_rec (List.map rec_defn lrd) in
         let sm = List.fold_left2 (fun rssm rd1 rd2 ->
                      sm_save_rs sm rd1.rec_sym rd2.rec_sym) sm lrd new_lrd in
         create_let_decl let_defn, sm
      | PDexn _ | PDtype _ -> pdecl, sm
    in

    let rec add_to_pmod (pmod_uc,rssm) decl =
      match decl with
      | Udecl pdecl ->
         let cloned_pdecl, rssm = clone_infer_pdecl pdecl rssm in
         add_pdecl ~warn:true ~vc:true pmod_uc cloned_pdecl, rssm
      | Uclone mod_inst -> add_clone pmod_uc mod_inst, rssm
      | Umeta (m, margs) -> add_meta pmod_uc m margs, rssm
      | Uscope (s, mis) ->
         let pmod_uc = open_scope pmod_uc s in
         let (s,rssm) = List.fold_left add_to_pmod (pmod_uc, rssm) mis in
         close_scope s ~import:true, rssm
      | Uuse pmod -> use_export pmod_uc pmod, rssm
    in

    let theory = pmod.mod_theory in
    let preid = Ident.id_clone Theory.(theory.th_name) in
    let pmuc = create_module env preid in
    Format.eprintf "Before@.";
    let pmuc,_ =
      List.fold_left add_to_pmod (pmuc,sm_empty) pmod.mod_units in
    Format.eprintf "After@.";
    if Debug.test_flag Uf_domain.infer_debug then
      Format.eprintf "Invariants inferred.@.";
    close_module pmuc

end


module InvGenPolyhedra : Inv_gen = Make (Domain.Polyhedra)
module InvGenBox       : Inv_gen = Make (Domain.Box)
module InvGenOct       : Inv_gen = Make (Domain.Oct)
