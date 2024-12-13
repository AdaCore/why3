(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3
open Pmodule
open Pdecl
open Ity
open Expr
open Term
open Ident

type domain_elt = Union of ity * domain_elt list | Variable of pvsymbol | Proj of ity * rsymbol * domain_elt | Bot

let rec equal a b =
  match (a, b) with
  | Bot, Bot -> true
  | Variable v, Variable w -> pv_equal v w
  | Proj (t, r, e), Proj (t2, r2, e2) -> ity_equal t t2 && rs_equal r r2 && equal e e2
  | Union (ty, elts), Union (ty2, elts2) -> ity_equal ty ty2 && List.for_all2 equal elts elts2
  | _, _ -> false

let rec print_elt fmt e =
  match e with
  | Union (_, elts) -> Format.fprintf fmt "{ %a }" (Format.pp_print_list print_elt) elts
  | Variable p -> Format.fprintf fmt "%a" Ity.print_pv p
  | Proj (_, r, elt) -> Format.fprintf fmt "%a -> %a" print_elt elt Expr.print_rs r
  | Bot -> Format.fprintf fmt "bot"

let rec ity_of d : ity =
  match d with
  | Variable p -> p.pv_ity
  | Proj (_, v, p) -> (
      let inner_ty = ity_of p in
      match inner_ty.ity_node with
      | Ityvar _ -> assert false
      | Ityapp (s, tl, rl) | Ityreg { reg_its = s; reg_args = tl; reg_regs = rl } ->
          let isb = its_match_regs s tl rl in
          ity_full_inst isb v.rs_cty.cty_result)
  | Bot -> assert false
  | Union (cty, _) -> cty

let fields ity =
  match ity.ity_node with
  | Ityapp (s, _, _) -> s.its_mfields @ s.its_ofields
  | Ityreg r -> r.reg_its.its_mfields @ r.reg_its.its_ofields
  | Ityvar _ -> assert false

(* Smart constructors *)

let mk_proj ty elt f =
  match elt with
  | Union (_, flds) ->
      let fld_nms = fields (ity_of elt) in
      let rec go nms vals =
        match (nms, vals) with
        | nm :: nms, v :: vals -> if pv_equal nm (fd_of_rs f) then v else go nms vals
        | _, _ -> failwith "mk_proj: field not part of type"
      in
      go fld_nms flds
  | Bot -> Bot
  | _ -> Proj (ty, f, elt)

let unfold known v =
  let ity = ity_of v in
  let sym = match ity.ity_node with Ityapp (sym, _, _) -> sym | Ityreg r -> r.reg_its | _ -> assert false in

  let def =
    try find_its_defn known sym
    with _ ->
      Format.eprintf "Could not find %a\n " print_its sym;
      assert false
  in
  if List.length def.itd_constructors <> 1 then Bot
  else Union (ity_purify ity, List.map (fun f -> mk_proj ity v f) def.itd_fields)

let rec merge known l r =
  (* Format.printf "merging %a  %a\n" print_elt l print_elt r; *)
  match (l, r) with
  | Union (ty1, l1), Union (ty2, l2) ->
      if ity_equal ty1 ty2 then Union (ty1, List.map2 (merge known) l1 l2)
      else (
        Format.eprintf "cannot merge %a with %a\n" print_ity ty1 print_ity ty2;
        assert false)
  | Variable v1, Variable v2 -> if pv_equal v1 v2 then Variable v1 else Bot
  | Proj (c, f1, p1), Proj (_, f2, p2) -> if f1 = f2 then mk_proj c (merge known p1 p2) f1 else Bot
  | Variable _, _ -> Bot
  | _, Variable _ -> Bot
  | _, Bot -> Bot
  | Bot, _ -> Bot
  | Proj _, Union _ -> merge known (unfold known l) r
  | Union _, Proj _ -> merge known l (unfold known r)

let rec update known l fld fld_ty v =
  (* Format.printf "update %a . %a  = %a \n" print_elt l print_pv fld print_elt v; *)
  match l with
  | Union (ty, flds) ->
      let rec worker flds regs =
        match (flds, regs) with
        | f :: fs, r :: rs -> if f = fld then v :: rs else r :: worker fs rs
        | _, _ -> assert false
      in
      Union (ty, worker (fields ty) flds)
  | Bot -> Bot
  | Variable _ -> update known (unfold known l) fld fld_ty v
  | _ -> assert false

(* requires the term to be a projection *)
let rec to_term elt : term =
  match elt with
  | Variable v -> t_var v.pv_vs
  | Proj (_, fld, p) -> t_app_infer (ls_of_rs fld) [ to_term p ]
  | _ -> assert false

let rec find_invariants known (a : domain_elt) (b : domain_elt) (k : domain_elt -> 'a) : 'a list =
  if equal a b then [ k a ]
  else
    match (a, b) with
    | Union (_, vls), Union (_, vls') ->
        let rec go vls vls' acc =
          match (vls, vls') with
          | v :: vls, v' :: vls' -> go vls vls' (find_invariants known v v' k @ acc)
          | [], [] -> acc
          | _, _ -> failwith "unreachable"
        in
        go vls vls' []
    | _, Bot | Bot, _ -> []
    | Variable _, Variable _ -> []
    | Proj (i, r, e), Proj (_, r2, e2) ->
        (* assert (ity_equal i i2); *)
        if rs_equal r r2 then find_invariants known e e2 (fun d -> k (Proj (i, r, d))) else []
    | Union _, _ -> find_invariants known a (unfold known b) k
    | _, Union _ -> find_invariants known (unfold known a) b k
    | Variable _, Proj _ -> []
    | Proj _, Variable _ -> []

(* The domain maps symbols to their symbolic value *)
type domain = domain_elt Mpv.t

let[@warning "-32"] print_domain fmt dom =
  Mpv.iter (fun k v -> Format.fprintf fmt "%a => %a" Ity.print_pv k print_elt v) dom

module FreshNames = struct
  open Ity

  type t = rsymbol Mrs.t * pvsymbol Mpv.t

  let empty = (Mrs.empty, Mpv.empty)
  let pv (_, m) k def = match Mpv.find_opt k m with Some v -> v | None -> def
  let pv2 (_, m) k def = match Mpv.find_opt k m with Some v -> v | None -> def
  let add_pv (m1, m2) k v = (m1, Mpv.add k v m2)
  let rs (m, _) k def = match Mrs.find_opt k m with Some v -> v | None -> def
  let merge_rs (m1, m2) (m1' : rsymbol Mrs.t) = (Mrs.set_union m1' m1, m2)
  let add_rs (m1, m2) k v = (Mrs.add k v m1, m2)
end

let find m k def = match Mpv.find_opt k m with Some v -> v | None -> def

let merge_domains known d1 d2 =
  Mpv.merge
    (fun _ a b -> match (a, b) with Some a, Some b -> Some (merge known a b) | None, b -> b | a, None -> a)
    d1 d2

let rec analyze muc (st : FreshNames.t) (regions : domain) (e : expr) : domain_elt * expr * domain =
  let attrs = e.e_attrs in
  let loc = e.e_loc in
  let d, e, r = inner muc st regions e in
  (d, e_attr_push ?loc attrs e, r)

and analyze_assign muc st regions (v, f, t) : domain * (_ * _ * _) =
  let t_val = find regions t (Variable (FreshNames.pv2 st t t)) in
  let v_val = find regions v (Variable (FreshNames.pv2 st v v)) in

  let cty' = cty_apply f.rs_cty [ FreshNames.pv2 st v v ] [] t.pv_ity in
  let e = (e_var (FreshNames.pv2 st v v), f, e_var (FreshNames.pv2 st t t)) in
  let v_val' = update muc.muc_known v_val (fd_of_rs f) cty' t_val in
  let regions = Mpv.add v v_val' regions in
  (regions, e)

and inner muc st regions e =
  match e.e_node with
  | Evar v -> (Bot, e_var (FreshNames.pv st v v), regions)
  | Econst _ -> (Bot, e, regions)
  | Elet (def, e) ->
      let st, def', regions = analyze_letdefn muc st regions def in
      let dom, e, regions = analyze muc st regions e in
      let regions = match def with LDvar (p, _) -> Mpv.remove p regions | _ -> regions in
      (dom, e_let def' e, regions)
  | Eexec (ce, _) ->
      let dom, e = analyze_cexp muc st regions ce in
      (dom, e_exec e, regions)
  | Eassign es ->
      let regions, es = Lists.map_fold_left (fun regions asgn -> analyze_assign muc st regions asgn) regions es in

      (Bot, e_assign es, regions)
  | Eif (s, i, e) ->
      let _, s, regions = analyze muc st regions s in

      let d, i, regions' = analyze muc st regions i in
      let d', e, regions'' = analyze muc st regions e in

      let d = merge muc.muc_known d d' in
      let regions = merge_domains muc.muc_known regions' regions'' in

      (d, e_if s i e, regions)
  | Ematch (scrut, brs, exn_brs) ->
      let _, scrut, regions = analyze muc st regions scrut in
      (* push the value of the scrutinee into branches *)
      let dom_reg, brs =
        if brs = [] then (None, [])
        else
          let dom_reg, brs =
            List.split
              (List.map
                 (fun br ->
                   let dom, br, reg = analyze_br muc st regions br in
                   ((dom, reg), br))
                 brs)
          in

          let dom, regions =
            List.fold_left
              (fun (dom_acc, reg_acc) (dom, reg) ->
                let dom' = merge muc.muc_known dom_acc dom in
                let reg' = merge_domains muc.muc_known reg_acc reg in
                (dom', reg'))
              (Bot, Mpv.empty) dom_reg
          in

          (Some (dom, regions), brs)
      in

      let e_dom_reg, exn_brs =
        if not (Mxs.is_empty exn_brs) then
          let (dom, reg), e_brs =
            Mxs.mapi_fold
              (fun _ ebr (dom_acc, reg_acc) ->
                let dom, ebr, regions = analyze_e_br muc st regions ebr in
                let dom' = merge muc.muc_known dom_acc dom in
                let reg' = merge_domains muc.muc_known regions reg_acc in
                ((dom', reg'), ebr))
              exn_brs (Bot, Mpv.empty)
          in
          (Some (dom, reg), e_brs)
        else (None, exn_brs)
      in

      let dom, regions =
        match (dom_reg, e_dom_reg) with
        | Some (dom1, reg1), Some (dom2, reg2) -> (merge muc.muc_known dom1 dom2, merge_domains muc.muc_known reg1 reg2)
        | None, Some (dom, reg) -> (dom, reg)
        | Some (dom, reg), None -> (dom, reg)
        | None, None -> assert false
      in

      (dom, e_match scrut brs exn_brs, regions)
  | Ewhile (cond, inv, var, body) ->
      let inv =
        List.map (fun i -> t_v_map (fun v -> t_var (FreshNames.pv st (restore_pv v) (restore_pv v)).pv_vs) i) inv
      in
      let var =
        List.map
          (fun (i, l) -> (t_v_map (fun v -> t_var (FreshNames.pv st (restore_pv v) (restore_pv v)).pv_vs) i, l))
          var
      in
      let _, cond, regions = analyze muc st regions cond in
      let _, body, body_regions = analyze muc st Mpv.empty body in

      (* Bind all the mutated variables *)
      let old_vals =
        List.map
          (fun k ->
            let k = FreshNames.pv st k k in
            let_var (Ident.id_clone k.pv_vs.vs_name) ~ghost:true (e_pure (t_var k.pv_vs)))
          (Mpv.keys body_regions)
      in
      let lets, vars = List.split old_vals in

      (* Maps the freshened version of a variable to the name of the ghost binding holding the version before the loop *)
      let olds =
        List.map2 (fun a b -> ((FreshNames.pv st a a).pv_vs, t_var b.pv_vs)) (Mpv.keys body_regions) vars |> Mvs.of_list
      in

      let eqs =
        List.fold_right
          (fun (k, v) acc ->
            let invs : term list = find_invariants muc.muc_known (Variable (FreshNames.pv st k k)) v to_term in
            let t' = List.map (fun t -> ps_app ps_equ [ t; t_subst olds t ]) invs in
            t' @ acc)
          (Mpv.bindings body_regions) []
      in
      let regions = merge_domains muc.muc_known regions body_regions in

      let body =
        List.fold_left
          (fun body eq ->
            let ld, _ = let_var (Ident.id_fresh "_") (e_assert Assume eq) in
            e_let ld body)
          body eqs
      in
      let loop = e_while cond inv var body in
      let loop =
        List.fold_left
          (fun loop eq ->
            let ld, _ = let_var (Ident.id_fresh "_") loop in
            e_let ld (e_assert Assume eq))
          loop eqs
      in
      let loop = List.fold_left (fun loop ld -> e_let ld loop) loop lets in

      (Bot, loop, regions)
  | Efor (ix, (l, dir, u), iix, invs, body) ->
      let invs =
        List.map (fun i -> t_v_map (fun v -> t_var (FreshNames.pv st (restore_pv v) (restore_pv v)).pv_vs) i) invs
      in
      let _, body, body_regions = analyze muc st Mpv.empty body in

      (* Bind all the mutated variables *)
      let old_vals =
        List.map
          (fun k ->
            let k = FreshNames.pv st k k in
            let_var (Ident.id_clone k.pv_vs.vs_name) ~ghost:true (e_pure (t_var k.pv_vs)))
          (Mpv.keys body_regions)
      in
      let lets, vars = List.split old_vals in

      let olds =
        List.map2 (fun a b -> ((FreshNames.pv st a a).pv_vs, t_var b.pv_vs)) (Mpv.keys body_regions) vars |> Mvs.of_list
      in

      let eqs =
        List.fold_right
          (fun (k, v) acc ->
            let invs = find_invariants muc.muc_known (Variable (FreshNames.pv st k k)) v to_term in
            let t' = List.map (fun t -> ps_app ps_equ [ t; t_subst olds t ]) invs in
            t' @ acc)
          (Mpv.bindings body_regions) []
      in
      let regions = merge_domains muc.muc_known regions body_regions in

      let body =
        List.fold_left
          (fun body eq ->
            let ld, _ = let_var (Ident.id_fresh "_") (e_assert Assume eq) in
            e_let ld body)
          body eqs
      in

      let loop = e_for ix (e_var (FreshNames.pv st l l)) dir (e_var (FreshNames.pv st u u)) iix invs body in

      let loop =
        List.fold_left
          (fun loop eq ->
            let ld, _ = let_var (Ident.id_fresh "_") loop in
            e_let ld (e_assert Assume eq))
          loop eqs
      in
      let loop = List.fold_left (fun loop ld -> e_let ld loop) loop lets in

      (Bot, loop, regions)
  | Eraise (x, inner) ->
      let _, e', regions = analyze muc st regions inner in
      (Bot, e_raise x e' e.e_ity, regions)
  | Eexn (x, expr) ->
      (* generate equations here as well *)
      let dom, expr, regions = analyze muc st Mpv.empty expr in
      let exn = e_exn x expr in
      (dom, exn, regions)
  | Eassert (k, t) ->
      let t = t_v_map (fun v -> t_var (FreshNames.pv st (restore_pv v) (restore_pv v)).pv_vs) t in
      (Bot, e_assert k t, regions)
  | Eghost e ->
      let dom, expr, regions = analyze muc st regions e in
      (dom, e_ghostify true expr, regions)
  | Epure t ->
      let t = t_v_map (fun v -> t_var (FreshNames.pv st (restore_pv v) (restore_pv v)).pv_vs) t in
      (Bot, e_pure t, regions)
  | Eabsurd -> (Bot, e, regions)

and analyze_letdefn muc st (regions : domain) (l : let_defn) : FreshNames.t * let_defn * domain =
  match l with
  | LDvar (nm, exp) ->
      (* Format.printf "BEFORE ==== \n\n %a\n\n" Expr.print_expr exp; *)
      let dom, exp, regions = analyze muc st regions exp in
      (* Format.printf "AFTER ==== \n\n %a\n\n" Expr.print_expr exp; *)
      let letdef, nm' = let_var (Ident.id_clone nm.pv_vs.vs_name) ~ghost:nm.pv_ghost exp in

      (FreshNames.add_pv st nm nm', letdef, Mpv.add nm dom regions)
  | LDsym (r, ce) -> (
      match ce.c_node with
      | Cfun e ->
          let _, e, _ = analyze muc FreshNames.empty Mpv.empty e in
          let cty = ce.c_cty in
          let f = c_fun cty.cty_args cty.cty_pre cty.cty_post cty.cty_xpost cty.cty_oldies e in
          let def, sym =
            let_sym (Ident.id_clone ~attrs:r.rs_name.id_attrs r.rs_name) ~ghost:(cty_ghost cty) ~kind:(rs_kind r) f
          in

          (FreshNames.add_rs st r sym, def, regions)
      | _ -> (st, l, regions))
  | LDrec rdl ->
      let defs =
        List.map
          (fun def ->
            let f =
              match def.rec_fun.c_node with
              | Cfun e ->
                  let _, e, _ = analyze muc st Mpv.empty e in
                  let cty = def.rec_fun.c_cty in
                  c_fun cty.cty_args cty.cty_pre cty.cty_post cty.cty_xpost cty.cty_oldies e
              | _ -> def.rec_fun
            in
            (def.rec_rsym, f, def.rec_varl, rs_kind def.rec_sym))
          rdl
      in
      let def, rdl' = let_rec defs in

      let subst = List.fold_left2 (fun sm d d' -> Mrs.add d.rec_sym d'.rec_sym sm) Mrs.empty rdl rdl' in

      (FreshNames.merge_rs st subst, def, regions)

and analyze_cexp muc st regions (c : cexp) : domain_elt * cexp =
  match c.c_node with
  | Capp (r, args) ->
      let region =
        match r.rs_field with
        | Some _ -> (
            match args with
            | [ a ] ->
                let var = find regions a (Variable (FreshNames.pv st a a)) in
                mk_proj c.c_cty.cty_result var r
            | _ -> failwith "projection applied to more than one arg")
        | None ->
            (* check if r is a record constructor *)
            if Strings.has_suffix "'mk" r.rs_name.id_string then
              Union (c.c_cty.cty_result, List.map (fun x -> find regions x (Variable (FreshNames.pv st x x))) args)
            else Bot
      in
      let vl = List.map (fun v -> FreshNames.pv st v v) args in
      let al = List.map (fun v -> v.pv_ity) c.c_cty.cty_args in
      let r = FreshNames.rs st r r in
      (region, c_app r vl al c.c_cty.cty_result)
  | Cpur (l, args) ->
      let vl = List.map (fun v -> FreshNames.pv st v v) args in
      let al = List.map (fun v -> v.pv_ity) c.c_cty.cty_args in
      (Bot, c_pur l vl al c.c_cty.cty_result)
  | Cfun expr ->
      let _, e, _ = analyze muc st regions expr in
      let cty = c.c_cty in
      (Bot, c_fun cty.cty_args cty.cty_pre cty.cty_post cty.cty_xpost cty.cty_oldies e)
  | Cany -> (Bot, c)

and analyze_br muc st regions (b : reg_branch) =
  let pat, e = b in
  let dom, e, reg = analyze muc st regions e in
  (dom, (pat, e), reg)

and analyze_e_br muc st regions (b : exn_branch) =
  let pat, e = b in
  let dom, e, reg = analyze muc st regions e in
  (dom, (pat, e), reg)

let transform_letdefn muc l =
  let _, def, _ = analyze_letdefn muc FreshNames.empty Mpv.empty l in
  def
