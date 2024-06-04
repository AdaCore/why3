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
open Wstdlib
open Ident
open Ty
open Term
open Ptree
open Coma_logic
open Coma_syntax

type vr = Ref of vsymbol | Var of vsymbol | Typ of tvsymbol

type ctx = {
  vars: vr Mstr.t;
  denv: Dterm.denv;
  hdls: (hsymbol * vsymbol list * param list) Mstr.t;
}

let ctx0 = {
  vars = Mstr.empty;
  denv = Dterm.denv_empty;
  hdls = Mstr.empty;
}

let add_hdl hs w pl ctx =
  let str = hs.hs_name.id_string in
  { ctx with hdls = Mstr.add str (hs, w, pl) ctx.hdls }

let add_var vs ctx =
  let str = vs.vs_name.id_string in
  { ctx with vars = Mstr.add str (Var vs) ctx.vars;
             denv = Mstr.add str (Dterm.DTgvar vs) ctx.denv }

let add_ref vs ctx =
  let str = vs.vs_name.id_string in
  { ctx with vars = Mstr.add str (Ref vs) ctx.vars;
             denv = Mstr.add str (Dterm.DTgvar vs) ctx.denv }

let add_typ ts ctx =
  let str = ts.tv_name.id_string in
  { ctx with vars = Mstr.add str (Typ ts) ctx.vars }

let add_param ctx = function
  | Pt ts -> add_typ ts ctx
  | Pv vs -> add_var vs ctx
  | Pr vs -> add_ref vs ctx
  | Pc (h, w, pl) -> add_hdl h w pl ctx

let find_ref ctx ({ id_str=id; id_loc=loc } : Ptree.ident) =
  match Mstr.find id ctx.vars with
  | Ref v -> v
  | Var _
  | Typ _ ->
      Loc.errorm ~loc
        "[coma typing] the symbol %s is not a reference" id
  | exception Not_found ->
      Loc.errorm ~loc
        "[coma typing] unbound variable %s" id

let create_user_id = Typing.Unsafe.create_user_prog_id

let rec type_param0 tuc ctx = function
  | PPv (id, ty) ->
      let ty = Typing.ty_of_pty tuc ty in
      let vs = create_vsymbol (create_user_id id) ty in
      Pv vs
  | PPr (id, ty) ->
      let ty = Typing.ty_of_pty tuc ty in
      let vs = create_vsymbol (create_user_id id) ty in
      Pr vs
  | PPc (id, w, pl) ->
      let _, params = Lists.map_fold_left (type_param tuc) ctx pl in
      let w = List.map (find_ref ctx) w in
      let hs = create_hsymbol (create_user_id id) in
      Pc (hs, w, params)
  | PPt id ->
      Pt (tv_of_string id.id_str)
  | PPo | PPb | PPl _ | PPa _ ->
      assert false

and type_param tuc ctx p =
  let p = type_param0 tuc ctx p in
  add_param ctx p, p

let type_term tuc ctx t =
  let open Theory in
  Typing.type_term_in_denv
    (get_namespace tuc) tuc.uc_known tuc.uc_crcmap ctx.denv t

let check_term tuc ctx t ty =
  let open Theory in
  Typing.check_term_in_denv
    (get_namespace tuc) tuc.uc_known tuc.uc_crcmap ctx.denv t ty

let type_fmla tuc ctx t =
  let open Theory in
  Typing.type_fmla_in_denv
    (get_namespace tuc) tuc.uc_known tuc.uc_crcmap ctx.denv t

let check_params ~loc p a =
  let rec aux ~loc l r = match l, r with
    | [], [] -> ()
    | Pt _  :: ll, Pt _  :: rr -> aux ~loc ll rr
    | Pr hl :: ll, Pr hr :: rr
    | Pv hl :: ll, Pv hr :: rr when ty_equal hl.vs_ty hr.vs_ty ->
        aux ~loc ll rr
    | Pc (_, wl, l) :: ll, Pc (_, wr, r) :: rr ->
        if not (Svs.equal (Svs.of_list wl) (Svs.of_list wr)) then
          Loc.errorm ~loc "[coma typing] prewrite mismatch"
        aux ~loc l r;
        aux ~loc ll rr
    | [], _ | _, [] ->
        Loc.errorm ~loc "[coma typing] \
          bad arity: %d argument(s) expected, %d given"
          (List.length p) (List.length a)
    | _ ->
        Loc.errorm ~loc "[coma typing] type error"
  in
  aux ~loc p a

(* let rec check_param ~loc l r =
  match l,r with
  | Pt _, Pt _ -> ()
  | Pr l, Pr r
  | Pv l, Pv r when ty_equal l.vs_ty r.vs_ty -> ()
  | Pc (_, _, l), Pc (_, _, r) -> check_params ~loc l r
  | _ -> Loc.errorm ~loc "[coma typing] type error"

and check_params ~loc l r =
  try List.iter2 (check_param ~loc) l r
  with Invalid_argument _ ->
    Loc.errorm ~loc
      "[coma typing] bad arity: %d argument(s) expected, %d given"
      (List.length l) (List.length r) *)

let has_attr t = match t.term_desc with
  | Tattr ((ATstr _), _) -> true
  | _ -> false

let rec sink_spec attr o bb dd al = function
  | PPb :: pl -> sink_spec attr o true dd al pl
  | PPo :: pl -> sink_spec attr o bb true al pl
  | PPc _ as p :: pl -> p :: sink_spec attr o bb dd al pl
  | PPa (t, true) :: pl when not (has_attr t) ->
      let a = PPa ({ t with term_desc = Tattr (attr, t)}, true) in
      sink_spec attr o true dd (a::al) pl
  | PPa _ as a :: pl -> sink_spec attr o true dd (a::al) pl
  | p::pl -> List.rev_append al (p :: sink_spec attr o bb dd [] pl)
  | [] -> if bb && not dd then
            List.rev_append al [PPb] else if o then List.rev al else
          Loc.errorm "this outcome must have a closed specification"

let rec param_spec (pre,name) o a pl e =
  let attach e dl = if dl = [] then e else
    { e with pexpr_desc = PEdef (e,true,dl) } in
  let rec clean = function
    | PPc (_,_,ql) -> List.for_all clean ql
    | PPa _ | PPl _ | PPo | PPb -> false
    | PPt _ | PPv _ | PPr _ -> true in
  let param p (o,a,pl,e,dl) = match p with
    | PPo -> o, a, pl, e, dl
    | PPt _ | PPv _ | PPr _  -> o, true, p::pl, e, dl
    | PPb -> false, a, pl, { e with pexpr_desc = PEbox (attach e dl) }, []
    | PPa (f,b) ->
        if a then Loc.errorm ~loc:f.term_loc "[coma typing] \
          specification clauses cannot appear before type or data parameters";
        o, a, pl, { e with pexpr_desc = PEcut ([f, b], attach e dl) }, []
    | PPl vtl ->
        List.iter (fun ({id_loc=loc},_,_,b) ->
          if a then Loc.errorm ~loc "[coma typing] \
            variable bindings cannot appear before type or data parameters";
          if b then Loc.errorm ~loc "[coma typing] \
            illegal reference binding") vtl;
        o, a, pl, { e with pexpr_desc = PElet (attach e dl, vtl) }, []
    | PPc (_,_,ql) when o && List.for_all clean ql -> o, a, p::pl, e, dl
    | PPc (h,wr,ql) ->
        let mkt d i = { term_desc = d; term_loc = i.id_loc } in
        let mke d i = { pexpr_desc = d; pexpr_loc = i.id_loc } in
        let apply d = function
          | PPt u -> mke (PEapp (d, PAt (PTtyvar u))) u
          | PPc (g,_,_) -> mke (PEapp (d, PAc (mke (PEsym (Qident g)) g))) g
          | PPv (v,_) -> mke (PEapp (d, PAv (mkt (Tident (Qident v)) v))) v
          | PPr (r,_) -> mke (PEapp (d, PAr r)) r
          | PPa _ | PPl _ | PPo | PPb -> d in
        let d = List.fold_left apply (mke (PEsym (Qident h)) h) ql in
        let post = false, name ^ "'" ^ h.id_str in
        let ql,d = Loc.try4 ~loc:h.id_loc param_spec post o a ql d in
        let d = { pdefn_name = h; pdefn_writes = wr;
                  pdefn_params = ql; pdefn_body = d } in
        let d = { pdefn_desc = d; pdefn_loc = h.id_loc } in
        o, a, PPc (h,wr,ql) :: pl, e, d::dl in
  let expl = if pre then "expl:precondition " else "expl:postcondition " in
  let attr = ATstr (Ident.create_attribute (expl^name)) in
  let pl = sink_spec attr o false false [] pl in
  let _,_,pl,e,dl = List.fold_right param pl (true,a,[],e,[]) in
  pl, attach e dl

let dl_split flat dl =
  if flat then [false, dl] else
  let head (h,_,_,_) = h in
  let iter fn (_,_,_,d) =
    (* we assume no collisions *)
    let rec inspect = function
      | Esym h -> fn h
      | Edef (e,_,dl) ->
          let check (_,_,_,d) = inspect d
          in List.iter check dl; inspect e
      | Eapp (e, Ac d) -> inspect d; inspect e
      | Elet (e,_) | Ecut (_,_,e) | Ebox e
      | Eset (e,_) | Elam (_,e) | Ewox e
      | Eapp (e,_) -> inspect e
      | Eany -> () in inspect d in
  let module SCC = MakeSCC(Hhs) in
  SCC.scc head iter dl

let rec qloc = function
  | Qdot (p, id) -> Loc.join (qloc p) id.id_loc
  | Qident id    -> id.id_loc

let hs_db = Wid.create 256

let hs_of_xs xs = Wid.find hs_db xs.Ity.xs_name

let hs_register (hs,_,_ as reg) =
  let xs = Ity.create_xsymbol (id_clone hs.hs_name) Ity.ity_unit in
  Wid.set hs_db xs.Ity.xs_name reg;
  Pdecl.create_exn_decl xs

let rec subs_param (mty, mvs as acc) = function
  | Pt _ as p -> acc, p
  | Pv v ->
      let t = ty_inst mty v.vs_ty in
      let v' = create_vsymbol (id_clone v.vs_name) t in
      acc, Pv v'
  | Pr v ->
      let t = ty_inst mty v.vs_ty in
      let v' = create_vsymbol (id_clone v.vs_name) t in
      let mvs = Mvs.add v v' mvs in
      (mty, mvs), Pr v'
  | Pc (h, ws, pl) ->
      let ws = List.map (fun v -> Mvs.find_def v v mvs) ws in
      let _, pl = Lists.map_fold_left subs_param acc pl in
      acc, Pc (h, ws, pl)

let rec type_expr ({Pmodule.muc_theory = tuc} as muc) ctx { pexpr_desc=d; pexpr_loc=loc } =
  match d with
  | PEany -> Eany, []
  | PEbox e -> let e = type_prog ~loc muc ctx e in Ebox e, []
  | PEwox e -> let e = type_prog ~loc muc ctx e in Ewox e, []
  | PEcut (l,e) ->
      let e = type_prog ~loc muc ctx e in
      let ll = List.fold_left
        (fun acc (t,b) -> Ecut (type_fmla tuc ctx t, b, acc))
        e (List.rev l) in
      ll, []
  | PEsym q ->
      let h, _, pl =
        try let nm = match q with
              | Qdot _ -> raise Not_found
              | Qident id -> id.id_str in
            Mstr.find nm ctx.hdls with Not_found ->
        try let sl = Typing.string_list_of_qualid q in
            let ns = List.hd muc.Pmodule.muc_import in
            hs_of_xs (Pmodule.ns_find_xs ns sl)
        with Not_found ->
          Loc.errorm ~loc:(qloc q) "[coma typing] \
            unbound handler `%a'" Typing.print_qualid q
      in
      Esym h, pl
  | PEapp (pe, a) ->
      let e, te = type_expr muc ctx pe in
      (match te, a with
       | Pv vs :: tes, PAv t ->
           let tt = type_term tuc ctx t in
           let () = match tt.t_ty with
             | Some ty when ty_equal ty vs.vs_ty -> ()
             | _ -> Loc.errorm ~loc:t.term_loc "[coma typing] \
                      type error in application" in
           Eapp (e, Av tt), tes
       | Pr rs :: tes, PAr id ->
           let s = match Mstr.find id.id_str ctx.vars with
             | Ref v -> v
             | Var _ | Typ _ ->
                Loc.errorm ~loc:id.id_loc "[coma typing] \
                  the symbol `%s' is not a reference" id.id_str
             | exception Not_found ->
                 Loc.errorm ~loc:id.id_loc "[coma typing] \
                   unbound variable `%s'" id.id_str in
           let m = Mvs.singleton rs s in
           let _, tes = Lists.map_fold_left subs_param (Mtv.empty, m) tes in
           Eapp (e, Ar s), tes
       | Pc (_h, _vs, pl) :: tes, PAc ea ->
           let ea, tea = type_expr muc ctx ea in
           check_params ~loc pl tea;
           Eapp (e, Ac ea), tes
       | Pt tv :: tes, PAt pty ->
           let ty = Typing.ty_of_pty tuc pty in
           let m = Mtv.singleton tv ty in
           let _, tes = Lists.map_fold_left subs_param (m, Mvs.empty) tes in
           Eapp (e, At ty), tes
       | [], _ ->
          Loc.errorm ~loc:pe.pexpr_loc "[coma typing] \
            the expression `%a' is already fully applied" PP.pp_expr e
       | _ -> Loc.errorm ~loc "[coma typing] type error with the application")
  | PElet (e, l) ->
      let ctx0 = ctx in
      let typ_let ctx (id, t, pty, mut) =
        let ty = Typing.ty_of_pty tuc pty in
        let tt = check_term tuc ctx0 t ty in
        let vs = create_vsymbol (create_user_id id) ty in
        let ctx = if mut then add_ref vs ctx else add_var vs ctx in
        ctx, (vs,tt,mut)
      in
      let ctx, ll = Lists.map_fold_left typ_let ctx l in
      let e = type_prog ~loc muc ctx e in
      Elet (e, ll), []
  | PEset (e, l) ->
      let typ_set ({ id_str=id; id_loc=loc }, t) =
        match Mstr.find id ctx.vars with
        | Ref v ->
          let tt = check_term tuc ctx t v.vs_ty in
          (v, tt)
        | Var _
        | Typ _ ->
            Loc.errorm ~loc "[coma typing] \
              the symbol `%s' is not a reference" id
        | exception Not_found ->
            Loc.errorm ~loc "[coma typing] \
              unbound variable `%s'" id in
      let ll = List.map typ_set l in
      let e = type_prog ~loc muc ctx e in
      Eset (e, ll), []
  | PElam (pl, e) ->
      let pl, e = param_spec (true, "<lambda>") true false pl e in
      let ctx, params = Lists.map_fold_left (type_param tuc) ctx pl in
      let e = type_prog ~loc:(e.pexpr_loc) muc ctx e in
      Elam (params, e), params
  | PEdef (e, flat, d) ->
      let ctx, dl = type_defn_list muc ctx flat d in
      let e = type_prog ~loc:(e.pexpr_loc) muc ctx e in
      let add_def e (r,dl) = Edef (e, not r, dl) in
      List.fold_left add_def e (dl_split flat dl), []

and type_prog ?loc muc ctx d =
  let e, te = type_expr muc ctx d in
  if te <> [] then
    Loc.errorm ?loc "[coma typing] every program must be box-typed";
  e

and type_defn_list muc ctx flat dl =
  let tuc = muc.Pmodule.muc_theory in
  let ctx_full, dl =
    Lists.map_fold_left
      (fun acc { pdefn_desc = d; pdefn_loc=loc} ->
         let id, pl = d.pdefn_name, d.pdefn_params in
         let h = create_hsymbol (create_user_id id) in
         let pl, e = param_spec (true, id.id_str) true false pl d.pdefn_body in
         let _, params = Lists.map_fold_left (type_param tuc) ctx pl in
         let writes = List.map (find_ref ctx) d.pdefn_writes in
         add_hdl h writes params acc, (h, writes, params, loc, e))
      ctx dl in
  let ctx = if flat then ctx else ctx_full in
  let dl =
    List.map
      (fun (h, writes, params, loc, b) ->
         let ctx = List.fold_left add_param ctx params in
         let d = type_prog ~loc muc ctx b in
         h, writes, params, d)
      dl in
  ctx_full, dl

let type_defn_list muc flat dl =
  let _, dl = type_defn_list muc ctx0 flat dl in
  let add_hs muc (h,wr,pl,_) =
    Pmodule.add_pdecl ~vc:false muc (hs_register (h,wr,pl)) in
  let uc = List.fold_left add_hs muc dl in
  let add_def dll (r,dl) = (not r, dl) :: dll in
  uc, List.fold_left add_def [] (dl_split flat dl)
