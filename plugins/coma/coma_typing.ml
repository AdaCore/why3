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
  hdls: (hsymbol * vsymbol list * param list * int ref) Mstr.t;
}

let ctx0 = {
  vars = Mstr.empty;
  denv = Dterm.denv_empty;
  hdls = Mstr.empty;
}

let add_hdl hs w pl ctx =
  let str = hs.hs_name.id_string in
  { ctx with hdls = Mstr.add str (hs, w, pl, ref 0) ctx.hdls }

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

let oc_hsymbol ctx {hs_name = id} =
  let h,_,_,oc = Mstr.find id.id_string ctx.hdls in
  assert (id_equal id h.hs_name);
  assert (not (Wid.mem hs_to_merge id));
  if !oc > 1 then Wid.set hs_to_merge id ()

let oc_param ctx = function
  | Pc (h, _, _) -> oc_hsymbol ctx h
  | Pt _ | Pv _ | Pr _ -> ()

let find_ref ctx (id: Ptree.ident) =
  try match Mstr.find id.id_str ctx.vars with
    | Ref v -> v
    | Var _
    | Typ _ -> Loc.errorm ~loc:id.id_loc "[coma typing] the symbol %s is not a reference" id.id_str
  with Not_found -> Loc.errorm ~loc:id.id_loc "[coma typing] unbound variable %s" id.id_str

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
      let _ctx1, params = Lists.map_fold_left (type_param tuc) ctx pl in
      let w = List.map (find_ref ctx) w in
      let hs = create_hsymbol (create_user_id id) in
      Pc (hs, w, params)
  | PPt id ->
      let ts = tv_of_string id.id_str in
      Pt ts

and type_param tuc ctx p =
  let p = type_param0 tuc ctx p in
  add_param ctx p, p

let type_term tuc ctx t =
  Typing.type_term_in_denv (Theory.get_namespace tuc) Theory.(tuc.uc_known) Theory.(tuc.uc_crcmap) ctx.denv t

let type_fmla tuc ctx t =
  Typing.type_fmla_in_denv (Theory.get_namespace tuc) Theory.(tuc.uc_known) Theory.(tuc.uc_crcmap) ctx.denv t

let rec check_param ~loc l r = match l,r with
  | Pt _l, Pt _r -> ()
  | Pr l, Pr r
  | Pv l, Pv r  when ty_equal l.vs_ty r.vs_ty -> ()
  | Pc (_, _, l), Pc (_, _, r) -> check_params ~loc l r
  | _ -> Loc.errorm ~loc "[coma typing] type error"

and check_params ~loc l r =
  try List.iter2 (check_param ~loc) l r
  with Invalid_argument _ -> Loc.errorm ~loc "[coma typing] bad arity: %d argument(s) expected, %d given" (List.length l) (List.length r)

(* let subs (tvs : tvsymbol) (pl : param list) =
  List.map (fun e -> )
    pl *)

module SCC = MakeSCC(Hid)

let defn_hs_iter fn (_,_,_,d) =
  (* we assume no collisions *)
  let rec inspect = function
    | Esym h -> fn h.hs_name
    | Edef (e,_,dl) ->
        let check (_,_,_,d) = inspect d
        in List.iter check dl; inspect e
    | Eapp (e, Ac d) -> inspect d; inspect e
    | Elet (e,_) | Ecut (_,e) | Ebox e
    | Eset (e,_) | Elam (_,e) | Ewox e
    | Eapp (e,_) -> inspect e
    | Eany -> () in
  inspect d

let rec type_expr tuc ctx { pexpr_desc=d; pexpr_loc=loc } =
  match d with
  | PEbox e     -> let e = type_prog ~loc tuc ctx e in Ebox e, []
  | PEwox e     -> let e = type_prog ~loc tuc ctx e in Ewox e, []
  | PEcut (t,e) -> let e = type_prog ~loc tuc ctx e in Ecut (type_fmla tuc ctx t, e), []
  | PEany       -> Eany, []
  | PEsym id ->
      let h, _, pl, oc =
        try
          Mstr.find id.id_str ctx.hdls
        with Not_found -> Loc.errorm ~loc:id.id_loc "[coma typing] unbounded handler `%s'" id.id_str
      in
      incr oc;
      Esym h, pl
  | PEapp (pe, a) ->
      let e, te = type_expr tuc ctx pe in
      (match te, a with
       | [], _ -> Loc.errorm ~loc:pe.pexpr_loc "[coma typing] the expression `%a' is already fully applied" PP.pp_expr e
       | Pv vs :: tes, PAv t ->
           let tt = type_term tuc ctx t in
           (match tt.t_ty with
            | Some ty when ty_equal ty vs.vs_ty -> ()
            | _ -> Loc.errorm ~loc:t.term_loc "[coma typing] type error in application");
           Eapp (e, Av tt), tes
       | Pr rs :: tes, PAr id ->
           let s =
             try match Mstr.find id.id_str ctx.vars with
               | Ref v -> v
               | Var _ | Typ _ -> Loc.errorm ~loc:id.id_loc "[coma typing] the symbol `%s' is not a reference" id.id_str
             with Not_found -> Loc.errorm ~loc:id.id_loc "[coma typing] unbounded variable `%s'" id.id_str
           in
           if ty_equal rs.vs_ty s.vs_ty then Eapp (e, Ar s), tes
           else Loc.errorm ~loc "[coma typing] type error in application"
       | Pc (_h, _vs, pl) :: tes, PAc ea ->
           let ea, tea = type_expr tuc ctx ea in
           check_params ~loc pl tea;
           Eapp (e, Ac ea), tes
       | Pt _tv :: tes, PAt pty ->
           let _ty = Typing.ty_of_pty tuc pty in
           Loc.errorm ~loc:loc "[coma typing] polymorphism is not supported yet", tes
       | _ -> Loc.errorm ~loc "[coma typing] type error with the application")
  | PElet (e, l) ->
      let ctx0 = ctx in
      let f ctx (id, t, pty, mut) =
        let tt = type_term tuc ctx0 t in
        let ty = Typing.ty_of_pty tuc pty in
        (match tt.t_ty with
         | Some tty when ty_equal tty ty -> ()
         | _ -> Loc.errorm ~loc:id.id_loc "[coma typing] type error with `&%s' assignation" id.id_str);
        let vs = create_vsymbol (create_user_id id) ty in
        let ctx = if mut then add_ref vs ctx else add_var vs ctx in
        ctx, (vs,tt, mut)
      in
      let ctx, ll = Lists.map_fold_left f ctx l in
      let e = type_prog ~loc tuc ctx e in
      Elet (e, ll), []
  | PEset (e, l) ->
      let f (id, t) =
        let tt = type_term tuc ctx t in
        let vs =
           try match Mstr.find id.id_str ctx.vars, tt.t_ty with
             | Ref v, Some tty when ty_equal tty v.vs_ty -> v
             | (Var _ | Typ _),_ -> Loc.errorm ~loc:id.id_loc "[coma typing] the symbol `%s' is not a reference" id.id_str
             | _ -> Loc.errorm ~loc:id.id_loc "[coma typing] type error with `&%s' assignation" id.id_str;
           with Not_found -> Loc.errorm ~loc:id.id_loc "[coma typing] unbounded variable `%s'" id.id_str in
        (vs,tt)
      in
      let ll = List.map f l in
      let e = type_prog ~loc tuc ctx e in
      Eset (e, ll), []
  | PElam (pl, e) ->
      let ctx, params = Lists.map_fold_left (type_param tuc) ctx pl in
      let e = type_prog ~loc:(e.pexpr_loc) tuc ctx e in
      List.iter (oc_param ctx) params;
      Elam (params, e), params
  | PEdef (e, notrec, d) ->
      let ctx, dl = type_defn_list tuc ctx notrec d in
      let e = type_prog ~loc:(e.pexpr_loc) tuc ctx e in
      List.iter (fun (h,_,_,_) -> oc_hsymbol ctx h) dl;
      if notrec then Edef (e, notrec, dl), [] else
      let defn_head (h,_,_,_) = h.hs_name in
      let dll = SCC.scc defn_head defn_hs_iter dl in
      let add_def e (r,dl) = Edef (e, not r, dl) in
      List.fold_left add_def e dll, []

and type_prog ?loc tuc ctx d =
  let e, te = type_expr tuc ctx d in
  if te <> [] then Loc.errorm ?loc "[coma typing] every programm must be box-typed";
  e

and type_defn_list tuc ctx notrec dl =
  let ctx_full, dl =
    Lists.map_fold_left
      (fun acc { pdefn_desc = d; pdefn_loc=loc} ->
         let id, pl = d.pdefn_name, d.pdefn_params in
         let h = create_hsymbol (create_user_id id) in
         let _, params = Lists.map_fold_left (type_param tuc) ctx0 pl in
         let writes = List.map (find_ref ctx) d.pdefn_writes in
         add_hdl h writes params acc, (h, writes, params, loc, d.pdefn_body))
      ctx dl in
  let ctx = if notrec then ctx else ctx_full in
  let dl =
    List.map
      (fun (h, writes, params, loc, b) ->
         let ctx = List.fold_left add_param ctx params in
         let d = type_prog ~loc tuc ctx b in
         List.iter (oc_param ctx) params;
         h, writes, params, d)
      dl in
  ctx_full, dl
