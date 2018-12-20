(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ident
open Ty
open Term
open Decl
open Expr
open Pdecl

(* helper functions for algebraic types *)

let is_projection ls = ls.ls_constr = 0 &&
  try (restore_rs ls).rs_field <> None
  with Not_found -> false

let ts_constructors kn ({ts_name = id} as ts) =
  let rec find = function
    | {d_news = s}::dl when not (Mid.mem id s) -> find dl
    | {d_node = Ddata dl}::_ -> List.assq ts dl
    | _ -> [] in
  find (Mid.find id kn).pd_pure

let ty_constructors kn ty = match ty.ty_node with
  | Tyapp (ts, _) -> ts_constructors kn ts
  | _ -> []

let ls_definition kn ({ls_name = id} as ls) =
  let rec find = function
    | {d_news = s}::dl when not (Mid.mem id s) -> find dl
    | {d_node = Dlogic dl}::_ -> Some (List.assq ls dl)
    | _ -> None in
  find (Mid.find id kn).pd_pure

let cs_fields kn cs =
  let ty = Opt.get cs.ls_value in
  List.assq cs (ty_constructors kn ty)

let select_field pj pjl tl =
  let rec find tl pjl = match tl, pjl with
    | t::_, Some ls::_ when ls_equal pj ls -> t
    | _::tl, _::pjl -> find tl pjl
    | _ -> raise Not_found in
  find tl pjl

(* we destruct tuples, units, and singleton records *)
let destructible kn ty =
  let check ls = match ls.ls_args with
    | [] | [_] -> true
    | _ -> is_fs_tuple ls in
  match ty_constructors kn ty with
  | [ls,_ as cs] when check ls -> Some cs
  | _ -> None

(* we inline projections of destructed types *)
let find_inlineable kn ls = match ls.ls_args with
  | [arg] when destructible kn arg <> None ->
      begin match ls_definition kn ls with
      | Some def ->
          let res = open_ls_defn def in
          begin match (snd res).t_node with
          | Tvar _ | Tconst _
          | Tapp (_, [{t_node = Tvar _}]) -> Some res
          | Tcase ({t_node = Tvar _}, [bt]) ->
              begin match t_open_branch bt with
              | _, {t_node = Tvar _} -> Some res
              | _ -> None end
          | _ -> None end
      | _ -> None end
  | _ -> None

let unfold_inlineable kn ls tl ty = match find_inlineable kn ls with
  | Some (vl, e) ->
      let mt = List.fold_left2 (fun mt x y ->
        ty_match mt x.vs_ty (t_type y)) Mtv.empty vl tl in
      let mv = List.fold_right2 Mvs.add vl tl Mvs.empty in
      Some (t_ty_subst (oty_match mt e.t_ty ty) mv e)
  | None -> None

exception FoundIdl of preid list

let rec add_quant kn d (vl,tl,f) ({vs_ty = ty} as v) =
  match destructible kn ty with
  | Some (ls, pjl) ->
      let s = ty_match Mtv.empty (Opt.get ls.ls_value) ty in
      let mk_v id ty = create_vsymbol id (ty_inst s ty) in
      let mk_id id d (pj: lsymbol option) =
      (* pj : projection symbol (if field is named),
         d  : depth of projection (starting at 0) *)
        let attrs =
          (* Introduce field attribute to reconstruct the term in
             counterexamples *)
          compute_model_trace_field (Opt.map (fun x -> x.ls_name) pj) d in
        id_clone ~attrs id in
      let clone id d = List.map (mk_id id d) pjl in
      let rec lookup_names f = match f.t_node with
        | Tcase ({t_node = Tvar u}, [bt]) when vs_equal u v ->
            begin match (fst (t_open_branch bt)).pat_node with
              | Pvar x -> raise (FoundIdl (clone x.vs_name 0))
              | Papp (cs, pl) when ls_equal ls cs ->
                  let name p pj = match p.pat_node with
                    | Pvar x -> id_clone x.vs_name
                    | _ -> mk_id v.vs_name d pj in
                  raise (FoundIdl (List.map2 name pl pjl))
              | Papp _ | Pwild | Por _ | Pas _ -> ()
            end
        | Tcase (t, [bt]) ->
            lookup_names t; lookup_names (snd (t_open_branch bt))
        | Tcase (t, _) | Tbinop (Timplies, _, t) -> lookup_names t
        | Tbinop (Tand, t1, t2) -> lookup_names t1; lookup_names t2
        | Tquant (_, qf) -> let _,_,f = t_open_quant qf in lookup_names f
        | _ -> () in
      let idl = try lookup_names f;
                    clone v.vs_name d
                with FoundIdl idl -> idl in
      let nvl = List.map2 mk_v idl ls.ls_args in
      let t = fs_app ls (List.map t_var nvl) ty in
      let f = t_let_close_simp v t f in
      let tl = tr_map (t_subst_single v t) tl in
      List.fold_left (add_quant kn (succ d)) (vl,tl,f) nvl
  | None ->
      (v::vl, tl, f)

let let_map fn env t1 tb =
  let x,t2,close = t_open_bound_cb tb in
  let t2 = fn (Mvs.add x t1 env) t2 in
  (* TODO/FIXME? convert (let x = if f then True else False in h)
     into (forall x. (x = True <-> f) -> h) ? *)
  t_let_simp t1 (close x t2)

let branch_map fn env t1 bl =
  let mk_b b =
    let p,t2,close = t_open_branch_cb b in close p (fn env t2) in
  t_case t1 (List.map mk_b bl)

let rec dive_to_constructor fn env t =
  let dive env t = dive_to_constructor fn env t in
  t_attr_copy t (match t.t_node with
    | Tvar x -> dive env (Mvs.find_exn Exit x env)
    | Tlet (t1,tb) -> let_map dive env t1 tb
    | Tcase (t1,bl) -> branch_map dive env t1 bl
    | Tif (f,t1,t2) -> t_if_simp f (dive env t1) (dive env t2)
    | Tapp (ls,tl) when ls.ls_constr > 0 -> fn env t ls tl
    | _ -> raise Exit)

let rec cs_equ env t1 t2 =
  if t_equal t1 t2 then t_true else
  let right cs1 tl1 env _t2 cs2 tl2 =
    if not (ls_equal cs1 cs2) then t_false else
    t_and_simp_l (List.map2 (cs_equ env) tl1 tl2) in
  let left t2 env _t1 cs1 tl1 =
    dive_to_constructor (right cs1 tl1) env t2 in
  try dive_to_constructor (left t2) env t1
  with Exit -> t_equ t1 t2

let flat_case t bl =
  let mk_b b = let p,t = t_open_branch b in [p],t in
  let mk_case = t_case_close and mk_let = t_let_close_simp in
  Pattern.compile_bare ~mk_case ~mk_let [t] (List.map mk_b bl)

let rec eval_match kn stop env t =
  let stop = stop || t.t_ty <> None ||
             Sattr.mem Ity.annot_attr t.t_attrs in
  let eval env t = eval_match kn stop env t in
  t_attr_copy t (match t.t_node with
    | Tapp (ls, [t1;t2]) when ls_equal ls ps_equ ->
        cs_equ env (eval env t1) (eval env t2)
    | Tnot { t_node = Tapp (ls, [t1;t2]) } when ls_equal ls ps_equ ->
        t_not_simp (cs_equ env (eval env t1) (eval env t2))
    | Tapp (ls, [t1]) when is_projection ls ->
        let t1 = eval env t1 in
        let fn _env _t2 cs tl =
          select_field ls (cs_fields kn cs) tl in
        begin try dive_to_constructor fn env t1
        with Exit -> t_app ls [t1] t.t_ty end
    | Tapp (ls, tl) ->
        begin match unfold_inlineable kn ls tl t.t_ty with
        | Some t -> eval env t
        | None -> t_map (eval env) t
        end
    | Tlet (t1, tb2) ->
        let t1 = eval env t1 in
        let_map eval env t1 tb2
    | Tcase (t1, bl1) ->
        let t1 = eval env t1 in
        let fn env t2 _cs _tl =
          eval env (Loc.try2 ?loc:t.t_loc flat_case t2 bl1) in
        begin try dive_to_constructor fn env t1
        with Exit -> branch_map eval env t1 bl1 end
    | Tquant (q, qf) ->
        let vl,tl,f,close = t_open_quant_cb qf in
        let add_quant (vl,tl,f as acc) ({vs_name = id} as v) =
          if stop && not (Sattr.mem Ity.break_attr id.id_attrs)
          then v::vl, tl, f else add_quant kn 0 acc v in
        let vl,tl,f = List.fold_left add_quant ([],tl,f) vl in
        t_quant_simp q (close (List.rev vl) tl (eval env f))
    | _ ->
        t_map (eval env) t)

let eval_match kn t = eval_match kn false Mvs.empty t
