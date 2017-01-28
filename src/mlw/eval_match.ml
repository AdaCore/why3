(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2016   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Stdlib
open Ident
open Ty
open Term
open Decl
open Ity
open Expr
open Pdecl

(* helper functions for algebraic types *)

let ls_of_rs s = match s.rs_logic with
  RLls ls -> ls | _ -> assert false

let is_projection kn ls = ls.ls_constr = 0 &&
  match Mid.find ls.ls_name kn with
  | { pd_node = PDtype _ } -> true
  | _ -> false

let find_constructors kn ({ts_name = id} as ts) =
  let rec find = function
    | {d_news = s}::dl when not (Mid.mem id s) -> find dl
    | {d_node = Ddata dl}::_ -> List.assq ts dl
    | _ -> [] in
  find (Mid.find id kn).pd_pure

let find_logic_definition kn ({ls_name = id} as ls) =
  let rec find = function
    | {d_news = s}::dl when not (Mid.mem id s) -> find dl
    | {d_node = Dlogic dl}::_ -> Some (List.assq ls dl)
    | _ -> None in
  find (Mid.find id kn).pd_pure

let apply_projection kn ls cs tl =
  let ts = match cs.ls_value with
    | Some { ty_node = Tyapp (ts,_) } -> ts
    | _ -> assert false in
  let pjl =
    try List.assq cs (find_constructors kn ts)
    with Not_found -> assert false in
  let find acc v = function
    | Some pj when ls_equal pj ls -> v
    | _ -> acc in
  List.fold_left2 find t_true tl pjl

(* Part I - Invariant handling *)

let ls_valid =
  let v = create_tvsymbol (id_fresh "a") in
  create_psymbol (id_fresh "valid") [ty_var v]

(* Integer "points" represent individual values whose invariant
   may be broken. The special point 0 represents any value with
   verified invariant. Fresh points are assigned to values from
   top to bottom, so that a lesser point can never be reached
   from a greater point. Each point is associated to a list of
   fresh variables that correspond to the "temporary fields" of
   the point. Committing a point means that we prove that the
   temporary fields satisfy the invariant and then assume that
   the temporary fields are equal to the respective projections.

   Recursive "caps" represent deconstructible values from which
   points can be reached. Each variable is associated to a cap.
   A cap is either a zero point (committed value), a non-zero
   point (a record with a breakable invariant), a constructible
   value (characterized by the set of possible constructors),
   or a record with an unbreakable invariant. *)

type cap =
  | P of int            (* point *)
  | C of cap list Mls.t (* algebraic type *)
  | R of cap Mls.t      (* record with unbreakable invariant *)

type point = {
  p_leaf   : term;                  (* term we can be reached from *)
  p_stem   : (term * pattern) list; (* deconstruction from a root *)
  p_fields : (vsymbol * cap) Mls.t; (* temporary fields *)
}

type binding =
  | E of point  (* endpoint *)
  | L of int    (* link *)

type state = {
  s_roots  : cap Mvs.t;       (* non-broken roots may be unbound *)
  s_points : binding Mint.t;  (* non-broken points may be unbound *)
}

let new_point =
  let c = ref 0 in
  fun () -> incr c; !c

(* notes:
  - do not collapse on Eif and Ecase in k_expr when the type is fragile
*)

let add_var kn st v =
  let rp = ref st.s_points in
  let rec down stem leaf ty = match ty.ty_node with
    | Tyvar _ -> P 0
    | Tyapp (s, tl) ->
        let s = restore_its s in
        if not s.its_fragile && (* no need to go any further *)
           List.for_all (fun f -> f.its_frozen) s.its_arg_flg &&
           List.for_all (fun f -> f.its_frozen) s.its_reg_flg then P 0 else
        let sbs = List.fold_right2 Mtv.add s.its_ts.ts_args tl Mtv.empty in
        let d = find_its_defn kn s in
        if s.its_nonfree then if s.its_fragile then (* breakable record *)
          assert false (* TODO *)
        else (* unbreakable record *)
          let add_field m f =
            let pj = ls_of_rs f in
            let ty = Ty.ty_inst sbs (Opt.get f.rs_field).pv_vs.vs_ty in
            match down stem (fs_app pj [leaf] ty) ty with
            | P 0 -> m | c -> Mls.add pj c m in
          let pjs = List.fold_left add_field Mls.empty d.itd_fields in
          if Mls.is_empty pjs then P 0 else R pjs
        else (* constructible type *)
          let add_field m f = Mpv.add (Opt.get f.rs_field) (ls_of_rs f) m in
          let pjm = List.fold_left add_field Mpv.empty d.itd_fields in
          let add_constr m c =
            let cs = ls_of_rs c in
            let inst f = Ty.ty_inst sbs f.pv_vs.vs_ty in
            let tyl = List.map inst c.rs_cty.cty_args in
            let conv_field f ty_f =
              match Mpv.find_opt f pjm with
              | Some pj -> down stem (fs_app pj [leaf] ty_f) ty_f
              | None ->
                  let pat_arg ({pv_vs = v} as a) ty = if pv_equal a f
                    then pat_var (create_vsymbol (id_clone v.vs_name) ty)
                    else pat_wild ty in
                  let pl = List.map2 pat_arg c.rs_cty.cty_args tyl in
                  let pat = pat_app cs pl ty in
                  let v = Svs.choose pat.pat_vars in
                  down ((leaf, pat)::stem) (t_var v) ty_f in
            Mls.add cs (List.map2 conv_field c.rs_cty.cty_args tyl) m in
          let css = List.fold_left add_constr Mls.empty d.itd_constructors in
          let chk _ l = List.for_all (function P 0 -> true | _ -> false) l in
          if Mls.for_all chk css then P 0 else C css
  in
  match down [] (t_var v) v.vs_ty with
  | P 0 -> st (* not broken *)
  | c -> { s_roots = Mvs.add v c st.s_roots; s_points = !rp }

(* Part II - EvalMatch simplification *)

(* we destruct tuples, units, and singleton records *)
let destructible kn ty =
  let cl = match ty.ty_node with
    | Tyapp (ts, _) -> find_constructors kn ts
    | _ -> [] in
  match cl with
    | [ls,_] when is_fs_tuple ls -> Some ls
    | [{ls_args = [_]} as ls, _] -> Some ls
    | [{ls_args = []}  as ls, _] -> Some ls
    | _ -> None

(* we inline projections of destructed types *)
let find_inlineable kn ls = match ls.ls_args with
  | [arg] when destructible kn arg <> None ->
      begin match find_logic_definition kn ls with
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

let rec add_quant kn (vl,tl,f) ({vs_ty = ty} as v) =
  match destructible kn ty with
  | Some ls ->
      let s = ty_match Mtv.empty (Opt.get ls.ls_value) ty in
      let mk_v ty = create_vsymbol (id_clone v.vs_name) (ty_inst s ty) in
      let nvl = List.map mk_v ls.ls_args in
      let t = fs_app ls (List.map t_var nvl) ty in
      let f = t_let_close_simp v t f in
      let tl = tr_map (t_subst_single v t) tl in
      List.fold_left (add_quant kn) (vl,tl,f) nvl
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
  t_label_copy t (match t.t_node with
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
  let stop = stop || Slab.mem Term.stop_split t.t_label in
  let eval env t = eval_match kn stop env t in
  t_label_copy t (match t.t_node with
    | Tapp (ls, [t1;t2]) when ls_equal ls ps_equ ->
        cs_equ env (eval env t1) (eval env t2)
    | Tapp (ls, [t1]) when is_projection kn ls ->
        let t1 = eval env t1 in
        let fn _env _t2 cs tl = apply_projection kn ls cs tl in
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
        let vl,tl,f = if stop then List.rev vl,tl,f else
          List.fold_left (add_quant kn) ([],tl,f) vl in
        t_quant_simp q (close (List.rev vl) tl (eval env f))
    | _ ->
        t_map (eval env) t)

let eval_match kn t = eval_match kn false Mvs.empty t
