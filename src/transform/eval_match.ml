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
open Task

let record_unfolding_threshold = 20
(* only unfold records whose number of fields (including subrecords) is smaller
 * or equal than this number *)

type inline = known_map -> lsymbol -> ty list -> ty option -> bool

let unfold def tl ty =
   (* Unfold the definition [defn], given the argument list [tl] and the
      expected type [ty] *)
  let vl, e = open_ls_defn def in
  let add (mt,mv) x y = ty_match mt x.vs_ty (t_type y), Mvs.add x y mv in
  let (mt,mv) = List.fold_left2 add (Mtv.empty, Mvs.empty) vl tl in
  let mt = oty_match mt e.t_ty ty in
  t_ty_subst mt mv e

let is_constructor kn ls =
   (* check whether logic symbol [ls] is a constructor; for this, [ls] must
      appear as a constructor in an algebraic data type definition *)
   match Mid.find ls.ls_name kn with
  | { d_node = Ddata dl } ->
      let constr (_,csl) = List.exists (fun (cs,_) -> ls_equal cs ls) csl in
      List.exists constr dl
  | _ -> false

let is_projection kn ls =
   (* check whether logic symbol [ls] is a projection; for this, [ls] must
      appear as a projection in an algebraic data type definition *)
   match Mid.find ls.ls_name kn with
  | { d_node = Ddata dl } ->
      let constr (_,csl) = List.exists (fun (cs,_) -> ls_equal cs ls) csl in
      not (List.exists constr dl)
  | _ -> false

let apply_projection kn ls t = match t.t_node with
   (* [ls] is a projection, [t] is a term of the form [mk a1 ... an];
      reduce the term to the [ai] that corresponds to the projection *)
  | Tapp (cs,tl) ->
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
  | _ -> assert false

let flat_case t bl =
  let mk_b b = let p,t = t_open_branch b in [p],t in
  let mk_case = t_case_close and mk_let = t_let_close_simp in
  Pattern.compile_bare ~mk_case ~mk_let [t] (List.map mk_b bl)

let rec add_quant kn (cnt, vl,tl,f) v =
  (* (vl,tl,f) represents a formula
        forall vl [tl]. f,
      on top of that we want to add a quantification for [v].
      If [v] is of record type (algebraic type with a single constructor), we
      do not add [v] directly, instead we transform [f] to
        let v = mk (v1 ... vn) in f
      and quantify over v1 ... vn.
      In case any of the vi are also of record type, we do the same.
      Actually, [add_quant] does *not* quantify, it just adds the let-form
      above and returns a triple
      (vl,tl,f) where
      vl - is the list of variables to quantify
      tl - triggers
      f  - formula
  *)
  let ty = v.vs_ty in
  let cl = match ty.ty_node with
    | Tyapp (ts, _) -> find_constructors kn ts
    | _ -> []
  in
  match cl with
    | [ls,pjl] ->
        (* there is only one constructor *)
        let s = ty_match Mtv.empty (Opt.get ls.ls_value) ty in
        let mk_v ty pj =
          (* The name of the field corresponding to the variable that is created  *)
          let field_name = (match pj with
            | Some pj_ls ->
              begin
                try
                  let fn = Ident.get_model_trace_string ~labels:pj_ls.ls_name.id_label in
                  if fn = "" then raise Not_found else fn
                with Not_found ->
                  (* No traceability information to SPARK code => the record field
                     will not be included in counterexample. *)
                  "@hide_field"

              end
            | _ -> ""
          ) in
          let label =
            if field_name = "@hide_field" then
              v.vs_name.id_label
            else
              Ident.append_to_model_element_name
                ~labels:v.vs_name.id_label ~to_append:(field_name) in
          create_vsymbol (id_lab label v.vs_name) (ty_inst s ty) in
        let nvl = List.map2 mk_v ls.ls_args pjl in
        let t = fs_app ls (List.map t_var nvl) ty in
        let f = t_let_close_simp v t f in
        let tl = tr_map (t_subst_single v t) tl in
        let cnt = cnt + 1 in
        (* in case any of the fields is also a record, we recurse over the new
           variables. *)
        List.fold_left (add_quant kn) (cnt, vl,tl,f) nvl
    | _ ->
        (* zero or more than one constructor *)
        (cnt, v::vl, tl, f)

let count_record_fields kn ty =
  (* if the type [ty] is a record type (= ADT with only one constructor), count
     the number of fields recursively (that is, unfolding types of fields that
     are also record types). *)
  let rec aux acc ty =
    let l =
      match ty.ty_node with
        | Tyapp (ts, _) -> find_constructors kn ts
        | _ -> []
    in
    match l with
    | [ls,_] ->
      List.fold_left (fun acc x -> aux (acc + 1) x) acc ls.ls_args
    | _ -> acc
  in
  aux 0 ty

let add_quant_small kn ((cnt, vl, tl, f) as tuple) v =
  (* wrapper around [add_quant] which does nothing if the variable is a record
     with more than [record_unfolding_threshold] fields. We also have an extra
     counter *)
  if cnt > record_unfolding_threshold ||
     count_record_fields kn v.vs_ty > record_unfolding_threshold then
    (cnt, v::vl, tl, f)
  else add_quant kn tuple v

let let_map fn env t1 tb =
  let x,t2,close = t_open_bound_cb tb in
  let t2 = fn (Mvs.add x t1 env) t2 in
  t_let_simp t1 (close x t2)

let branch_map fn env t1 bl =
  let mk_b b =
    let p,t2,close = t_open_branch_cb b in close p (fn env t2) in
  t_case t1 (List.map mk_b bl)

let dive_to_constructor kn fn env t =
  let rec dive env t = t_label_copy t (match t.t_node with
    | Tvar x -> dive env (Mvs.find_exn Exit x env)
    | Tlet (t1,tb) -> let_map dive env t1 tb
    | Tcase (t1,bl) -> branch_map dive env t1 bl
    | Tif (f,t1,t2) -> t_if_simp f (dive env t1) (dive env t2)
    | Tapp (ls,_) when is_constructor kn ls -> fn env t
    | _ -> raise Exit)
  in
  dive env t


let rec cs_equ kn env t1 t2 =
  if t_equal t1 t2 then t_true
  else
    let aux cs tl t =
      let fn = apply_cs_equ kn cs tl in
      try dive_to_constructor kn fn env t
      with Exit -> t_equ t1 t2
    in
    match t1,t2 with
    (* cannot merge the 2 patterns because of warning 57 *)
    | { t_node = Tapp (cs,tl) }, t
         when is_constructor kn cs -> aux cs tl t
    | t, { t_node = Tapp (cs,tl) }
         when is_constructor kn cs -> aux cs tl t
    | _ -> t_equ t1 t2

and apply_cs_equ kn cs1 tl1 env t = match t.t_node with
  | Tapp (cs2,tl2) when ls_equal cs1 cs2 ->
      let merge t1 t2 f = t_and_simp (cs_equ kn env t1 t2) f in
      List.fold_right2 merge tl1 tl2 t_true
  | Tapp _ -> t_false
  | _ -> assert false

let eval_match ~inline kn t =
  let rec eval stop env t =
    let stop = stop || Slab.mem Split_goal.stop_split t.t_label ||
    Slab.mem keep_on_simp_label t.t_label in
    let eval = eval stop in
    let t_eval_matched =
      (match t.t_node with
      | Tapp (ls, [t1;t2]) when ls_equal ls ps_equ ->
          cs_equ kn env (eval env t1) (eval env t2)
      | Tapp (ls, [t1]) when is_projection kn ls ->
          let t1 = eval env t1 in
          let fn _env t = apply_projection kn ls t in
          begin try dive_to_constructor kn fn env t1
          with Exit -> t_app ls [t1] t.t_ty end
      | Tapp (ls, tl) when inline kn ls (List.map t_type tl) t.t_ty ->
          begin match find_logic_definition kn ls with
            | None -> t_map (eval env) t
            | Some def -> eval env (unfold def tl t.t_ty)
          end
      | Tlet (t1, tb2) ->
          let t1 = eval env t1 in
          let_map eval env t1 tb2
      | Tcase (t1, bl1) ->
          let t1 = eval env t1 in
          let fn env t2 = eval env (Loc.try2 ?loc:t.t_loc flat_case t2 bl1) in
          begin try dive_to_constructor kn fn env t1
          with Exit -> branch_map eval env t1 bl1 end
      | Tquant (q, qf) ->
        let vl,tl,f,close = t_open_quant_cb qf in
        let _, vl,tl,f = if stop
          then (0, List.rev vl,tl,f)
          else List.fold_left (add_quant_small kn) (0,[],tl,f) vl in
        t_quant_simp q (close (List.rev vl) tl (eval env f))
      | _ ->
          t_map_simp (eval env) t)
    in

    (* Copy all labels of t to t_eval_matched except for "model_trace:*" label.
       This label is not copied if both t and t_eval_matched contain it. *)
    let t =
      (try
        let _ = Ident.get_model_trace_label ~labels:t_eval_matched.t_label in
        let original_mt_label = Ident.get_model_trace_label ~labels:t.t_label in
        (* If both t_eval_matched and t contain model_trace label, remove it *)
        t_label_remove original_mt_label t
       with Not_found -> t) in
    t_label_copy t t_eval_matched
  in
  eval false Mvs.empty t

let rec linear vars t = match t.t_node with
  | Tvar x -> Svs.add_new Exit x vars
  | Tif _ | Teps _ -> raise Exit
  | _ -> t_fold linear vars t

let linear t =
  try ignore (linear Svs.empty t); true with Exit -> false

let is_algebraic_type kn ty = match ty.ty_node with
  | Tyapp (ts, _) -> find_constructors kn ts <> []
  | Tyvar _ -> false

(* The following memoization by function definition is unsafe,
   since the same definition can be used in different contexts.
   If we could produce the record updates {| x with field = v |}
   that were linear (by eliminating occurrences of x.field in v),
   inline_nonrec_linear might not call eval_match at all and so
   be independent of the context. FIXME/TODO *)

let inline_cache = Wdecl.create 17

let rec inline_nonrec_linear kn ls tyl ty =
  (* at least one actual parameter (or the result) has an algebraic type *)
  List.exists (is_algebraic_type kn) (oty_cons tyl ty) &&
  (* and ls is not recursively defined and is linear *)
  let d = Mid.find ls.ls_name kn in
  if Mid.mem ls.ls_name d.d_syms then false else
  match d.d_node with
    | Dlogic [_,def] ->
        begin try Wdecl.find inline_cache d with Not_found ->
          let vl,t = open_ls_defn def in
          let _,_,_,t = List.fold_left (add_quant kn) (0,[],[],t) vl in
          let t = eval_match ~inline:inline_nonrec_linear kn t in
          let res = linear t in
          Wdecl.set inline_cache d res;
          res
        end
    | _ -> false


let eval_match_trans =
  let eval_match_fun = eval_match ~inline:inline_nonrec_linear in
  Trans.fold (fun th acc ->
      match th.task_decl.Theory.td_node with
      | Theory.Decl { d_node = Dprop (kind, sym, f) } ->
          let f = eval_match_fun th.task_known f in
          add_decl acc (create_prop_decl kind sym f)
      | _ -> add_tdecl acc th.task_decl) None

let () = Trans.register_transform
  "eval_match" eval_match_trans
  ~desc:"simplify pattern matching on constructors"
