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
open Term
open Decl

(* Canonical forms for epsilon terms. *)
type canonical =
  | Id of Ty.ty                    (* identity lambda    (\x (x_i). x (x_i)) *)
  | Eta of term                    (* eta-expansed term  (\(x_i). t (x_i))
                                      (x_i not in t's free variables)        *)
  | Partial of lsymbol * term list (* partial application
                                      (\(x_i). f (arguments) (x_i))
                                      (x_i not free in arguments)            *)
  | Nothing                        (* No canonical form found. *)

let canonicalize x f =
  let vl,_,f = match f.t_node with
    | Tquant (Tforall,b) -> t_open_quant b
    | _ -> [],[],f in
  let hd,e = match f.t_node with
    | Tapp (ls, [hd; t]) when ls_equal ls ps_equ -> hd,t
    | Tbinop (Tiff, {t_node = Tapp (ls, [hd; t])}, f)
      when ls_equal ls ps_equ && t_equal t t_bool_true ->
        hd, begin match f.t_node with
            | Tapp (ls, [t1;t2])
              when ls_equal ls ps_equ && t_equal t2 t_bool_true -> t1
            | _ -> f
            end
    | _ -> raise Exit in
  let rvl = List.rev vl in
  let rec match_args tl vl = match tl, vl with
    | _, [] -> let tvs = List.fold_left t_freevars Mvs.empty tl in
        if Mvs.set_disjoint tvs (Svs.of_list rvl) then tl else raise Exit
    | {t_node = Tvar u} :: tl, v :: vl when vs_equal u v -> match_args tl vl
    | _ -> raise Exit in
  let rec match_apps e vl = match e.t_node, vl with
    | _, [] ->
        if Mvs.set_disjoint (t_freevars Mvs.empty e) (Svs.of_list rvl)
        then Eta e
        else raise Exit
    | Tvar u, [v] when vs_equal u v -> Id v.vs_ty
    | Tapp (ls, [fn; {t_node = Tvar u}]), v :: vl
      when ls_equal ls fs_func_app ->
        if vs_equal u v then match_apps fn vl else raise Exit
    | Tapp (ls,tl), vl -> Partial (ls, match_args (List.rev tl) vl)
    | _ -> raise Exit in
  let canon = match_apps e rvl in
  let rec check_head hd vl = match hd.t_node, vl with
    | Tapp (ls, [hd; {t_node = Tvar u}]), v :: vl
      when ls_equal ls fs_func_app && vs_equal u v -> check_head hd vl
    | Tvar y, [] when vs_equal y x -> ()
    | _ -> raise Exit in
  check_head hd rvl;
  canon

let canonicalize x f =
  try canonicalize x f
  with Exit -> Nothing

let get_canonical ls =
  let ty = Opt.get_def Ty.ty_bool ls.ls_value in
  let ty = List.fold_right Ty.ty_func ls.ls_args ty in
  let nm = ls.ls_name.id_string ^ "_closure" in
  let cs = create_fsymbol (id_derive nm ls.ls_name) [] ty in
  let mk_vs ty = create_vsymbol (id_fresh "y") ty in
  let vl = List.map mk_vs ls.ls_args in
  let tl = List.map t_var vl in
  let t = List.fold_left t_func_app (fs_app cs [] ty) tl in
  let e = t_app ls tl ls.ls_value in
  let f = if ls.ls_value = None
    then t_iff (t_equ t t_bool_true) e else t_equ t e in
  let nm = ls.ls_name.id_string ^ "_closure_def" in
  let pr = create_prsymbol (id_derive nm ls.ls_name) in
  let ax = (pr, (t_forall_close vl [] f)) in
  create_param_decl cs, ax, cs

let id_canonical ty =
  let tyf = Ty.ty_func ty ty in
  let cs = create_fsymbol (id_fresh "identity") [] tyf in
  let vs = create_vsymbol (id_fresh "y") ty in
  let tvs = t_var vs in
  let eq = t_equ (t_func_app (fs_app cs [] tyf) tvs) tvs in
  let pr = create_prsymbol (id_fresh "identity_def") in
  let ax = (pr, (t_forall_close [vs] [] eq)) in
  create_param_decl cs, ax, cs

let get_canonical =
  let ht = Hls.create 3 in fun ls ->
  try Hls.find ht ls with Not_found ->
  let res = get_canonical ls in
  Hls.add ht ls res; res

let id_canonical =
  let ht = Ty.Hty.create 3 in fun ty ->
  try Ty.Hty.find ht ty with Not_found ->
  let res = id_canonical ty in
  Ty.Hty.add ht ty res; res

let poly_id_canonical =
  id_canonical (Ty.ty_var (Ty.tv_of_string "a"))

type to_elim =
  | All           (* eliminate all epsilon-terms *)
  | NonLambda     (* preserve lambda-terms *)
  | NonLambdaSet  (* preserve lambda-terms with value-typed body *)

let to_elim el t = match el with
  | All -> true
  | NonLambda -> not (t_is_lambda t)
  | NonLambdaSet ->
      let vl,_,t = t_open_lambda t in
      vl = [] || t.t_ty = None

let rec lift_f el bv acc t0 =
  let elim_eps_eq t1 fb t2 =
      let vs, f = t_open_bound fb in
      if canonicalize vs f <> Nothing then
        match t1.t_node with
        | Teps fb when to_elim el t1 ->
            let vs, f = t_open_bound fb in
            if canonicalize vs f <> Nothing then
              t_map_fold (lift_f el bv) acc t0
            else
              let f = t_let_close_simp vs t2 f in
              lift_f el bv acc (t_attr_copy t0 f)
        | _ ->
            t_map_fold (lift_f el bv) acc t0
      else
        let f = t_let_close_simp vs t1 f in
        lift_f el bv acc (t_attr_copy t0 f)
  in
  match t0.t_node with
    (* cannot merge the 2 patterns because of warning 57 *)
    (* This code is suspicious for negative polarity *)
  (*| Tapp (ps, [t1; {t_node = Teps fb} as t2])
    when ls_equal ps ps_equ && to_elim el t2 ->
     elim_eps_eq t1 fb t2
  | Tapp (ps, [{t_node = Teps fb} as t2; t1])
    when ls_equal ps ps_equ && to_elim el t2 ->
     elim_eps_eq t1 fb t2*)
  | Teps fb when to_elim el t0 ->
      let vl = Mvs.keys (Mvs.set_diff (t_vars t0) bv) in
      let vs, f = t_open_bound fb in
      let acc, t = match canonicalize vs f with
        | Id ty ->
            let ld, ax, cs = if Ty.ty_closed ty then
              id_canonical ty else poly_id_canonical in
            let abst, axml = acc in
            (ld :: abst, ax :: axml), fs_app cs [] vs.vs_ty
        | Eta t -> lift_f el bv acc t
        | Partial (ls, rargs) ->
            let ld, ax, cs = get_canonical ls in
            let args, ty, acc = List.fold_left (fun (args, ty, acc) x ->
                let acc, y = lift_f el bv acc x in
                y :: args, Ty.ty_func (t_type y) ty, acc
              ) ([], vs.vs_ty, acc) rargs in
            let abst, axml = acc in
            let apply f x = t_app_infer fs_func_app [f;x] in
            let ap = List.fold_left apply (fs_app cs [] ty) args in
            (ld :: abst, ax :: axml), ap
        | Nothing ->
            (* case \x. x = t /\ f *)
            (* do not generate a new name for x, use t instead *)
            match f.t_node with
              | Tbinop (Tand, {t_node = Tapp (ls, [{t_node = Tvar y}; t])}, f)
	          when vs_equal y vs &&
	          ls_equal ls ps_equ &&
	          not (Mvs.mem vs (t_freevars Mvs.empty t)) ->
	          let acc, f = lift_f el bv acc f in
	          let (abst,axml), t = lift_f el bv acc t in
                  let f = t_forall_close_merge vl (t_subst_single vs t f) in
                  let id = id_derive (vs.vs_name.id_string ^ "_def") vs.vs_name
		  in
                  let ax = (create_prsymbol id, f) in
                  (abst, ax :: axml), t
	      | _ ->
                  let (abst,axml), f = lift_f el bv acc f in
                  let tyl = List.map (fun x -> x.vs_ty) vl in
                  let ls = create_fsymbol (id_clone vs.vs_name) tyl vs.vs_ty in
                  let t = fs_app ls (List.map t_var vl) vs.vs_ty in
                  let f = t_forall_close_merge vl (t_subst_single vs t f) in
                  let id = id_derive (vs.vs_name.id_string ^ "_def") vs.vs_name
                  in
                  let ax = (create_prsymbol id, f) in
                  (create_param_decl ls :: abst, ax :: axml), t
      in
      acc, t_attr_copy t0 t
  | Teps _ ->
      let vl,tr,t = t_open_lambda t0 in
      let acc, t = lift_f el bv acc t in
      let acc, tr = Lists.map_fold_left
                      (Lists.map_fold_left (lift_f el bv))
                      acc tr in
      acc, t_attr_copy t0 (t_lambda vl tr t)
  | _ ->
      let acc, t = t_map_fold (lift_f el bv) acc t0 in
      acc, t_attr_copy t0 t

let rec lift_q el pol acc t0 =
  let binop = if pol then Tand else Timplies in
  let acc, t = match t0.t_node with
  | Tquant (Tforall, _)
  | Tbinop (Tand, _, _)
  | Tbinop (Tor, _, _) -> t_map_fold (lift_q el pol) acc t0
  | Tbinop (Timplies, t1, t2) ->
    let (abst, axml), t1 = lift_f el (t_freevars Mvs.empty t1) acc t1 in
    let acc, t2 = lift_q el pol (abst, []) t2 in
    let t = List.fold_left (fun t (_, ax) -> t_binary binop ax t)
      (t_binary Timplies t1 t2) axml in
    acc, t
  | Tlet (t1, bt2) ->
    let (x, t2) = t_open_bound bt2 in
    let (abst, axml), t1 = lift_f el (t_freevars Mvs.empty t1) acc t1 in
    let acc, t2 = lift_q el pol (abst, []) t2 in
    let t = List.fold_left (fun t (_, ax) -> t_binary binop ax t)
      (t_let t1 (t_close_bound x t2)) axml in
    acc, t
  | _ ->
    let (abst, axml), t = lift_f el (t_freevars Mvs.empty t0) acc t0 in
    let t = List.fold_left (fun t (_, ax) -> t_binary binop ax t) t axml in
      (abst, []), t
  in
  acc, t_attr_copy t0 t

let lift_l el (acc,dl) (ls,ld) =
  let vl, t, close = open_ls_defn_cb ld in
  (* remove special case for function declaration to keep definitions when
     no new symbol is generated for fb *)
  (* match t.t_node with
  | Teps fb when to_elim el t ->
      let vs, f = t_open_bound fb in
      let (abst,axml), f = lift_f el acc f in
      let t = t_app ls (List.map t_var vl) t.t_ty in
      let f = t_forall_close_merge vl (t_subst_single vs t f) in
      let id = id_derive (ls.ls_name.id_string ^ "_def") ls.ls_name in
      let ax = (create_prsymbol id, f) in
      (create_param_decl ls :: abst, ax :: axml), dl
  | _ -> *)
      let acc, t = lift_f el Mvs.empty acc t in
      acc, close ls vl t :: dl

let lift_d el d = match d.d_node with
  | Dlogic dl ->
      let (abst,axml), dl = List.fold_left (lift_l el) (([],[]),[]) dl in
      if dl = [] then List.rev_append abst
        (List.rev_map (fun (id, f) -> create_prop_decl Paxiom id f) axml) else
      let d = create_logic_decl (List.rev dl) in
      let add_ax (axml1, axml2) (id, f) =
        let ax = create_prop_decl Paxiom id f in
        if Sid.disjoint ax.d_syms d.d_news
        then ax :: axml1, axml2 else axml1, ax :: axml2 in
      let axml1, axml2 = List.fold_left add_ax ([],[]) axml in
      List.rev_append abst (axml1 @ d :: axml2)
  (* for goals and axioms, introduce assumptions after top-level quantifier
     and guards *)
  | Dprop (Pgoal, _, _) ->
      let (abst,axml), d = decl_map_fold (lift_q el false) ([],[]) d in
      List.rev_append abst
        (List.fold_left (fun l (id, f) ->
                           (create_prop_decl Paxiom id f) :: l) [d] axml)
  | Dprop (Paxiom, _, _) ->
      let (abst,axml), d = decl_map_fold (lift_q el true) ([],[]) d in
      List.rev_append abst
        (List.fold_left (fun l (id, f) ->
                           (create_prop_decl Paxiom id f) :: l) [d] axml)
  | _ ->
      let (abst,axml), d = decl_map_fold (lift_f el Mvs.empty) ([],[]) d in
      List.rev_append abst
      (List.fold_left (fun l (id, f) ->
			   (create_prop_decl Paxiom id f) :: l) [d] axml)

let eliminate_epsilon     = Trans.decl (lift_d All) None
let eliminate_nl_epsilon  = Trans.decl (lift_d NonLambda) None
let eliminate_nls_epsilon = Trans.decl (lift_d NonLambdaSet) None

let () = Trans.register_transform "eliminate_epsilon" eliminate_epsilon
  ~desc:"Eliminate@ lambda-terms@ and@ other@ comprehension@ forms."

let () = Trans.register_transform "eliminate_non_lambda_epsilon"
  eliminate_nl_epsilon
  ~desc:"Eliminate@ all@ comprehension@ forms@ except@ lambda-terms."

let () = Trans.register_transform "eliminate_non_lambda_set_epsilon"
  eliminate_nls_epsilon
  ~desc:"Eliminate@ all@ comprehension@ forms@ except@ value-typed@ lambda-terms."
