(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2013   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ident
open Term
open Decl

let is_canonical x f =
  let vl,_,f = match f.t_node with
    | Tquant (Tforall,b) -> t_open_quant b
    | _ -> [],[],f in
  let hd,e = match f.t_node with
    | Tapp (ls, [hd; t]) when ls_equal ls ps_equ -> hd,t
    | Tbinop (Tiff, {t_node = Tapp (ls, [hd; t])}, f)
      when ls_equal ls ps_equ && t_equal t t_bool_true -> hd,f
    | _ -> raise Exit in
  let check_arg v t = match t.t_node with
    | Tvar u when vs_equal u v -> ()
    | _ -> raise Exit in
  let ls = match e.t_node with
    | Tapp (ls,tl) -> List.iter2 check_arg vl tl; ls
    | _ -> raise Exit in
  let rec check_head hd vl = match hd.t_node, vl with
    | Tapp (ls, [hd; {t_node = Tvar u}]), v :: vl
      when ls_equal ls fs_func_app && vs_equal u v -> check_head hd vl
    | Tvar y, [] when vs_equal y x -> ()
    | _ -> raise Exit in
  check_head hd (List.rev vl);
  ls

let is_canonical x f =
  try Some (is_canonical x f)
  with Exit | Invalid_argument _ -> None

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
  let ax = create_prop_decl Paxiom pr (t_forall_close vl [] f) in
  create_param_decl cs, ax, cs

let get_canonical =
  let ht = Hls.create 3 in fun ls ->
  try Hls.find ht ls with Not_found ->
  let res = get_canonical ls in
  Hls.add ht ls res; res

let rec lift_f acc t0 = match t0.t_node with
  | (Tapp (ps, [t1; {t_node = Teps fb}])
  | Tapp (ps, [{t_node = Teps fb}; t1]))
    when ls_equal ps ps_equ ->
      let vs, f = t_open_bound fb in
      let f = t_let_close_simp vs t1 f in
      lift_f acc (t_label_copy t0 f)
  | Teps fb ->
      let vl = Mvs.keys (t_vars t0) in
      let vs, f = t_open_bound fb in
      let acc, t = match is_canonical vs f with
        | Some ls ->
            let abst, axml = acc in
            let ld, ax, cs = get_canonical ls in
            (ld :: abst, ax :: axml), fs_app cs [] vs.vs_ty
        | None ->
            let (abst,axml), f = lift_f acc f in
            let tyl = List.map (fun x -> x.vs_ty) vl in
            let ls = create_fsymbol (id_clone vs.vs_name) tyl vs.vs_ty in
            let t = fs_app ls (List.map t_var vl) vs.vs_ty in
            let f = t_forall_close_merge vl (t_subst_single vs t f) in
            let id = id_derive (vs.vs_name.id_string ^ "_def") vs.vs_name in
            let ax = create_prop_decl Paxiom (create_prsymbol id) f in
            (create_param_decl ls :: abst, ax :: axml), t
      in
      acc, t_label_copy t0 t
  | _ ->
      t_map_fold lift_f acc t0

let lift_l (acc,dl) (ls,ld) =
  let vl, t, close = open_ls_defn_cb ld in
  match t.t_node with
  | Teps fb ->
      let vs, f = t_open_bound fb in
      let (abst,axml), f = lift_f acc f in
      let t = t_app ls (List.map t_var vl) t.t_ty in
      let f = t_forall_close_merge vl (t_subst_single vs t f) in
      let id = id_derive (ls.ls_name.id_string ^ "_def") ls.ls_name in
      let ax = create_prop_decl Paxiom (create_prsymbol id) f in
      (create_param_decl ls :: abst, ax :: axml), dl
  | _ ->
      let acc, t = lift_f acc t in
      acc, close ls vl t :: dl

let lift_d d = match d.d_node with
  | Dlogic dl ->
      let (abst,axml), dl = List.fold_left lift_l (([],[]),[]) dl in
      if dl = [] then List.rev_append abst (List.rev axml) else
      let d = create_logic_decl (List.rev dl) in
      let add_ax (axml1, axml2) ax =
        if Sid.disjoint ax.d_syms d.d_news
        then ax :: axml1, axml2 else axml1, ax :: axml2 in
      let axml1, axml2 = List.fold_left add_ax ([],[]) axml in
      List.rev_append abst (axml1 @ d :: axml2)
  | _ ->
      let (abst,axml), d = decl_map_fold lift_f ([],[]) d in
      List.rev_append abst (List.rev_append axml [d])

let eliminate_epsilon = Trans.decl lift_d None

let () = Trans.register_transform "eliminate_epsilon" eliminate_epsilon
  ~desc:"Eliminate@ lambda-terms@ and@ other@ comprehension@ forms."
