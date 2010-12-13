
open Why
open Util
open Ident
open Ty
open Theory
open Term
open Decl
module E = Pgm_effect

(* types *)

type effect = Pgm_effect.t
type reference = Pgm_effect.reference

type pre = Term.fmla

type post_fmla = Term.vsymbol (* result *) * Term.fmla
type exn_post_fmla = Term.vsymbol (* result *) option * Term.fmla

type post = post_fmla * (Term.lsymbol * exn_post_fmla) list

type type_v =
  | Tpure of Ty.ty
  | Tarrow of binder list * type_c

and type_c =
  { c_result_type : type_v;
    c_effect      : effect;
    c_pre         : pre;
    c_post        : post; }

and binder = Term.vsymbol * type_v

(* purify: turns program types into logic types *)

let ts_arrow = 
  let v = List.map (fun s -> create_tvsymbol (Ident.id_fresh s)) ["a"; "b"] in
  Ty.create_tysymbol (Ident.id_fresh "arrow") v None

let make_arrow_type tyl ty =
  let arrow ty1 ty2 = Ty.ty_app ts_arrow [ty1; ty2] in
  List.fold_right arrow tyl ty

let rec uncurry_type = function
  | Tpure ty ->
      [], ty
  | Tarrow (bl, c) ->
      let tyl1 = List.map (fun (v,_) -> v.vs_ty) bl in
      let tyl2, ty = uncurry_type c.c_result_type in
      tyl1 @ tyl2, ty (* TODO: improve? *)

let purify v =
  let tyl, ty = uncurry_type v in
  make_arrow_type tyl ty

(* symbols *)

type psymbol = {
  p_ls : lsymbol;
  p_tv : type_v;
}

let create_psymbol id v = 
  let tyl, ty = uncurry_type v in
  let ls = create_lsymbol id tyl (Some ty) in
  { p_ls = ls; p_tv = v }

type esymbol = lsymbol

type mtsymbol = {
  mt_name  : ident;
  mt_args  : tvsymbol list;
  mt_model : ty option;
}

let create_mtsymbol name args model = { 
  mt_name  = id_register name;
  mt_args  = args;
  mt_model = model; 
}

let mt_equal = (==)

(* misc. functions *)

let v_result ty = create_vsymbol (id_fresh "result") ty

let exn_v_result ls = match ls.ls_args with
  | [] -> None
  | [ty] -> Some (v_result ty)
  | _ -> assert false

let post_map f ((v, q), ql) =
  (v, f q), List.map (fun (e,(v,q)) -> e, (v, f q)) ql

let type_c_of_type_v = function
  | Tarrow ([], c) ->
      c
  | v ->
      let ty = purify v in
      { c_result_type = v;
	c_effect      = Pgm_effect.empty;
	c_pre         = f_true;
	c_post        = (v_result ty, f_true), []; }

let rec subst_var ts s vs =
  let ty' = ty_inst ts vs.vs_ty in
  if ty_equal ty' vs.vs_ty then
    s, vs
  else
    let vs' = create_vsymbol (id_clone vs.vs_name) ty' in
    Mvs.add vs (t_var vs') s, vs'

and subst_post ts s ((v, q), ql) =
  let vq = let s, v = subst_var ts s v in v, f_ty_subst ts s q in
  let handler (e, (v, q)) = match v with
    | None -> e, (v, f_ty_subst ts s q)
    | Some v -> let s, v = subst_var ts s v in e, (Some v, f_ty_subst ts s q)
  in
  vq, List.map handler ql

let rec subst_type_c ef ts s c =
  { c_result_type = subst_type_v ef ts s c.c_result_type;
    c_effect      = E.subst ef c.c_effect;
    c_pre         = f_ty_subst ts s c.c_pre;
    c_post        = subst_post ts s c.c_post; }

and subst_type_v ef ts s = function
  | Tpure ty ->
      Tpure (ty_inst ts ty)
  | Tarrow (bl, c) ->
      let s, bl = Util.map_fold_left (binder ef ts) s bl in
      Tarrow (bl, subst_type_c ef ts s c)

and binder ef ts s (vs, v) =
  let v = subst_type_v ef ts s v in
  let s, vs = subst_var ts s vs in
  s, (vs, v)


let tpure ty = Tpure ty

let tarrow bl c = match bl with
  | [] ->
      invalid_arg "tarrow"
  | _ ->
      let rename (e, s) (vs, v) =
	let vs' = create_vsymbol (id_clone vs.vs_name) vs.vs_ty in
	let v' = subst_type_v e Mtv.empty s v in
	let e' = Mvs.add vs (E.Rlocal vs') e in
	let s' = Mvs.add vs (t_var vs') s in
	(e', s'), (vs', v')
      in
      let (e, s), bl' = Util.map_fold_left rename (Mvs.empty, Mvs.empty) bl in
      Tarrow (bl', subst_type_c e Mtv.empty s c)


let subst1 vs1 t2 = Mvs.add vs1 t2 Mvs.empty

let apply_type_v v vs = match v with
  | Tarrow ((x, tyx) :: bl, c) ->
      let ts = ty_match Mtv.empty (purify tyx) vs.vs_ty in
      let c = type_c_of_type_v (Tarrow (bl, c)) in
      subst_type_c Mvs.empty ts (subst1 x (t_var vs)) c
  | Tarrow ([], _) | Tpure _ ->
      assert false

let apply_type_v_ref v r = match r, v with
  | E.Rlocal vs as r, Tarrow ((x, tyx) :: bl, c) ->
      let ts = ty_match Mtv.empty (purify tyx) vs.vs_ty in
      let c = type_c_of_type_v (Tarrow (bl, c)) in
      let ef = Mvs.add x r Mvs.empty in
      subst_type_c ef ts (subst1 x (t_var vs)) c
  | E.Rglobal ls as r, Tarrow ((x, tyx) :: bl, c) ->
      let ty = match ls.ls_value with None -> assert false | Some ty -> ty in
      let ts = ty_match Mtv.empty (purify tyx) ty in
      let c = type_c_of_type_v (Tarrow (bl, c)) in
      let ef = Mvs.add x r Mvs.empty in
      subst_type_c ef ts (subst1 x (t_app ls [] ty)) c
  | _ ->
      assert false

let occur_formula r f = match r with
  | E.Rlocal vs  -> f_occurs_single vs f
  | E.Rglobal ls -> f_s_any (fun _ -> false) (ls_equal ls) f

let rec occur_type_v r = function
  | Tpure _ ->
      false
  | Tarrow (bl, c) ->
      occur_arrow r bl c

and occur_arrow r bl c = match bl with
  | [] ->
      occur_type_c r c
  | (vs, v) :: bl ->
      occur_type_v r v ||
      not (E.ref_equal r (E.Rlocal vs)) && occur_arrow r bl c

and occur_type_c r c =
  occur_type_v r c.c_result_type ||
  occur_formula r c.c_pre ||
  E.occur r c.c_effect ||
  occur_post r c.c_post

and occur_post r ((_, q), ql) =
  occur_formula r q ||
  List.exists (fun (_, (_, qe)) -> occur_formula r qe) ql

let rec eq_type_v v1 v2 = match v1, v2 with
  | Tpure ty1, Tpure ty2 ->
      ty_equal ty1 ty2
  | Tarrow _, Tarrow _ ->
      false (* TODO? *)
  | _ ->
      assert false

(* pretty-printers *)

open Pp
open Format
open Pretty

let print_post fmt ((_,q), el) =
  let print_exn_post fmt (l,(_,q)) =
    fprintf fmt "| %a -> {%a}" print_ls l print_fmla q
  in
  fprintf fmt "{%a} %a" print_fmla q (print_list space print_exn_post) el

let rec print_type_v fmt = function
  | Tpure ty ->
      print_ty fmt ty
  | Tarrow (bl, c) ->
      fprintf fmt "@[<hov 2>%a ->@ %a@]"
	(print_list arrow print_binder) bl print_type_c c

and print_type_c fmt c =
  fprintf fmt "@[{%a}@ %a%a@ %a@]" print_fmla c.c_pre
    print_type_v c.c_result_type Pgm_effect.print c.c_effect
    print_post c.c_post

and print_binder fmt (x, v) =
  fprintf fmt "(%a:%a)" print_vs x print_type_v v

(* let apply_type_v env v vs = *)
(*   eprintf "apply_type_v: v=%a vs=%a@." print_type_v v print_vs vs; *)
(*   apply_type_v env v vs *)

