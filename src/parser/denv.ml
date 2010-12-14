(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Format
open Pp
open Util
open Ptree
open Ident
open Ty
open Term
open Theory

exception AnyMessage of string

let error ?loc e = match loc with
  | None -> raise e
  | Some loc -> raise (Loc.Located (loc,e))

let () = Exn_printer.register (fun fmt e -> match e with
  | AnyMessage s -> fprintf fmt "%s" s
  | _ -> raise e)

(** types with destructive type variables *)

type dty =
  | Tyvar of type_var
  | Tyapp of tysymbol * dty list

and type_var = {
  tag : int;
  user : bool;
  tvsymbol : tvsymbol;
  mutable type_val : dty option;
  type_var_loc : loc option;
}

let tvsymbol_of_type_var tv = tv.tvsymbol

let rec print_dty fmt = function
  | Tyvar { type_val = Some t } ->
      print_dty fmt t
  | Tyvar { type_val = None; tvsymbol = v } ->
      fprintf fmt "'%s" v.tv_name.id_string
  | Tyapp (s, []) ->
      fprintf fmt "%s" s.ts_name.id_string
  | Tyapp (s, [t]) ->
      fprintf fmt "%s %a" s.ts_name.id_string print_dty t
  | Tyapp (s, l) ->
      fprintf fmt "%s %a" s.ts_name.id_string (print_list comma print_dty) l

let create_ty_decl_var =
  let t = ref 0 in
  fun ?loc ~user tv ->
    incr t;
    { tag = !t; user = user; tvsymbol = tv; type_val = None;
      type_var_loc = loc }

let rec occurs v = function
  | Tyvar { type_val = Some t } -> occurs v t
  | Tyvar { tag = t; type_val = None } -> v.tag = t
  | Tyapp (_, l) -> List.exists (occurs v) l

(* destructive type unification *)
let rec unify t1 t2 = match t1, t2 with
  | Tyvar { type_val = Some t1 }, _ ->
      unify t1 t2
  | _, Tyvar { type_val = Some t2 } ->
      unify t1 t2
  | Tyvar v1, Tyvar v2 when v1.tag = v2.tag ->
      true
	(* instantiable variables *)
  | Tyvar ({user=false} as v), t
  | t, Tyvar ({user=false} as v) ->
      not (occurs v t) && (v.type_val <- Some t; true)
	(* recursive types *)
  | Tyapp (s1, l1), Tyapp (s2, l2) ->
      ts_equal s1 s2 && List.length l1 = List.length l2 &&
	  List.for_all2 unify l1 l2
  | Tyapp _, _ | _, Tyapp _ ->
      false
	(* other cases *)
  | Tyvar {user=true; tag=t1}, Tyvar {user=true; tag=t2} ->
      t1 = t2

(* intermediate types -> types *)
let rec ty_of_dty = function
  | Tyvar { type_val = Some t } ->
      ty_of_dty t
  | Tyvar { type_val = None; user = false; type_var_loc = loc } ->
      error ?loc (AnyMessage "undefined type variable")
  | Tyvar { tvsymbol = tv } ->
      ty_var tv
  | Tyapp (s, tl) ->
      ty_app s (List.map ty_of_dty tl)

type ident = Ptree.ident

type dpattern = { dp_node : dpattern_node; dp_ty : dty }

and dpattern_node =
  | Pwild
  | Pvar of ident
  | Papp of lsymbol * dpattern list
  | Por of dpattern * dpattern
  | Pas of dpattern * ident

let rec pattern_env env p = match p.dp_node with
  | Pwild -> env
  | Papp (_, pl) -> List.fold_left pattern_env env pl
  | Por (p, _) -> pattern_env env p
  | Pvar { id = x ; id_loc = loc } ->
      let ty = ty_of_dty p.dp_ty in
      let vs = create_vsymbol (id_user x loc) ty in
      Mstr.add x vs env
  | Pas (p, { id = x ; id_loc = loc }) ->
      let ty = ty_of_dty p.dp_ty in
      let vs = create_vsymbol (id_user x loc) ty in
      pattern_env (Mstr.add x vs env) p

let get_pat_var env p x = try Mstr.find x env with Not_found ->
  raise (Term.UncoveredVar (create_vsymbol (id_fresh x) (ty_of_dty p.dp_ty)))

let rec pattern_pat env p = match p.dp_node with
  | Pwild -> pat_wild (ty_of_dty p.dp_ty)
  | Pvar x -> pat_var (get_pat_var env p x.id)
  | Pas (p, x) -> pat_as (pattern_pat env p) (get_pat_var env p x.id)
  | Por (p, q) -> pat_or (pattern_pat env p) (pattern_pat env q)
  | Papp (s, pl) ->
      pat_app s (List.map (pattern_pat env) pl) (ty_of_dty p.dp_ty)

let pattern env p = let env = pattern_env env p in env, pattern_pat env p

type dterm = { dt_node : dterm_node; dt_ty : dty }

and dterm_node =
  | Tvar of string
  | Tconst of constant
  | Tapp of lsymbol * dterm list
  | Tif of dfmla * dterm * dterm
  | Tlet of dterm * ident * dterm
  | Tmatch of dterm * (dpattern * dterm) list
  | Tnamed of label * dterm
  | Teps of ident * dty * dfmla

and dfmla =
  | Fapp of lsymbol * dterm list
  | Fquant of quant * (ident * dty) list * dtrigger list list * dfmla
  | Fbinop of binop * dfmla * dfmla
  | Fnot of dfmla
  | Ftrue
  | Ffalse
  | Fif of dfmla * dfmla * dfmla
  | Flet of dterm * ident * dfmla
  | Fmatch of dterm * (dpattern * dfmla) list
  | Fnamed of label * dfmla
  | Fvar of fmla

and dtrigger =
  | TRterm of dterm
  | TRfmla of dfmla

let rec term env t = match t.dt_node with
  | Tvar x ->
      assert (Mstr.mem x env);
      t_var (Mstr.find x env)
  | Tconst c ->
      t_const c
  | Tapp (s, tl) ->
      t_app s (List.map (term env) tl) (ty_of_dty t.dt_ty)
  | Tif (f, t1, t2) ->
      t_if (fmla env f) (term env t1) (term env t2)
  | Tlet (e1, { id = x ; id_loc = loc }, e2) ->
      let ty = ty_of_dty e1.dt_ty in
      let e1 = term env e1 in
      let v = create_vsymbol (id_user x loc) ty in
      let env = Mstr.add x v env in
      let e2 = term env e2 in
      t_let_close v e1 e2
  | Tmatch (t1, bl) ->
      let branch (p,e) =
        let env, p = pattern env p in t_close_branch p (term env e)
      in
      t_case (term env t1) (List.map branch bl)
  | Tnamed (x, e1) ->
      let e1 = term env e1 in
      t_label_add x e1
  | Teps ({ id = x ; id_loc = loc }, ty, e1) ->
      let ty = ty_of_dty ty in
      let v = create_vsymbol (id_user x loc) ty in
      let env = Mstr.add x v env in
      let e1 = fmla env e1 in
      t_eps_close v e1

and fmla env = function
  | Ftrue ->
      f_true
  | Ffalse ->
      f_false
  | Fnot f ->
      f_not (fmla env f)
  | Fbinop (op, f1, f2) ->
      f_binary op (fmla env f1) (fmla env f2)
  | Fif (f1, f2, f3) ->
      f_if (fmla env f1) (fmla env f2) (fmla env f3)
  | Fquant (q, uqu, trl, f1) ->
      let uquant env ({ id = x ; id_loc = loc },ty) =
        let ty = ty_of_dty ty in
        let v = create_vsymbol (id_user x loc) ty in
        Mstr.add x v env, v
      in
      let env, vl = map_fold_left uquant env uqu in
      let trigger = function
	| TRterm t -> Term (term env t)
	| TRfmla f -> Fmla (fmla env f)
      in
      let trl = List.map (List.map trigger) trl in
      f_quant_close q vl trl (fmla env f1)
  | Fapp (s, tl) ->
      f_app s (List.map (term env) tl)
  | Flet (e1, { id = x ; id_loc = loc }, f2) ->
      let ty = ty_of_dty e1.dt_ty in
      let e1 = term env e1 in
      let v = create_vsymbol (id_user x loc) ty in
      let env = Mstr.add x v env in
      let f2 = fmla env f2 in
      f_let_close v e1 f2
  | Fmatch (t, bl) ->
      let branch (p,e) =
        let env, p = pattern env p in f_close_branch p (fmla env e)
      in
      f_case (term env t) (List.map branch bl)
  | Fnamed (x, f1) ->
      let f1 = fmla env f1 in
      f_label_add x f1
  | Fvar f ->
      f

(* Specialize *)

let find_type_var ~loc env tv =
  try
    Htv.find env tv
  with Not_found ->
    let v = create_ty_decl_var ~loc ~user:false tv in
    Htv.add env tv v;
    v

let rec specialize_ty ~loc env t = match t.ty_node with
  | Ty.Tyvar tv ->
      Tyvar (find_type_var ~loc env tv)
  | Ty.Tyapp (s, tl) ->
      Tyapp (s, List.map (specialize_ty ~loc env) tl)

let specialize_lsymbol ~loc s =
  let tl = s.ls_args in
  let t = s.ls_value in
  let env = Htv.create 17 in
  List.map (specialize_ty ~loc env) tl, option_map (specialize_ty ~loc env) t

let ident_of_vs ~loc vs =
  { id     = vs.vs_name.id_string;
    id_lab = vs.vs_name.id_label;
    id_loc = match vs.vs_name.id_origin with
      | User loc -> loc
      | _ -> loc }

let rec specialize_pattern ~loc htv p =
  { dp_node = specialize_pattern_node  ~loc htv p.pat_node;
    dp_ty   = specialize_ty            ~loc htv p.pat_ty; }

and specialize_pattern_node ~loc htv = function
  | Term.Pwild ->
      Pwild
  | Term.Pvar v ->
      Pvar (ident_of_vs ~loc v)
  | Term.Papp (s, pl) ->
      Papp (s, List.map (specialize_pattern ~loc htv) pl)
  | Term.Pas (p, v) ->
      Pas (specialize_pattern ~loc htv p, ident_of_vs ~loc v)
  | Term.Por (p, q) ->
      Por (specialize_pattern ~loc htv p, specialize_pattern ~loc htv q)

let rec specialize_term ~loc htv t =
  let dt =
    { dt_node = specialize_term_node  ~loc htv t.t_node;
      dt_ty   = specialize_ty         ~loc htv t.t_ty; }
  in
  List.fold_left (fun t l -> { t with dt_node = Tnamed (l, t) }) dt t.t_label

and specialize_term_node ~loc htv = function
  | Term.Tbvar _ ->
      assert false
  | Term.Tvar v ->
      Tvar v.vs_name.id_string (* TODO: correct? is capture possible? *)
  | Term.Tconst c ->
      Tconst c
  | Term.Tapp (ls, tl) ->
      Tapp (ls, List.map (specialize_term ~loc htv) tl)
  | Term.Tif (f, t1, t2) ->
      Tif (specialize_fmla ~loc htv f,
	   specialize_term ~loc htv t1, specialize_term ~loc htv t2)
  | Term.Tlet (t1, t2) ->
      let v, t2 = t_open_bound t2 in
      Tlet (specialize_term ~loc htv t1,
	    ident_of_vs ~loc v, specialize_term ~loc htv t2)
  | Term.Tcase (t1, bl) ->
      let branch b = let p, t = t_open_branch b in
	specialize_pattern ~loc htv p, specialize_term ~loc htv t
      in
      Tmatch (specialize_term ~loc htv t1, List.map branch bl)
  | Term.Teps fb ->
      let v, f = f_open_bound fb in
      Teps (ident_of_vs ~loc v, specialize_ty ~loc htv v.vs_ty,
	    specialize_fmla ~loc htv f)

(* TODO: labels are lost *)
and specialize_fmla ~loc htv f =
  let df = specialize_fmla_node ~loc htv f.f_node in
  List.fold_left (fun f l -> Fnamed (l, f)) df f.f_label

and specialize_fmla_node ~loc htv = function
  | Term.Fapp (ls, tl) ->
      Fapp (ls, List.map (specialize_term ~loc htv) tl)
  | Term.Fquant (q, fq) ->
      let vl, tl, f = f_open_quant fq in
      let uquant v = ident_of_vs ~loc v, specialize_ty ~loc htv v.vs_ty in
      let tl = List.map (List.map (specialize_trigger ~loc htv)) tl in
      Fquant (q, List.map uquant vl, tl, specialize_fmla ~loc htv f)
  | Term.Fbinop (b, f1, f2) ->
      Fbinop (b, specialize_fmla ~loc htv f1, specialize_fmla ~loc htv f2)
  | Term.Fnot f1 ->
      Fnot (specialize_fmla ~loc htv f1)
  | Term.Ftrue ->
      Ftrue
  | Term.Ffalse ->
      Ffalse
  | Term.Fif (f1, f2, f3) ->
      Fif (specialize_fmla ~loc htv f1,
	   specialize_fmla ~loc htv f2, specialize_fmla ~loc htv f3)
  | Term.Flet (t1, f2b) ->
      let v, f2 = f_open_bound f2b in
      Flet (specialize_term ~loc htv t1,
	    ident_of_vs ~loc v, specialize_fmla ~loc htv f2)
  | Term.Fcase (t, fbl) ->
      let branch b = let p, f = f_open_branch b in
	specialize_pattern ~loc htv p, specialize_fmla ~loc htv f
      in
      Fmatch (specialize_term ~loc htv t, List.map branch fbl)

and specialize_trigger ~loc htv = function
  | Term.Term t -> TRterm (specialize_term ~loc htv t)
  | Term.Fmla f -> TRfmla (specialize_fmla ~loc htv f)


