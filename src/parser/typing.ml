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

open Util
open Format
open Pp
open Ptree
open Ident
open Ty
open Term
open Decl
open Theory
open Env
open Denv

(** errors *)

type error =
  | Message of string
  | DuplicateTypeVar of string
  | TypeArity of qualid * int * int
  | Clash of string
  | PredicateExpected
  | TermExpected
  | BadNumberOfArguments of Ident.ident * int * int
  | ClashTheory of string
  | UnboundTheory of qualid
  | AlreadyTheory of string
  | UnboundFile of string
  | UnboundDir of string
  | AmbiguousPath of string * string
  | NotInLoadpath of string
  | CyclicTypeDef
  | UnboundTypeVar of string
  | UnboundType of string list
  | UnboundSymbol of string list

exception Error of error

let error ?loc e = match loc with
  | None -> raise (Error e)
  | Some loc -> raise (Loc.Located (loc, Error e))

let errorm ?loc f =
  let buf = Buffer.create 512 in
  let fmt = Format.formatter_of_buffer buf in
  Format.kfprintf
    (fun _ ->
       Format.pp_print_flush fmt ();
       let s = Buffer.contents buf in
       Buffer.clear buf;
       error ?loc (Message s))
    fmt f

let rec print_qualid fmt = function
  | Qident s -> fprintf fmt "%s" s.id
  | Qdot (m, s) -> fprintf fmt "%a.%s" print_qualid m s.id

let report fmt = function
  | Message s ->
      fprintf fmt "%s" s
  | DuplicateTypeVar s ->
      fprintf fmt "duplicate type parameter %s" s
  | TypeArity (id, a, n) ->
      fprintf fmt "@[The type %a expects %d argument(s),@ " print_qualid id a;
      fprintf fmt "but is applied to %d argument(s)@]" n
  | Clash id ->
      fprintf fmt "Clash with previous symbol %s" id
  | PredicateExpected ->
      fprintf fmt "syntax error: predicate expected"
  | TermExpected ->
      fprintf fmt "syntax error: term expected"
  | BadNumberOfArguments (s, n, m) ->
      fprintf fmt "@[Symbol `%s' is applied to %d terms,@ " s.id_short n;
      fprintf fmt "but is expecting %d arguments@]" m
  | ClashTheory s ->
      fprintf fmt "clash with previous theory %s" s
  | UnboundTheory q ->
      fprintf fmt "unbound theory %a" print_qualid q
  | AlreadyTheory s ->
      fprintf fmt "already using a theory with name %s" s
  | UnboundFile s ->
      fprintf fmt "no such file %s" s
  | UnboundDir s ->
      fprintf fmt "no such directory %s" s
  | AmbiguousPath (f1, f2) ->
      fprintf fmt "@[ambiguous path:@ both `%s'@ and `%s'@ match@]" f1 f2
  | NotInLoadpath f ->
      fprintf fmt "cannot find `%s' in loadpath" f
  | CyclicTypeDef ->
      fprintf fmt "cyclic type definition"
  | UnboundTypeVar s ->
      fprintf fmt "unbound type variable '%s" s
  | UnboundType sl ->
       fprintf fmt "Unbound type '%a'" (print_list dot pp_print_string) sl
  | UnboundSymbol sl ->
       fprintf fmt "Unbound symbol '%a'" (print_list dot pp_print_string) sl

(** Environments *)

(** typing using destructive type variables

    parsed trees        intermediate trees       typed trees
      (Ptree)               (D below)               (Term)
   -----------------------------------------------------------
     ppure_type  ---dty--->   dty       ---ty--->    ty
      lexpr      --dterm-->   dterm     --term-->    term
      lexpr      --dfmla-->   dfmla     --fmla-->    fmla

*)

let term_expected_type ~loc ty1 ty2 =
  errorm ~loc
    "@[This term has type %a@ but is expected to have type@ %a@]"
    print_dty ty1 print_dty ty2

(** Destructive typing environment, that is
    environment + local variables.
    It is only local to this module and created with [create_denv] below. *)

type denv = {
  uc : theory_uc; (* the theory under construction *)
  utyvars : (string, type_var) Hashtbl.t; (* user type variables *)
  dvars : dty Mstr.t; (* local variables, to be bound later *)
}

let create_denv uc = {
  uc = uc;
  utyvars = Hashtbl.create 17;
  dvars = Mstr.empty;
}

let find_user_type_var x env =
  try
    Hashtbl.find env.utyvars x
  with Not_found ->
    (* TODO: shouldn't we localize this ident? *)
    let v = create_tvsymbol (id_fresh x) in
    let v = create_ty_decl_var ~user:true v in
    Hashtbl.add env.utyvars x v;
    v

let mem_var x denv = Mstr.mem x denv.dvars
let find_var x denv = Mstr.find x denv.dvars
let add_var x ty denv = { denv with dvars = Mstr.add x ty denv.dvars }

(* parsed types -> intermediate types *)

let rec qloc = function
  | Qident x -> x.id_loc
  | Qdot (m, x) -> Loc.join (qloc m) x.id_loc

let rec string_list_of_qualid acc = function
  | Qident id -> id.id :: acc
  | Qdot (p, id) -> string_list_of_qualid (id.id :: acc) p

let specialize_tysymbol loc p uc =
  let sl = string_list_of_qualid [] p in
  let ts =
    try ns_find_ts (get_namespace uc) sl
    with Not_found -> error ~loc (UnboundType sl)
  in
  ts, specialize_tysymbol ~loc ts

let rec type_inst s ty = match ty.ty_node with
  | Ty.Tyvar n -> Mtv.find n s
  | Ty.Tyapp (ts, tyl) -> Tyapp (ts, List.map (type_inst s) tyl)

let rec dty env = function
  | PPTtyvar {id=x} ->
      Tyvar (find_user_type_var x env)
  | PPTtyapp (p, x) ->
      let loc = qloc x in
      let ts, tv = specialize_tysymbol loc x env.uc in
      let np = List.length p in
      let a = List.length tv in
      if np <> a then error ~loc (TypeArity (x, a, np));
      let tyl = List.map (dty env) p in
      match ts.ts_def with
	| None ->
	    Tyapp (ts, tyl)
	| Some ty ->
	    let add m v t = Mtv.add v t m in
            let s = List.fold_left2 add Mtv.empty ts.ts_args tyl in
	    type_inst s ty

let find_ns find p ns =
  let loc = qloc p in
  let sl = string_list_of_qualid [] p in
  try find ns sl
  with Not_found -> error ~loc (UnboundSymbol sl)

let find_prop_ns = find_ns ns_find_prop
let find_prop p uc = find_prop_ns p (get_namespace uc)

let find_tysymbol_ns = find_ns ns_find_ts
let find_tysymbol q uc = find_tysymbol_ns q (get_namespace uc)

let find_lsymbol_ns = find_ns ns_find_ls
let find_lsymbol q uc = find_lsymbol_ns q (get_namespace uc)

let specialize_lsymbol p uc =
  let s = find_lsymbol p uc in
  s, specialize_lsymbol (qloc p) s

let specialize_fsymbol p uc =
  let s, (tl, ty) = specialize_lsymbol p uc in
  match ty with
    | None -> let loc = qloc p in error ~loc TermExpected
    | Some ty -> s, tl, ty

let specialize_psymbol p uc =
  let s, (tl, ty) = specialize_lsymbol p uc in
  match ty with
    | None -> s, tl
    | Some _ -> let loc = qloc p in error ~loc PredicateExpected

let is_psymbol p uc = 
  let s = find_lsymbol p uc in
  s.ls_value = None


(** Typing types *)

let split_qualid = function
  | Qident id -> [], id.id
  | Qdot (p, id) -> string_list_of_qualid [] p, id.id

(** Typing terms and formulas *)

type dpattern = { dp_node : dpattern_node; dp_ty : dty }

and dpattern_node =
  | Pwild
  | Pvar of string
  | Papp of lsymbol * dpattern list
  | Pas of dpattern * string

type uquant = string list * dty

type dterm = { dt_node : dterm_node; dt_ty : dty }

and dterm_node =
  | Tvar of string
  | Tconst of constant
  | Tapp of lsymbol * dterm list
  | Tif of dfmla * dterm * dterm
  | Tlet of dterm * string * dterm
  | Tmatch of dterm list * (dpattern list * dterm) list
  | Tnamed of string * dterm
  | Teps of string * dty * dfmla

and dfmla =
  | Fapp of lsymbol * dterm list
  | Fquant of quant * uquant list * dtrigger list list * dfmla
  | Fbinop of binop * dfmla * dfmla
  | Fnot of dfmla
  | Ftrue
  | Ffalse
  | Fif of dfmla * dfmla * dfmla
  | Flet of dterm * string * dfmla
  | Fmatch of dterm list * (dpattern list * dfmla) list
  | Fnamed of string * dfmla
  | Fvar of fmla

and dtrigger =
  | TRterm of dterm
  | TRfmla of dfmla

let binop = function
  | PPand -> Fand
  | PPor -> For
  | PPimplies -> Fimplies
  | PPiff -> Fiff

let check_pat_linearity pl =
  let s = ref Sstr.empty in
  let add id =
    if Sstr.mem id.id !s then
      errorm ~loc:id.id_loc "duplicate variable %s" id.id;
    s := Sstr.add id.id !s
  in
  let rec check p = match p.pat_desc with
    | PPpwild -> ()
    | PPpvar id -> add id
    | PPpapp (_, pl) -> List.iter check pl
    | PPpas (p, id) -> check p; add id
  in
  List.iter check pl

let rec dpat env pat =
  let env, n, ty = dpat_node pat.pat_loc env pat.pat_desc in
  env, { dp_node = n; dp_ty = ty }

and dpat_node loc env = function
  | PPpwild ->
      let tv = create_tvsymbol (id_user "a" loc) in
      let ty = Tyvar (create_ty_decl_var ~loc ~user:false tv) in
      env, Pwild, ty
  | PPpvar {id=x} ->
      let tv = create_tvsymbol (id_user "a" loc) in
      let ty = Tyvar (create_ty_decl_var ~loc ~user:false tv) in
      let env = { env with dvars = Mstr.add x ty env.dvars } in
      env, Pvar x, ty
  | PPpapp (x, pl) ->
      let s, tyl, ty = specialize_fsymbol x env.uc in
      let env, pl = dpat_args s.ls_name loc env tyl pl in
      env, Papp (s, pl), ty
  | PPpas (p, {id=x}) ->
      let env, p = dpat env p in
      let env = { env with dvars = Mstr.add x p.dp_ty env.dvars } in
      env, Pas (p,x), p.dp_ty

and dpat_args s loc env el pl =
  let n = List.length el and m = List.length pl in
  if n <> m then error ~loc (BadNumberOfArguments (s, m, n));
  let rec check_arg env = function
    | [], [] ->
	env, []
    | a :: al, p :: pl ->
	let loc = p.pat_loc in
	let env, p = dpat env p in
	if not (unify a p.dp_ty) then term_expected_type ~loc p.dp_ty a;
	let env, pl = check_arg env (al, pl) in
	env, p :: pl
    | _ ->
	assert false
  in
  check_arg env (el, pl)

let rec trigger_not_a_term_exn = function
  | Error TermExpected -> true
  | Loc.Located (_, exn) -> trigger_not_a_term_exn exn
  | _ -> false

let check_quant_linearity uqu =
  let s = ref Sstr.empty in
  let check id =
    if Sstr.mem id.id !s then errorm ~loc:id.id_loc "duplicate variable %s" id.id;
    s := Sstr.add id.id !s
  in
  List.iter (fun (idl, _) -> List.iter check idl) uqu

let rec dterm env t =
  let n, ty = dterm_node t.pp_loc env t.pp_desc in
  { dt_node = n; dt_ty = ty }

and dterm_node loc env = function
  | PPvar (Qident {id=x}) when Mstr.mem x env.dvars ->
      (* local variable *)
      let ty = Mstr.find x env.dvars in
      Tvar x, ty
  | PPvar x ->
      (* 0-arity symbol (constant) *)
      let s, tyl, ty = specialize_fsymbol x env.uc in
      let n = List.length tyl in
      if n > 0 then error ~loc (BadNumberOfArguments (s.ls_name, 0, n));
      Tapp (s, []), ty
  | PPapp (x, tl) ->
      let s, tyl, ty = specialize_fsymbol x env.uc in
      let tl = dtype_args s.ls_name loc env tyl tl in
      Tapp (s, tl), ty
  | PPinfix (e1, x, e2) ->
      let s, tyl, ty = specialize_fsymbol (Qident x) env.uc in
      let tl = dtype_args s.ls_name loc env tyl [e1; e2] in
      Tapp (s, tl), ty
  | PPconst (ConstInt _ as c) ->
      Tconst c, Tyapp (Ty.ts_int, [])
  | PPconst (ConstReal _ as c) ->
      Tconst c, Tyapp (Ty.ts_real, [])
  | PPlet ({id=x}, e1, e2) ->
      let e1 = dterm env e1 in
      let ty = e1.dt_ty in
      let env = { env with dvars = Mstr.add x ty env.dvars } in
      let e2 = dterm env e2 in
      Tlet (e1, x, e2), e2.dt_ty
  | PPmatch (el, bl) ->
      let tl = List.map (dterm env) el in
      let tb = (* the type of all branches *)
	let tv = create_tvsymbol (id_user "a" loc) in
	Tyvar (create_ty_decl_var ~loc ~user:false tv)
      in
      let branch (pl, e) =
        let env, pl = dpat_list env tl pl in
        let loc = e.pp_loc in
	let e = dterm env e in
	if not (unify e.dt_ty tb) then term_expected_type ~loc e.dt_ty tb;
        pl, e
      in
      let bl = List.map branch bl in
      let ty = (snd (List.hd bl)).dt_ty in
      Tmatch (tl, bl), ty
  | PPnamed (x, e1) ->
      let e1 = dterm env e1 in
      Tnamed (x, e1), e1.dt_ty
  | PPcast (e1, ty) ->
      let loc = e1.pp_loc in
      let e1 = dterm env e1 in
      let ty = dty env ty in
      if not (unify e1.dt_ty ty) then term_expected_type ~loc e1.dt_ty ty;
      e1.dt_node, ty
  | PPif (e1, e2, e3) ->
      let loc = e3.pp_loc in
      let e2 = dterm env e2 in
      let e3 = dterm env e3 in
      if not (unify e2.dt_ty e3.dt_ty) then
        term_expected_type ~loc e3.dt_ty e2.dt_ty;
      Tif (dfmla env e1, e2, e3), e2.dt_ty
  | PPeps ({id=x}, ty, e1) ->
      let ty = dty env ty in
      let env = { env with dvars = Mstr.add x ty env.dvars } in
      let e1 = dfmla env e1 in
      Teps (x, ty, e1), ty
  | PPquant _
  | PPbinop _ | PPunop _ | PPfalse | PPtrue ->
      error ~loc TermExpected

and dfmla env e = match e.pp_desc with
  | PPtrue ->
      Ftrue
  | PPfalse ->
      Ffalse
  | PPunop (PPnot, a) ->
      Fnot (dfmla env a)
  | PPbinop (a, (PPand | PPor | PPimplies | PPiff as op), b) ->
      Fbinop (binop op, dfmla env a, dfmla env b)
  | PPif (a, b, c) ->
      Fif (dfmla env a, dfmla env b, dfmla env c)
  | PPquant (q, uqu, trl, a) ->
      check_quant_linearity uqu;
      let uquant env (idl,ty) =
        let ty = dty env ty in
        let env, idl =
          map_fold_left
            (fun env {id=x} -> { env with dvars = Mstr.add x ty env.dvars }, x)
            env idl
        in
        env, (idl,ty)
      in
      let env, uqu = map_fold_left uquant env uqu in
      let trigger e =
	try
	  TRterm (dterm env e)
	with exn when trigger_not_a_term_exn exn ->
	  TRfmla (dfmla env e)
      in
      let trl = List.map (List.map trigger) trl in
      let q = match q with
        | PPforall -> Fforall
        | PPexists -> Fexists
      in
      Fquant (q, uqu, trl, dfmla env a)
  | PPapp (x, tl) ->
      let s, tyl = specialize_psymbol x env.uc in
      let tl = dtype_args s.ls_name e.pp_loc env tyl tl in
      Fapp (s, tl)
  | PPinfix (e12, op2, e3) ->
      begin match e12.pp_desc with
	| PPinfix (_, op1, e2) when is_psymbol (Qident op1) env.uc ->
	    let e23 = { e with pp_desc = PPinfix (e2, op2, e3) } in
	    Fbinop (Fand, dfmla env e12, dfmla env e23)
	| _ ->
	    let s, tyl = specialize_psymbol (Qident op2) env.uc in
	    let tl = dtype_args s.ls_name e.pp_loc env tyl [e12; e3] in
	    Fapp (s, tl)
      end
  | PPlet ({id=x}, e1, e2) ->
      let e1 = dterm env e1 in
      let ty = e1.dt_ty in
      let env = { env with dvars = Mstr.add x ty env.dvars } in
      let e2 = dfmla env e2 in
      Flet (e1, x, e2)
  | PPmatch (el, bl) ->
      let tl = List.map (dterm env) el in
      let branch (pl, e) =
        let env, pl = dpat_list env tl pl in
        pl, dfmla env e
      in
      Fmatch (tl, List.map branch bl)
  | PPnamed (x, f1) ->
      let f1 = dfmla env f1 in
      Fnamed (x, f1)
  | PPvar x ->
      Fvar (snd (find_prop x env.uc))
  | PPeps _ | PPconst _ | PPcast _ ->
      error ~loc:e.pp_loc PredicateExpected

and dpat_list env tl pl =
  check_pat_linearity pl;
  let pattern (env,pl) pat t =
    let loc = pat.pat_loc in
    let env, pat = dpat env pat in
    if not (unify pat.dp_ty t.dt_ty)
      then term_expected_type ~loc pat.dp_ty t.dt_ty;
    env, pat::pl
  in
  let loc = (List.hd pl).pat_loc in
  let env, pl = try List.fold_left2 pattern (env,[]) pl tl
    with Invalid_argument _ -> errorm ~loc
      "This pattern has length %d but is expected to have length %d"
      (List.length pl) (List.length tl)
  in
  env, List.rev pl

and dtype_args s loc env el tl =
  let n = List.length el and m = List.length tl in
  if n <> m then error ~loc (BadNumberOfArguments (s, m, n));
  let rec check_arg = function
    | [], [] ->
	[]
    | a :: al, t :: bl ->
	let loc = t.pp_loc in
	let t = dterm env t in
	if not (unify a t.dt_ty) then term_expected_type ~loc t.dt_ty a;
	t :: check_arg (al, bl)
    | _ ->
	assert false
  in
  check_arg (el, tl)

let rec pattern env p =
  let ty = ty_of_dty p.dp_ty in
  match p.dp_node with
  | Pwild -> env, pat_wild ty
  | Pvar x ->
      let v = create_vsymbol (id_fresh x) ty in
      Mstr.add x v env, pat_var v
  | Papp (s, pl) ->
      let env, pl = map_fold_left pattern env pl in
      env, pat_app s pl ty
  | Pas (p, x) ->
      let v = create_vsymbol (id_fresh x) ty in
      let env, p = pattern (Mstr.add x v env) p in
      env, pat_as p v

let rec term env t = match t.dt_node with
  | Tvar x ->
      assert (Mstr.mem x env);
      t_var (Mstr.find x env)
  | Tconst c ->
      t_const c (ty_of_dty t.dt_ty)
  | Tapp (s, tl) ->
      t_app s (List.map (term env) tl) (ty_of_dty t.dt_ty)
  | Tif (f, t1, t2) ->
      t_if (fmla env f) (term env t1) (term env t2)
  | Tlet (e1, x, e2) ->
      let ty = ty_of_dty e1.dt_ty in
      let e1 = term env e1 in
      let v = create_vsymbol (id_fresh x) ty in
      let env = Mstr.add x v env in
      let e2 = term env e2 in
      t_let v e1 e2
  | Tmatch (tl, bl) ->
      let branch (pl,e) =
        let env, pl = map_fold_left pattern env pl in
        (pl, term env e)
      in
      let bl = List.map branch bl in
      let ty = (snd (List.hd bl)).t_ty in
      t_case (List.map (term env) tl) bl ty
  | Tnamed (x, e1) ->
      let e1 = term env e1 in
      t_label_add x e1
  | Teps (x, ty, e1) ->
      let ty = ty_of_dty ty in
      let v = create_vsymbol (id_fresh x) ty in
      let env = Mstr.add x v env in
      let e1 = fmla env e1 in
      t_eps v e1

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
      (* TODO: shouldn't we localize this ident? *)
      let uquant env (xl,ty) =
        let ty = ty_of_dty ty in
        map_fold_left
          (fun env x ->
             let v = create_vsymbol (id_fresh x) ty in Mstr.add x v env, v)
          env xl
      in
      let env, vl = map_fold_left uquant env uqu in
      let trigger = function
	| TRterm t -> Term (term env t)
	| TRfmla f -> Fmla (fmla env f)
      in
      let trl = List.map (List.map trigger) trl in
      f_quant q (List.concat vl) trl (fmla env f1)
  | Fapp (s, tl) ->
      f_app s (List.map (term env) tl)
  | Flet (e1, x, f2) ->
      let ty = ty_of_dty e1.dt_ty in
      let e1 = term env e1 in
      let v = create_vsymbol (id_fresh x) ty in
      let env = Mstr.add x v env in
      let f2 = fmla env f2 in
      f_let v e1 f2
  | Fmatch (tl, bl) ->
      let branch (pl,e) =
        let env, pl = map_fold_left pattern env pl in
        (pl, fmla env e)
      in
      f_case (List.map (term env) tl) (List.map branch bl)
  | Fnamed (x, f1) ->
      let f1 = fmla env f1 in
      f_label_add x f1
  | Fvar f ->
      f

(** Typing declarations, that is building environments. *)

open Ptree

let add_types dl th =
  let def = List.fold_left 
    (fun def d ->
      let id = d.td_ident.id in 
      if Mstr.mem id def then error ~loc:d.td_loc (Clash id);
      Mstr.add id d def) 
    Mstr.empty dl 
  in
  let tysymbols = Hashtbl.create 17 in
  let rec visit x =
    try
      match Hashtbl.find tysymbols x with
	| None -> error CyclicTypeDef
	| Some ts -> ts
    with Not_found ->
      Hashtbl.add tysymbols x None;
      let d = Mstr.find x def in
      let id = d.td_ident.id in
      let vars = Hashtbl.create 17 in
      let vl =
	List.map
	  (fun v ->
	     if Hashtbl.mem vars v.id then
	       error ~loc:v.id_loc (DuplicateTypeVar v.id);
	     let i = create_tvsymbol (id_user v.id v.id_loc) in
	     Hashtbl.add vars v.id i;
	     i)
	  d.td_params
      in
      let id = id_user id d.td_loc in
      let ts = match d.td_def with
	| TDalias ty ->
	    let rec apply = function
	      | PPTtyvar v ->
		  begin
		    try ty_var (Hashtbl.find vars v.id)
		    with Not_found -> error ~loc:v.id_loc (UnboundTypeVar v.id)
		  end
	      | PPTtyapp (tyl, q) ->
		  let ts = match q with
		    | Qident x when Mstr.mem x.id def ->
			visit x.id
		    | Qident _ | Qdot _ ->
			find_tysymbol q th
		  in
		  try
		    ty_app ts (List.map apply tyl)
		  with Ty.BadTypeArity (tsal, tyll) ->
		    error ~loc:(qloc q) (TypeArity (q, tsal, tyll))
	    in
	    create_tysymbol id vl (Some (apply ty))
	| TDabstract | TDalgebraic _ ->
	    create_tysymbol id vl None
      in
      Hashtbl.add tysymbols x (Some ts);
      ts
  in
  let tsl = List.rev_map (fun d -> visit d.td_ident.id, Tabstract) dl in 
  let th' = try add_ty_decl th tsl
    with ClashSymbol s -> error ~loc:(Mstr.find s def).td_loc (Clash s)
  in
  let csymbols = Hashtbl.create 17 in
  let decl d =
    let ts, th' = match Hashtbl.find tysymbols d.td_ident.id with
      | None ->
	  assert false
      | Some ts ->
	  let th' = create_denv th' in
	  let vars = th'.utyvars in
	  List.iter
	    (fun v ->
	       Hashtbl.add vars v.tv_name.id_short
                  (create_ty_decl_var ~user:true v))
	    ts.ts_args;
	  ts, th'
    in
    let d = match d.td_def with
      | TDabstract | TDalias _ ->
	  Tabstract
      | TDalgebraic cl ->
	  let ty = ty_app ts (List.map ty_var ts.ts_args) in
	  let constructor (loc, id, pl) =
	    let param t = ty_of_dty (dty th' t) in
	    let tyl = List.map param pl in
	    Hashtbl.replace csymbols id.id loc;
	    create_fsymbol (id_user id.id loc) tyl ty
	  in
	  Talgebraic (List.map constructor cl)
    in
    ts, d
  in
  try add_ty_decls th (List.map decl dl)
  with ClashSymbol s -> error ~loc:(Hashtbl.find csymbols s) (Clash s)

let env_of_vsymbol_list vl =
  List.fold_left (fun env v -> Mstr.add v.vs_name.id_short v env) Mstr.empty vl

let add_logics dl th =
  let fsymbols = Hashtbl.create 17 in
  let psymbols = Hashtbl.create 17 in
  let denvs = Hashtbl.create 17 in
  (* 1. create all symbols and make an environment with these symbols *)
  let create_symbol th d =
    let id = d.ld_ident.id in
    let v = id_user id d.ld_loc in
    let denv = create_denv th in
    Hashtbl.add denvs id denv;
    let type_ty (_,t) = ty_of_dty (dty denv t) in
    let pl = List.map type_ty d.ld_params in
    try match d.ld_type with
      | None -> (* predicate *)
	  let ps = create_psymbol v pl in
	  Hashtbl.add psymbols id ps;
	  add_logic_decl th [ps, None]
      | Some t -> (* function *)
	  let t = type_ty (None, t) in
	  let fs = create_fsymbol v pl t in
	  Hashtbl.add fsymbols id fs;
	  add_logic_decl th [fs, None]
    with ClashSymbol s -> error ~loc:d.ld_loc (Clash s)
  in
  let th' = List.fold_left create_symbol th dl in
  (* 2. then type-check all definitions *)
  let type_decl d =
    let id = d.ld_ident.id in
    let dadd_var denv (x, ty) = match x with
      | None -> denv
      | Some id -> { denv with dvars = Mstr.add id.id (dty denv ty) denv.dvars }
    in
    let denv = Hashtbl.find denvs id in
    let denv = { denv with uc = th' } in
    let denv = List.fold_left dadd_var denv d.ld_params in
    let create_var (x, _) ty =
      let id = match x with
	| None -> id_fresh "%x"
	| Some id -> id_user id.id id.id_loc
      in
      create_vsymbol id ty
    in
    let mk_vlist = List.map2 create_var d.ld_params in
    match d.ld_type with
    | None -> (* predicate *)
	let ps = Hashtbl.find psymbols id in
        begin match d.ld_def with
	  | None -> ps,None
	  | Some f ->
	      let f = dfmla denv f in
              let vl = match ps.ls_value with
                | None -> mk_vlist ps.ls_args
                | _ -> assert false
              in
	      let env = env_of_vsymbol_list vl in
              make_ps_defn ps vl (fmla env f)
        end
    | Some ty -> (* function *)
	let fs = Hashtbl.find fsymbols id in
        begin match d.ld_def with
	  | None -> fs,None
	  | Some t ->
	      let loc = t.pp_loc in
	      let ty = dty denv ty in
	      let t = dterm denv t in
	      if not (unify t.dt_ty ty) then 
		term_expected_type ~loc t.dt_ty ty;
              let vl = match fs.ls_value with
                | Some _ -> mk_vlist fs.ls_args
                | _ -> assert false
              in
	      let env = env_of_vsymbol_list vl in
	      make_fs_defn fs vl (term env t)
        end
  in
  add_logic_decls th (List.map type_decl dl)

let type_term denv env t =
  let t = dterm denv t in
  term env t

let term uc = type_term (create_denv uc) Mstr.empty

let type_fmla denv env f =
  let f = dfmla denv f in
  fmla env f

let fmla uc = type_fmla (create_denv uc) Mstr.empty

let add_prop k loc s f th =
  let pr = create_prsymbol (id_user s.id loc) in
  try add_prop_decl th k pr (fmla th f)
  with ClashSymbol s -> error ~loc (Clash s)

let loc_of_id id = match id.id_origin with
  | User loc -> loc
  | _ -> assert false

let add_inductives dl th =
  (* 1. create all symbols and make an environment with these symbols *)
  let psymbols = Hashtbl.create 17 in
  let create_symbol th d =
    let id = d.in_ident.id in
    let v = id_user id d.in_loc in
    let denv = create_denv th in
    let type_ty t = ty_of_dty (dty denv t) in
    let pl = List.map type_ty d.in_params in
    let ps = create_psymbol v pl in
    Hashtbl.add psymbols id ps;
    try add_logic_decl th [ps, None]
    with ClashSymbol s -> error ~loc:d.in_loc (Clash s)
  in
  let th' = List.fold_left create_symbol th dl in
  (* 2. then type-check all definitions *)
  let propsyms = Hashtbl.create 17 in
  let type_decl d =
    let id = d.in_ident.id in
    let ps = Hashtbl.find psymbols id in
    let clause (loc, id, f) =
      Hashtbl.replace propsyms id.id loc;
      create_prsymbol (id_user id.id loc), fmla th' f
    in
    ps, List.map clause d.in_def
  in
  try add_ind_decls th (List.map type_decl dl)
  with
  | ClashSymbol s -> error ~loc:(Hashtbl.find propsyms s) (Clash s)
  | InvalidIndDecl (_,pr) -> errorm ~loc:(loc_of_id pr.pr_name)
      "not a clausal form"
  | NonPositiveIndDecl (_,pr,s) -> errorm ~loc:(loc_of_id pr.pr_name)
      "non-positive occurrence of %a" Pretty.print_ls s
  | TooSpecificIndDecl (_,pr,t) -> errorm ~loc:(loc_of_id pr.pr_name)
      "term @[%a@] is too specific" Pretty.print_term t

(* parse file and store all theories into parsed_theories *)

let load_channel file c =
  let lb = Lexing.from_channel c in
  Loc.set_file file lb;
  Lexer.parse_logic_file lb

let load_file file =
  let c = open_in file in
  let tl = load_channel file c in
  close_in c;
  tl

let prop_kind = function
  | Kaxiom -> Paxiom
  | Kgoal -> Pgoal
  | Klemma -> Plemma

let find_theory env lenv q id = match q with
  | [] ->
      (* local theory *)
      begin try Mnm.find id lenv
      with Not_found -> find_theory env [] id end
  | _ :: _ ->
      (* theory in file f *)
      find_theory env q id

let rec type_theory env lenv id pt =
  let n = id_user id.id id.id_loc in
  let th = create_theory n in
  let th = add_decls env lenv th pt.pt_decl in
  close_theory th

and add_decls env lenv th = List.fold_left (add_decl env lenv) th

and add_decl env lenv th = function
  | TypeDecl dl ->
      add_types dl th
  | LogicDecl dl ->
      add_logics dl th
  | IndDecl dl ->
      add_inductives dl th
  | PropDecl (loc, k, s, f) ->
      add_prop (prop_kind k) loc s f th
  | UseClone (loc, use, subst) ->
      let q, id = split_qualid use.use_theory in
      let t =
	try
	  find_theory env lenv q id
	with
	  | TheoryNotFound _ -> error ~loc (UnboundTheory use.use_theory)
	  | Error (AmbiguousPath _ as e) -> error ~loc e
      in
      let use_or_clone th = match subst with
	| None ->
	    use_export th t
	| Some s ->
            let add_inst s = function
              | CStsym (p,q) ->
                  let ts1 = find_tysymbol_ns p t.th_export in
                  let ts2 = find_tysymbol q th in
                  if Mts.mem ts1 s.inst_ts
                  then error ~loc (Clash ts1.ts_name.id_short);
                  { s with inst_ts = Mts.add ts1 ts2 s.inst_ts }
              | CSlsym (p,q) ->
                  let ls1 = find_lsymbol_ns p t.th_export in
                  let ls2 = find_lsymbol q th in
                  if Mls.mem ls1 s.inst_ls
                  then error ~loc (Clash ls1.ls_name.id_short);
                  { s with inst_ls = Mls.add ls1 ls2 s.inst_ls }
              | CSlemma p ->
                  let pr,_ = find_prop_ns p t.th_export in
                  if Spr.mem pr s.inst_lemma || Spr.mem pr s.inst_goal
                  then error ~loc (Clash pr.pr_name.id_short);
                  { s with inst_lemma = Spr.add pr s.inst_lemma }
              | CSgoal p ->
                  let pr,_ = find_prop_ns p t.th_export in
                  if Spr.mem pr s.inst_lemma || Spr.mem pr s.inst_goal
                  then error ~loc (Clash pr.pr_name.id_short);
                  { s with inst_goal = Spr.add pr s.inst_goal }
	    in
            let s = List.fold_left add_inst empty_inst s in
	    clone_export th t s
      in
      let n = match use.use_as with
	| None -> Some t.th_name.id_short
	| Some (Some x) -> Some x.id
	| Some None -> None
      in
      begin try match use.use_imp_exp with
	| Nothing ->
	    (* use T = namespace T use_export T end *)
	    let th = open_namespace th in
	    let th = use_or_clone th in
	    close_namespace th false n
	| Import ->
	    (* use import T = namespace T use_export T end import T *)
	    let th = open_namespace th in
	    let th = use_or_clone th in
	    close_namespace th true n
	| Export ->
	    use_or_clone th
      with ClashSymbol s -> error ~loc (Clash s)
      end
  | Namespace (loc, import, name, dl) ->
      let th = open_namespace th in
      let th = add_decls env lenv th dl in
      let id = option_map (fun id -> id.id) name in
      try close_namespace th import id
      with ClashSymbol s -> error ~loc (Clash s)

and type_and_add_theory env lenv pt =
  let id = pt.pt_name in
  if Mnm.mem id.id lenv || id.id = builtin_theory.th_name.id_short
    then error (ClashTheory id.id);
  let th = type_theory env lenv id pt in
  Mnm.add id.id th lenv

let type_theories env tl =
  List.fold_left (type_and_add_theory env) Mnm.empty tl

let read_file env file =
  let tl = load_file file in
  type_theories env tl

let read_channel env file ic =
  let tl = load_channel file ic in
  type_theories env tl

let locate_file lp sl =
  let f = List.fold_left Filename.concat "" sl ^ ".why" in
  let fl = List.map (fun dir -> Filename.concat  dir f) lp in
  match List.filter Sys.file_exists fl with
    | [] -> raise Not_found
    | [file] -> file
    | file1 :: file2 :: _ -> error (AmbiguousPath (file1, file2))

let retrieve lp env sl =
  let file = locate_file lp sl in
  read_file env file

(*
Local Variables:
compile-command: "make -C ../.. test"
End:
*)
