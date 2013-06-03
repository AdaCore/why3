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

open Stdlib
open Format
open Ident
open Ptree
open Ty
open Term
open Decl
open Theory
open Env
open Denv

(** errors *)

exception DuplicateVar of string
exception DuplicateTypeVar of string
exception PredicateExpected
exception TermExpected
exception FSymExpected of lsymbol
exception PSymExpected of lsymbol
exception ClashTheory of string
(* dead code
exception UnboundTheory of qualid
*)
exception UnboundTypeVar of string
(* dead code
exception UnboundType of string list
*)
exception UnboundSymbol of qualid

let error = Loc.error

let errorm = Loc.errorm

let rec print_qualid fmt = function
  | Qident s -> fprintf fmt "%s" s.id
  | Qdot (m, s) -> fprintf fmt "%a.%s" print_qualid m s.id

let () = Exn_printer.register (fun fmt e -> match e with
  | DuplicateTypeVar s ->
      fprintf fmt "Duplicate type parameter %s" s
  | DuplicateVar s ->
      fprintf fmt "Duplicate variable %s" s
  | PredicateExpected ->
      fprintf fmt "syntax error: predicate expected"
  | TermExpected ->
      fprintf fmt "syntax error: term expected"
  | FSymExpected ls ->
      fprintf fmt "%a is not a function symbol" Pretty.print_ls ls
  | PSymExpected ls ->
      fprintf fmt "%a is not a predicate symbol" Pretty.print_ls ls
  | ClashTheory s ->
      fprintf fmt "Clash with previous theory %s" s
(* dead code
  | UnboundTheory q ->
      fprintf fmt "unbound theory %a" print_qualid q
*)
  | UnboundTypeVar s ->
      fprintf fmt "unbound type variable '%s" s
(* dead code
  | UnboundType sl ->
       fprintf fmt "Unbound type '%a'" (print_list dot pp_print_string) sl
*)
  | UnboundSymbol q ->
       fprintf fmt "Unbound symbol '%a'" print_qualid q
  | _ -> raise e)

let debug_parse_only = Debug.register_flag "parse_only"
  ~desc:"Stop@ after@ parsing."
let debug_type_only  = Debug.register_flag "type_only"
  ~desc:"Stop@ after@ type-checking."

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
    "This term has type %a@ but is expected to have type@ %a"
    print_dty ty1 print_dty ty2

let unify_raise ~loc ty1 ty2 =
  if not (unify ty1 ty2) then term_expected_type ~loc ty1 ty2

(** Destructive typing environment, that is
    environment + local variables.
    It is only local to this module and created with [create_denv] below. *)

let create_user_tv =
  let hs = Hstr.create 17 in
  fun s -> try Hstr.find hs s with Not_found ->
  let tv = create_tvsymbol (id_fresh s) in
  Hstr.add hs s tv;
  tv

(* TODO: shouldn't we localize this ident? *)
let create_user_type_var x =
  tyuvar (create_user_tv x)

type denv = {
  dvars : dty Mstr.t;    (* local variables, to be bound later *)
  gvars : qualid -> vsymbol option; (* global variables, for programs *)
}

let denv_empty = { dvars = Mstr.empty; gvars = Util.const None }
let denv_empty_with_globals gv = { dvars = Mstr.empty; gvars = gv }

(* dead code
let mem_var x denv = Mstr.mem x denv.dvars
let find_var x denv = Mstr.find x denv.dvars
*)
let add_var x ty denv = { denv with dvars = Mstr.add x ty denv.dvars }

(* dead code
let print_denv fmt denv =
  Mstr.iter (fun x ty -> fprintf fmt "%s:%a,@ " x print_dty ty) denv.dvars
*)

(* parsed types -> intermediate types *)

let rec qloc = function
  | Qident x -> x.id_loc
  | Qdot (m, x) -> Loc.join (qloc m) x.id_loc

let rec string_list_of_qualid acc = function
  | Qident id -> id.id :: acc
  | Qdot (p, id) -> string_list_of_qualid (id.id :: acc) p

(* lazy declaration of tuples *)

let add_ty_decl uc ts = add_decl_with_tuples uc (create_ty_decl ts)
let add_data_decl uc dl = add_decl_with_tuples uc (create_data_decl dl)
let add_param_decl uc ls = add_decl_with_tuples uc (create_param_decl ls)
let add_logic_decl uc dl = add_decl_with_tuples uc (create_logic_decl dl)
let add_ind_decl uc s dl = add_decl_with_tuples uc (create_ind_decl s dl)
let add_prop_decl uc k p f = add_decl_with_tuples uc (create_prop_decl k p f)

let find_ns get_id find p ns =
  let loc = qloc p in
  let sl = string_list_of_qualid [] p in
  try
    let r = find ns sl in
    if Debug.test_flag Glob.flag then Glob.use loc (get_id r);
    r
  with Not_found -> error ~loc (UnboundSymbol p)

let get_id_prop p = p.pr_name
let find_prop_ns = find_ns get_id_prop ns_find_pr
let find_prop p uc = find_prop_ns p (get_namespace uc)

let get_id_ts ts = ts.ts_name
let find_tysymbol_ns = find_ns get_id_ts ns_find_ts
let find_tysymbol q uc = find_tysymbol_ns q (get_namespace uc)

let get_id_ls ls = ls.ls_name
let find_lsymbol_ns = find_ns get_id_ls ns_find_ls
let find_lsymbol q uc = find_lsymbol_ns q (get_namespace uc)

let find_fsymbol_ns q ns =
  let ls = find_lsymbol_ns q ns in
  if ls.ls_value = None then error ~loc:(qloc q) (FSymExpected ls) else ls

let find_psymbol_ns q ns =
  let ls = find_lsymbol_ns q ns in
  if ls.ls_value <> None then error ~loc:(qloc q) (PSymExpected ls) else ls

let find_fsymbol q uc = find_fsymbol_ns q (get_namespace uc)
let find_psymbol q uc = find_psymbol_ns q (get_namespace uc)

let get_dummy_id _ = Glob.dummy_id
let find_namespace_ns = find_ns get_dummy_id ns_find_ns
(* dead code
let find_namespace q uc = find_namespace_ns q (get_namespace uc)
*)

let rec dty uc = function
  | PPTtyvar ({id=x}, _) ->
      create_user_type_var x
  | PPTtyapp (x, p) ->
      let ts = find_tysymbol x uc in
      let tyl = List.map (dty uc) p in
      Loc.try2 (qloc x) tyapp ts tyl
  | PPTtuple tyl ->
      let ts = ts_tuple (List.length tyl) in
      tyapp ts (List.map (dty uc) tyl)

let rec ty_of_pty uc = function
  | PPTtyvar ({id=x}, _) ->
      ty_var (create_user_tv x)
  | PPTtyapp (x, p) ->
      let ts = find_tysymbol x uc in
      let tyl = List.map (ty_of_pty uc) p in
      Loc.try2 (qloc x) ty_app ts tyl
  | PPTtuple tyl ->
      let ts = ts_tuple (List.length tyl) in
      ty_app ts (List.map (ty_of_pty uc) tyl)

let rec opaque_tvs acc = function
  | Ptree.PPTtyvar (id, true) -> Stv.add (create_user_tv id.id) acc
  | Ptree.PPTtyvar (_, false) -> acc
  | Ptree.PPTtyapp (_, pl)
  | Ptree.PPTtuple pl -> List.fold_left opaque_tvs acc pl

let opaque_tvs args value =
  let acc = Opt.fold opaque_tvs Stv.empty value in
  List.fold_left (fun acc (_,_,_,ty) -> opaque_tvs acc ty) acc args

let specialize_lsymbol p uc =
  let s = find_lsymbol p uc in
  let tl,ty = specialize_lsymbol ~loc:(qloc p) s in
  s,tl,ty

let specialize_fsymbol p uc =
  let s,tl,ty = specialize_lsymbol p uc in
  match ty with
    | None -> let loc = qloc p in error ~loc TermExpected
    | Some ty -> s, tl, ty

let specialize_psymbol p uc =
  let s,tl,ty = specialize_lsymbol p uc in
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

let binop = function
  | PPand -> Tand
  | PPor -> Tor
  | PPimplies -> Timplies
  | PPiff -> Tiff

let check_pat_linearity p =
  let s = ref Sstr.empty in
  let add id =
    s := Loc.try3 id.id_loc Sstr.add_new (DuplicateVar id.id) id.id !s
  in
  let rec check p = match p.pat_desc with
    | PPpwild -> ()
    | PPpvar id -> add id
    | PPpapp (_, pl) | PPptuple pl -> List.iter check pl
    | PPprec pfl -> List.iter (fun (_,p) -> check p) pfl
    | PPpas (p, id) -> check p; add id
    | PPpor (p, _) -> check p
  in
  check p

let rec dpat uc env pat =
  let env, n, ty = dpat_node pat.pat_loc uc env pat.pat_desc in
  env, { dp_node = n; dp_ty = ty }

and dpat_node loc uc env = function
  | PPpwild ->
      let ty = fresh_type_var loc in
      env, Pwild, ty
  | PPpvar x ->
      let ty = fresh_type_var loc in
      let env = add_var x.id ty env in
      env, Pvar x, ty
  | PPpapp (x, pl) ->
      let s, tyl, ty = specialize_fsymbol x uc in
      let env, pl = dpat_args s loc uc env tyl pl in
      env, Papp (s, pl), ty
  | PPprec fl ->
      let renv = ref env in
      let fl = List.map (fun (q,e) -> find_lsymbol q uc,e) fl in
      let cs,pjl,flm = Loc.try2 loc parse_record (get_known uc) fl in
      let tyl,ty = Denv.specialize_lsymbol ~loc cs in
      let get_val pj ty = match Mls.find_opt pj flm with
        | Some e ->
            let loc = e.pat_loc in
            let env,e = dpat uc !renv e in
            unify_raise ~loc e.dp_ty ty;
            renv := env;
            e
        | None ->
            { dp_node = Pwild; dp_ty = ty }
      in
      let al = List.map2 get_val pjl tyl in
      !renv, Papp (cs, al), Opt.get ty
  | PPptuple pl ->
      let n = List.length pl in
      let s = fs_tuple n in
      let tyl = List.map (fun _ -> fresh_type_var loc) pl in
      let env, pl = dpat_args s loc uc env tyl pl in
      let ty = tyapp (ts_tuple n) tyl in
      env, Papp (s, pl), ty
  | PPpas (p, x) ->
      let env, p = dpat uc env p in
      let env = add_var x.id p.dp_ty env in
      env, Pas (p,x), p.dp_ty
  | PPpor (p, q) ->
      let env, p = dpat uc env p in
      let env, q = dpat uc env q in
      unify_raise ~loc p.dp_ty q.dp_ty;
      env, Por (p,q), p.dp_ty

and dpat_args ls loc uc env el pl =
  let n = List.length el and m = List.length pl in
  if n <> m then error ~loc (BadArity (ls,m));
  let rec check_arg env = function
    | [], [] ->
        env, []
    | a :: al, p :: pl ->
        let loc = p.pat_loc in
        let env, p = dpat uc env p in
        unify_raise ~loc p.dp_ty a;
        let env, pl = check_arg env (al, pl) in
        env, p :: pl
    | _ ->
        assert false
  in
  check_arg env (el, pl)

let rec trigger_not_a_term_exn = function
  | TermExpected -> true
  | Loc.Located (_, exn) -> trigger_not_a_term_exn exn
  | _ -> false

let param_tys uc pl =
  let s = ref Sstr.empty in
  let ty_of_param (loc,id,gh,ty) =
    if gh then Loc.errorm ~loc "ghost parameters are not allowed here";
    Opt.iter (fun { id = id; id_loc = loc } ->
      s := Loc.try3 loc Sstr.add_new (DuplicateVar id) id !s) id;
    ty_of_dty (dty uc ty) in
  List.map ty_of_param pl

let quant_var uc env (id,ty) =
  let ty = match ty with
    | None -> Denv.fresh_type_var id.id_loc
    | Some ty -> dty uc ty in
  add_var id.id ty env, (id,ty)

let quant_vars uc env qvl =
  let s = ref Sstr.empty in
  let add env (({ id = id; id_loc = loc }, _) as qv) =
    s := Loc.try3 loc Sstr.add_new (DuplicateVar id) id !s;
    quant_var uc env qv in
  Lists.map_fold_left add env qvl

let check_highord uc env x tl = match x with
  | Qident { id = x } when Mstr.mem x env.dvars -> true
  | _ -> env.gvars x <> None ||
      List.length tl > List.length ((find_lsymbol x uc).ls_args)

let apply_highord loc x tl = match List.rev tl with
  | a::[] -> [{pp_loc = loc; pp_desc = PPvar x}; a]
  | a::tl -> [{pp_loc = loc; pp_desc = PPapp (x, List.rev tl)}; a]
  | [] -> assert false

let rec dterm ?(localize=None) uc env { pp_loc = loc; pp_desc = t } =
  let n, ty = dterm_node ~localize loc uc env t in
  let t = { dt_node = n; dt_ty = ty } in
  let rec down loc e = match e.dt_node with
    | Tnamed (Lstr _, e) -> down loc e
    | Tnamed (Lpos _, _) -> t
    | _ -> { dt_node = Tnamed (Lpos loc, t); dt_ty = ty }
  in
  match localize with
    | Some (Some loc) -> down loc t
    | Some None -> down loc t
    | None -> t

and dterm_node ~localize loc uc env = function
  | PPvar (Qident {id=x}) when Mstr.mem x env.dvars ->
      (* local variable *)
      let ty = Mstr.find x env.dvars in
      Tvar x, ty
  | PPvar x when env.gvars x <> None ->
      let vs = Opt.get (env.gvars x) in
      Tgvar vs, dty_of_ty vs.vs_ty
  | PPvar x ->
      (* 0-arity symbol (constant) *)
      let s, tyl, ty = specialize_fsymbol x uc in
      if tyl <> [] then error ~loc (BadArity (s,0));
      Tapp (s, []), ty
  | PPapp (x, tl) when check_highord uc env x tl ->
      let tl = apply_highord loc x tl in
      let atyl, aty = Denv.specialize_lsymbol ~loc fs_func_app in
      let tl = dtype_args ~localize fs_func_app loc uc env atyl tl in
      Tapp (fs_func_app, tl), Opt.get aty
  | PPapp (x, tl) ->
      let s, tyl, ty = specialize_fsymbol x uc in
      let tl = dtype_args ~localize s loc uc env tyl tl in
      Tapp (s, tl), ty
  | PPtuple tl ->
      let n = List.length tl in
      let s = fs_tuple n in
      let tyl = List.map (fun _ -> fresh_type_var loc) tl in
      let tl = dtype_args ~localize s loc uc env tyl tl in
      let ty = tyapp (ts_tuple n) tyl in
      Tapp (s, tl), ty
  | PPinfix (e1, x, e2)
  | PPinnfix (e1, x, e2) ->
      if x.id = "infix <>" then error ~loc TermExpected;
      let s, tyl, ty = specialize_fsymbol (Qident x) uc in
      let tl = dtype_args ~localize s loc uc env tyl [e1; e2] in
      Tapp (s, tl), ty
  | PPconst (Number.ConstInt _ as c) ->
      Tconst c, tyapp Ty.ts_int []
  | PPconst (Number.ConstReal _ as c) ->
      Tconst c, tyapp Ty.ts_real []
  | PPlet (x, e1, e2) ->
      let e1 = dterm ~localize uc env e1 in
      let ty = e1.dt_ty in
      let env = add_var x.id ty env in
      let e2 = dterm ~localize uc env e2 in
      Tlet (e1, x, e2), e2.dt_ty
  | PPmatch (e1, bl) ->
      let t1 = dterm ~localize uc env e1 in
      let ty1 = t1.dt_ty in
      let tb = fresh_type_var loc in (* the type of all branches *)
      let branch (p, e) =
        let env, p = dpat_list uc env ty1 p in
        let loc = e.pp_loc in
        let e = dterm ~localize uc env e in
        unify_raise ~loc e.dt_ty tb;
        p, e
      in
      let bl = List.map branch bl in
      Tmatch (t1, bl), tb
  | PPnamed (x, e1) ->
      let localize = match x with
        | Lpos l -> Some (Some l)
        | Lstr _ -> localize
      in
      let e1 = dterm ~localize uc env e1 in
      Tnamed (x, e1), e1.dt_ty
  | PPcast (e1, ty) ->
      let loc = e1.pp_loc in
      let e1 = dterm ~localize uc env e1 in
      let ty = dty uc ty in
      unify_raise ~loc e1.dt_ty ty;
      e1.dt_node, ty
  | PPif (e1, e2, e3) ->
      let loc = e3.pp_loc in
      let e2 = dterm ~localize uc env e2 in
      let e3 = dterm ~localize uc env e3 in
      unify_raise ~loc e3.dt_ty e2.dt_ty;
      Tif (dfmla ~localize uc env e1, e2, e3), e2.dt_ty
  | PPeps (b, e1) ->
      let env, (x, ty) = quant_var uc env b in
      let e1 = dfmla ~localize uc env e1 in
      Teps (x, ty, e1), ty
  | PPquant ((PPlambda|PPfunc|PPpred) as q, uqu, trl, a) ->
      let env, uqu = quant_vars uc env uqu in
      let trigger e =
        try
          TRterm (dterm ~localize uc env e)
        with exn when trigger_not_a_term_exn exn ->
          TRfmla (dfmla ~localize uc env e)
      in
      let trl = List.map (List.map trigger) trl in
      let e = match q with
        | PPfunc -> TRterm (dterm ~localize uc env a)
        | PPpred -> TRfmla (dfmla ~localize uc env a)
        | PPlambda -> trigger a
        | _ -> assert false
      in
      let id, ty, f = match e with
        | TRterm t ->
            let id = { id = "fc"; id_lab = []; id_loc = loc } in
            let tyl,ty = List.fold_right (fun (_,uty) (tyl,ty) ->
              let nty = tyapp ts_func [uty;ty] in ty :: tyl, nty)
              uqu ([],t.dt_ty)
            in
            let h = { dt_node = Tvar id.id ; dt_ty = ty } in
            let h = List.fold_left2 (fun h (uid,uty) ty ->
              let u = { dt_node = Tvar uid.id ; dt_ty = uty } in
              { dt_node = Tapp (fs_func_app, [h;u]) ; dt_ty = ty })
              h uqu tyl
            in
            id, ty, Fapp (ps_equ, [h;t])
        | TRfmla f ->
            let id = { id = "pc"; id_lab = []; id_loc = loc } in
            let (uid,uty),uqu = match List.rev uqu with
              | uq :: uqu -> uq, List.rev uqu
              | [] -> assert false
            in
            let tyl,ty = List.fold_right (fun (_,uty) (tyl,ty) ->
              let nty = tyapp ts_func [uty;ty] in ty :: tyl, nty)
              uqu ([], tyapp ts_pred [uty])
            in
            let h = { dt_node = Tvar id.id ; dt_ty = ty } in
            let h = List.fold_left2 (fun h (uid,uty) ty ->
              let u = { dt_node = Tvar uid.id ; dt_ty = uty } in
              { dt_node = Tapp (fs_func_app, [h;u]) ; dt_ty = ty })
              h uqu tyl
            in
            let u = { dt_node = Tvar uid.id ; dt_ty = uty } in
            id, ty, Fbinop (Tiff, Fapp (ps_pred_app, [h;u]), f)
      in
      Teps (id, ty, Fquant (Tforall, uqu, trl, f)), ty
  | PPrecord fl ->
      let fl = List.map (fun (q,e) -> find_lsymbol q uc,e) fl in
      let cs,pjl,flm = Loc.try2 loc parse_record (get_known uc) fl in
      let tyl,ty = Denv.specialize_lsymbol ~loc cs in
      let get_val pj ty = match Mls.find_opt pj flm with
        | Some e ->
            let loc = e.pp_loc in
            let e = dterm ~localize uc env e in
            unify_raise ~loc e.dt_ty ty;
            e
        | None -> error ~loc (RecordFieldMissing (cs,pj))
      in
      let al = List.map2 get_val pjl tyl in
      Tapp (cs,al), Opt.get ty
  | PPupdate (e,fl) ->
      let e = dterm ~localize uc env e in
      let fl = List.map (fun (q,e) -> find_lsymbol q uc,e) fl in
      let cs,pjl,flm = Loc.try2 loc parse_record (get_known uc) fl in
      let tyl,ty = Denv.specialize_lsymbol ~loc cs in
      let get_val pj ty = match Mls.find_opt pj flm with
        | Some e ->
            let loc = e.pp_loc in
            let e = dterm ~localize uc env e in
            unify_raise ~loc e.dt_ty ty;
            e
        | None ->
            let ptyl,pty = Denv.specialize_lsymbol ~loc pj in
            unify_raise ~loc (Opt.get pty) ty;
            unify_raise ~loc (List.hd ptyl) e.dt_ty;
            (* FIXME? if e is a complex expression, use let *)
            { dt_node = Tapp (pj,[e]) ; dt_ty = ty }
      in
      let al = List.map2 get_val pjl tyl in
      Tapp (cs,al), Opt.get ty
  | PPquant _ | PPbinop _ | PPunop _ | PPfalse | PPtrue ->
      error ~loc TermExpected

and dfmla ?(localize=None) uc env { pp_loc = loc; pp_desc = f } =
  let f = dfmla_node ~localize loc uc env f in
  let rec down loc e = match e with
    | Fnamed (Lstr _, e) -> down loc e
    | Fnamed (Lpos _, _) -> f
    | _ -> Fnamed (Lpos loc, f)
  in
  match localize with
    | Some (Some loc) -> down loc f
    | Some None -> down loc f
    | None -> f

and dfmla_node ~localize loc uc env = function
  | PPtrue ->
      Ftrue
  | PPfalse ->
      Ffalse
  | PPunop (PPnot, a) ->
      Fnot (dfmla ~localize uc env a)
  | PPbinop (a, (PPand | PPor | PPimplies | PPiff as op), b) ->
      Fbinop (binop op, dfmla ~localize uc env a, dfmla ~localize uc env b)
  | PPif (a, b, c) ->
      Fif (dfmla ~localize uc env a,
           dfmla ~localize uc env b, dfmla ~localize uc env c)
  | PPquant (q, uqu, trl, a) ->
      let env, uqu = quant_vars uc env uqu in
      let trigger e =
        try
          TRterm (dterm ~localize uc env e)
        with exn when trigger_not_a_term_exn exn ->
          TRfmla (dfmla ~localize uc env e)
      in
      let trl = List.map (List.map trigger) trl in
      let q = match q with
        | PPforall -> Tforall
        | PPexists -> Texists
        | _ -> error ~loc PredicateExpected
      in
      Fquant (q, uqu, trl, dfmla ~localize uc env a)
  | PPapp (x, tl) when check_highord uc env x tl ->
      let tl = apply_highord loc x tl in
      let atyl, _ = Denv.specialize_lsymbol ~loc ps_pred_app in
      let tl = dtype_args ~localize ps_pred_app loc uc env atyl tl in
      Fapp (ps_pred_app, tl)
  | PPapp (x, tl) ->
      let s, tyl = specialize_psymbol x uc in
      let tl = dtype_args ~localize s loc uc env tyl tl in
      Fapp (s, tl)
  | PPinfix (e12, op2, e3)
  | PPinnfix (e12, op2, e3) ->
      begin match e12.pp_desc with
        | PPinfix (_, op1, e2)
          when op1.id = "infix <>" || is_psymbol (Qident op1) uc ->
            let e23 = { pp_desc = PPinfix (e2, op2, e3); pp_loc = loc } in
            Fbinop (Tand, dfmla ~localize uc env e12,
                    dfmla ~localize uc env e23)
        | _ when op2.id = "infix <>" ->
            let op2 = { op2 with id = "infix =" } in
            let e0 = { pp_desc = PPinfix (e12, op2, e3); pp_loc = loc } in
            Fnot (dfmla ~localize uc env e0)
        | _ ->
            let s, tyl = specialize_psymbol (Qident op2) uc in
            let tl = dtype_args ~localize s loc uc env tyl [e12;e3] in
            Fapp (s, tl)
      end
  | PPlet (x, e1, e2) ->
      let e1 = dterm ~localize uc env e1 in
      let ty = e1.dt_ty in
      let env = add_var x.id ty env in
      let e2 = dfmla ~localize uc env e2 in
      Flet (e1, x, e2)
  | PPmatch (e1, bl) ->
      let t1 = dterm ~localize uc env e1 in
      let ty1 = t1.dt_ty in
      let branch (p, e) =
        let env, p = dpat_list uc env ty1 p in
        p, dfmla ~localize uc env e
      in
      Fmatch (t1, List.map branch bl)
  | PPnamed (x, f1) ->
      let localize = match x with
        | Lpos l -> Some (Some l)
        | Lstr _ -> localize
      in
      let f1 = dfmla ~localize uc env f1 in
      Fnamed (x, f1)
(*
  | PPvar (Qident s | Qdot (_,s) as x) when is_uppercase s.id.[0] ->
      let pr = find_prop x uc in
      Fvar (Decl.find_prop (Theory.get_known uc) pr)
*)
  | PPvar x ->
      let s, tyl = specialize_psymbol x uc in
      let tl = dtype_args ~localize s loc uc env tyl [] in
      Fapp (s, tl)
  | PPeps _ | PPconst _ | PPcast _ | PPtuple _ | PPrecord _ | PPupdate _ ->
      error ~loc PredicateExpected

and dpat_list uc env ty p =
  check_pat_linearity p;
  let loc = p.pat_loc in
  let env, p = dpat uc env p in
  unify_raise ~loc p.dp_ty ty;
  env, p

and dtype_args ~localize ls loc uc env el tl =
  let n = List.length el and m = List.length tl in
  if n <> m then error ~loc (BadArity (ls,m));
  let rec check_arg = function
    | [], [] ->
        []
    | a :: al, t :: bl ->
        let loc = t.pp_loc in
        let t = dterm ~localize uc env t in
        unify_raise ~loc t.dt_ty a;
        t :: check_arg (al, bl)
    | _ ->
        assert false
  in
  check_arg (el, tl)

(** Typing declarations, that is building environments. *)

open Ptree

let add_types dl th =
  let def = List.fold_left
    (fun def d ->
      let id = d.td_ident.id in
      Mstr.add_new (Loc.Located (d.td_loc, ClashSymbol id)) id d def)
    Mstr.empty dl
  in
  let tysymbols = Hstr.create 17 in
  let rec visit x =
    let d = Mstr.find x def in
    try
      match Hstr.find tysymbols x with
        | None -> errorm ~loc:d.td_loc "Cyclic type definition"
        | Some ts -> ts
    with Not_found ->
      Hstr.add tysymbols x None;
      let vars = Hstr.create 17 in
      let vl = List.map (fun id ->
        if Hstr.mem vars id.id then
          error ~loc:id.id_loc (DuplicateTypeVar id.id);
        let i = create_user_tv id.id in
        Hstr.add vars id.id i;
        i) d.td_params
      in
      let id = create_user_id d.td_ident in
      let ts = match d.td_def with
        | TDalias ty ->
            let rec apply = function
              | PPTtyvar (v, _) ->
                  begin
                    try ty_var (Hstr.find vars v.id)
                    with Not_found -> error ~loc:v.id_loc (UnboundTypeVar v.id)
                  end
              | PPTtyapp (q, tyl) ->
                  let ts = match q with
                    | Qident x when Mstr.mem x.id def ->
                        visit x.id
                    | Qident _ | Qdot _ ->
                        find_tysymbol q th
                  in
                  Loc.try2 (qloc q) ty_app ts (List.map apply tyl)
              | PPTtuple tyl ->
                  let ts = ts_tuple (List.length tyl) in
                  ty_app ts (List.map apply tyl)
            in
            create_tysymbol id vl (Some (apply ty))
        | TDabstract | TDalgebraic _ ->
            create_tysymbol id vl None
        | TDrecord _ ->
            assert false
      in
      Hstr.add tysymbols x (Some ts);
      ts
  in
  let th' =
    let add_ts (abstr,alias) d =
      let ts = visit d.td_ident.id in
      if ts.ts_def = None then ts::abstr, alias else abstr, ts::alias in
    let abstr,alias = List.fold_left add_ts ([],[]) dl in
    try
      let th = List.fold_left add_ty_decl th abstr in
      let th = List.fold_left add_ty_decl th alias in
      th
    with ClashSymbol s -> error ~loc:(Mstr.find s def).td_loc (ClashSymbol s)
  in
  let csymbols = Hstr.create 17 in
  let decl d (abstr,algeb,alias) =
    let ts = match Hstr.find tysymbols d.td_ident.id with
      | None ->
          assert false
      | Some ts ->
          ts
    in
    match d.td_def with
      | TDabstract -> ts::abstr, algeb, alias
      | TDalias _ -> abstr, algeb, ts::alias
      | TDalgebraic cl ->
          let ht = Hstr.create 17 in
          let constr = List.length cl in
          let opaque = Stv.of_list ts.ts_args in
          let ty = ty_app ts (List.map ty_var ts.ts_args) in
          let projection (_,id,_,_) fty = match id with
            | None -> None
            | Some id ->
                try
                  let pj = Hstr.find ht id.id in
                  let ty = Opt.get pj.ls_value in
                  ignore (Loc.try2 id.id_loc ty_equal_check ty fty);
                  Some pj
                with Not_found ->
                  let fn = create_user_id id in
                  let pj = create_fsymbol ~opaque fn [ty] fty in
                  Hstr.replace csymbols id.id id.id_loc;
                  Hstr.replace ht id.id pj;
                  Some pj
          in
          let constructor (loc, id, pl) =
            let tyl = param_tys th' pl in
            let pjl = List.map2 projection pl tyl in
            Hstr.replace csymbols id.id loc;
            create_fsymbol ~opaque ~constr (create_user_id id) tyl ty, pjl
          in
          abstr, (ts, List.map constructor cl) :: algeb, alias
      | TDrecord _ ->
          assert false
  in
  let abstr,algeb,alias = List.fold_right decl dl ([],[],[]) in
  try
    let th = List.fold_left add_ty_decl th abstr in
    let th = if algeb = [] then th else add_data_decl th algeb in
    let th = List.fold_left add_ty_decl th alias in
    th
  with
    | ClashSymbol s ->
        error ~loc:(Hstr.find csymbols s) (ClashSymbol s)
    | RecordFieldMissing ({ ls_name = { id_string = s }} as cs,ls) ->
        error ~loc:(Hstr.find csymbols s) (RecordFieldMissing (cs,ls))
    | DuplicateRecordField ({ ls_name = { id_string = s }} as cs,ls) ->
        error ~loc:(Hstr.find csymbols s) (DuplicateRecordField (cs,ls))

let prepare_typedef td =
  if td.td_model then
    errorm ~loc:td.td_loc "model types are not allowed in pure theories";
  if td.td_vis <> Public then
    errorm ~loc:td.td_loc "pure types cannot be abstract or private";
  if td.td_inv <> [] then
    errorm ~loc:td.td_loc "pure types cannot have invariants";
  match td.td_def with
  | TDabstract | TDalgebraic _ | TDalias _ ->
      td
  | TDrecord fl ->
      let field { f_loc = loc; f_ident = id; f_pty = ty;
                  f_mutable = mut; f_ghost = gh } =
        if mut then errorm ~loc "a logic record field cannot be mutable";
        if gh then errorm ~loc "a logic record field cannot be ghost";
        loc, Some id, false, ty
      in
      (* constructor for type t is "mk t" (and not String.capitalize t) *)
      let id = { td.td_ident with id = "mk " ^ td.td_ident.id } in
      { td with td_def = TDalgebraic [td.td_loc, id, List.map field fl] }

let add_types dl th =
  add_types (List.map prepare_typedef dl) th

let env_of_vsymbol_list vl =
  List.fold_left (fun env v -> Mstr.add v.vs_name.id_string v env) Mstr.empty vl

let add_logics dl th =
  let lsymbols = Hstr.create 17 in
  let denvs = Hstr.create 17 in
  (* 1. create all symbols and make an environment with these symbols *)
  let create_symbol th d =
    let id = d.ld_ident.id in
    let denv = denv_empty in
    Hstr.add denvs id denv;
    let v = create_user_id d.ld_ident in
    let pl = param_tys th d.ld_params in
    let ty = Opt.map (fun t -> ty_of_dty (dty th t)) d.ld_type in
    let opaque = opaque_tvs d.ld_params d.ld_type in
    let ls = create_lsymbol ~opaque v pl ty in
    Hstr.add lsymbols id ls;
    Loc.try2 d.ld_loc add_param_decl th ls
  in
  let th' = List.fold_left create_symbol th dl in
  (* 2. then type-check all definitions *)
  let type_decl d (abst,defn) =
    let id = d.ld_ident.id in
    let dadd_var denv (_,x,_,ty) = match x with
      | Some id -> add_var id.id (dty th' ty) denv
      | None -> denv
    in
    let denv = Hstr.find denvs id in
    let denv = List.fold_left dadd_var denv d.ld_params in
    let create_var (loc,x,_,_) ty =
      let id = match x with
        | Some id -> create_user_id id
        | None -> id_user "_" loc in
      create_vsymbol id ty in
    let ls = Hstr.find lsymbols id in
    let vl = List.map2 create_var d.ld_params ls.ls_args in
    let env = env_of_vsymbol_list vl in
    match d.ld_def, d.ld_type with
    | None, _ -> ls :: abst, defn
    | Some e, None -> (* predicate *)
        let f = dfmla th' denv e in
        abst, (ls, vl, fmla env f) :: defn
    | Some e, Some ty -> (* function *)
        let t = dterm th' denv e in
        unify_raise ~loc:e.pp_loc t.dt_ty (dty th' ty);
        abst, (ls, vl, term env t) :: defn
  in
  let abst,defn = List.fold_right type_decl dl ([],[]) in
  (* 3. detect opacity *)
  let ldefns defn =
    let ht = Hls.create 3 in
    let add_ls (ls,_,_) =
      let tvs = oty_freevars Stv.empty ls.ls_value in
      let tvs = List.fold_left ty_freevars tvs ls.ls_args in
      Hls.replace ht ls tvs in
    List.iter add_ls defn;
    let compared s ls args value =
      let sbs = oty_match Mtv.empty ls.ls_value value in
      let sbs = List.fold_left2 ty_match sbs ls.ls_args args in
      let opq = try Hls.find ht ls with Not_found -> ls.ls_opaque in
      Mtv.fold (fun _ ty s -> ty_freevars s ty) (Mtv.set_diff sbs opq) s in
    let check_ld fixp (ls,_,t) =
      let opq = Hls.find ht ls in
      let npq = Stv.diff opq (t_app_fold compared Stv.empty t) in
      Hls.replace ht ls npq;
      fixp && Stv.equal opq npq in
    let rec fixp () =
      if not (List.fold_left check_ld true defn) then fixp () in
    fixp ();
    let mk_sbs sbs ({ls_name = id} as ls,_,_) =
      let opaque = Stv.union ls.ls_opaque (Hls.find ht ls) in
      if Stv.equal ls.ls_opaque opaque then sbs else
      let nls = create_lsymbol ~opaque (id_clone id) ls.ls_args ls.ls_value in
      Mls.add ls nls sbs in
    let sbs = List.fold_left mk_sbs Mls.empty defn in
    let mk_ld (ls,vl,t) =
      let get_ls ls = Mls.find_def ls ls sbs in
      make_ls_defn (get_ls ls) vl (t_s_map (fun ty -> ty) get_ls t) in
    List.map mk_ld defn
  in
  let th = List.fold_left add_param_decl th abst in
  let th = if defn = [] then th else add_logic_decl th (ldefns defn) in
  th

let type_term uc gfn t =
  let denv = denv_empty_with_globals gfn in
  let t = dterm ~localize:(Some None) uc denv t in
  term Mstr.empty t

let type_fmla uc gfn f =
  let denv = denv_empty_with_globals gfn in
  let f = dfmla ~localize:(Some None) uc denv f in
  fmla Mstr.empty f

let add_prop k loc s f th =
  let pr = create_prsymbol (create_user_id s) in
  let f = type_fmla th (fun _ -> None) f in
  Loc.try4 loc add_prop_decl th k pr f

let loc_of_id id = Opt.get id.Ident.id_loc

let add_inductives s dl th =
  (* 1. create all symbols and make an environment with these symbols *)
  let psymbols = Hstr.create 17 in
  let create_symbol th d =
    let id = d.in_ident.id in
    let v = create_user_id d.in_ident in
    let pl = param_tys th d.in_params in
    let opaque = opaque_tvs d.in_params None in
    let ps = create_psymbol ~opaque v pl in
    Hstr.add psymbols id ps;
    Loc.try2 d.in_loc add_param_decl th ps
  in
  let th' = List.fold_left create_symbol th dl in
  (* 2. then type-check all definitions *)
  let propsyms = Hstr.create 17 in
  let type_decl d =
    let id = d.in_ident.id in
    let ps = Hstr.find psymbols id in
    let clause (loc, id, f) =
      Hstr.replace propsyms id.id loc;
      let f = type_fmla th' (fun _ -> None) f in
      create_prsymbol (create_user_id id), f
    in
    ps, List.map clause d.in_def
  in
  try add_ind_decl th s (List.map type_decl dl)
  with
  | ClashSymbol s ->
      error ~loc:(Hstr.find propsyms s) (ClashSymbol s)
  | InvalidIndDecl (ls,pr) ->
      error ~loc:(loc_of_id pr.pr_name) (InvalidIndDecl (ls,pr))
  | NonPositiveIndDecl (ls,pr,s) ->
      error ~loc:(loc_of_id pr.pr_name) (NonPositiveIndDecl (ls,pr,s))

(* parse declarations *)

let prop_kind = function
  | Kaxiom -> Paxiom
  | Kgoal -> Pgoal
  | Klemma -> Plemma

let find_theory env lenv q id = match q with
  | [] ->
      (* local theory *)
      begin try Mstr.find id lenv
      with Not_found -> read_lib_theory env [] id end
  | _ :: _ ->
      (* theory in file f *)
      read_lib_theory env q id

let rec clone_ns kn sl path ns2 ns1 s =
  let qualid fmt path = Pp.print_list
    (fun fmt () -> pp_print_char fmt '.')
    pp_print_string fmt (List.rev path) in
  let s = Mstr.fold (fun nm ns1 acc ->
    let ns2 = Mstr.find_def empty_ns nm ns2.ns_ns in
    clone_ns kn sl (nm::path) ns2 ns1 acc) ns1.ns_ns s
  in
  let inst_ts = Mstr.fold (fun nm ts1 acc ->
    match Mstr.find_opt nm ns2.ns_ts with
    | Some ts2 when ts_equal ts1 ts2 -> acc
    | Some _ when not (Sid.mem ts1.ts_name sl) ->
        raise (NonLocal ts1.ts_name)
    | Some _ when ts1.ts_def <> None ->
        raise (CannotInstantiate ts1.ts_name)
    | Some ts2 ->
        begin match (Mid.find ts1.ts_name kn).d_node with
          | Decl.Dtype _ -> Mts.add_new (ClashSymbol nm) ts1 ts2 acc
          | _ -> raise (CannotInstantiate ts1.ts_name)
        end
    | None when not (Sid.mem ts1.ts_name sl) -> acc
    | None when ts1.ts_def <> None -> acc
    | None ->
        begin match (Mid.find ts1.ts_name kn).d_node with
          | Decl.Dtype _ -> Loc.errorm
              "type symbol %a not found in the target theory"
              qualid (nm::path)
          | _ -> acc
        end)
    ns1.ns_ts s.inst_ts
  in
  let inst_ls = Mstr.fold (fun nm ls1 acc ->
    match Mstr.find_opt nm ns2.ns_ls with
    | Some ls2 when ls_equal ls1 ls2 -> acc
    | Some _ when not (Sid.mem ls1.ls_name sl) ->
       raise (NonLocal ls1.ls_name)
    | Some ls2 ->
        begin match (Mid.find ls1.ls_name kn).d_node with
          | Decl.Dparam _ -> Mls.add_new (ClashSymbol nm) ls1 ls2 acc
          | _ -> raise (CannotInstantiate ls1.ls_name)
        end
    | None when not (Sid.mem ls1.ls_name sl) -> acc
    | None ->
        begin match (Mid.find ls1.ls_name kn).d_node with
          | Decl.Dparam _ -> Loc.errorm
              "%s symbol %a not found in the target theory"
              (if ls1.ls_value <> None then "function" else "predicate")
              qualid (nm::path)
          | _ -> acc
        end)
    ns1.ns_ls s.inst_ls
  in
  { s with inst_ts = inst_ts; inst_ls = inst_ls }

let add_decl loc th = function
  | TypeDecl dl ->
      add_types dl th
  | LogicDecl dl ->
      add_logics dl th
  | IndDecl (s, dl) ->
      add_inductives s dl th
  | PropDecl (k, s, f) ->
      add_prop (prop_kind k) loc s f th
  | Meta (id, al) ->
      let convert = function
        | PMAty ty -> MAty (ty_of_pty th ty)
        | PMAfs q  -> MAls (find_fsymbol q th)
        | PMAps q  -> MAls (find_psymbol q th)
        | PMApr q  -> MApr (find_prop q th)
        | PMAstr s -> MAstr s
        | PMAint i -> MAint i
      in
      let add s = add_meta th (lookup_meta s) (List.map convert al) in
      Loc.try1 loc add id.id

let add_decl loc th d =
  if Debug.test_flag debug_parse_only then th else
  Loc.try3 loc add_decl loc th d

let type_inst th t s =
  let add_inst s = function
    | CSns (loc,p,q) ->
      let find ns x = find_namespace_ns x ns in
      let ns1 = Opt.fold find t.th_export p in
      let ns2 = Opt.fold find (get_namespace th) q in
      Loc.try6 loc clone_ns t.th_known t.th_local [] ns2 ns1 s
    | CStsym (loc,p,[],PPTtyapp (q,[])) ->
      let ts1 = find_tysymbol_ns p t.th_export in
      let ts2 = find_tysymbol q th in
      if Mts.mem ts1 s.inst_ts
      then error ~loc (ClashSymbol ts1.ts_name.id_string);
      { s with inst_ts = Mts.add ts1 ts2 s.inst_ts }
    | CStsym (loc,p,tvl,pty) ->
      let ts1 = find_tysymbol_ns p t.th_export in
      let id = id_user (ts1.ts_name.id_string ^ "_subst") loc in
      let tvl = List.map (fun id -> create_user_tv id.id) tvl in
      let def = Some (ty_of_pty th pty) in
      let ts2 = Loc.try3 loc create_tysymbol id tvl def in
      if Mts.mem ts1 s.inst_ts
      then error ~loc (ClashSymbol ts1.ts_name.id_string);
      { s with inst_ts = Mts.add ts1 ts2 s.inst_ts }
    | CSfsym (loc,p,q) ->
      let ls1 = find_fsymbol_ns p t.th_export in
      let ls2 = find_fsymbol q th in
      if Mls.mem ls1 s.inst_ls
      then error ~loc (ClashSymbol ls1.ls_name.id_string);
      { s with inst_ls = Mls.add ls1 ls2 s.inst_ls }
    | CSpsym (loc,p,q) ->
      let ls1 = find_psymbol_ns p t.th_export in
      let ls2 = find_psymbol q th in
      if Mls.mem ls1 s.inst_ls
      then error ~loc (ClashSymbol ls1.ls_name.id_string);
      { s with inst_ls = Mls.add ls1 ls2 s.inst_ls }
    | CSlemma (loc,p) ->
      let pr = find_prop_ns p t.th_export in
      if Spr.mem pr s.inst_lemma || Spr.mem pr s.inst_goal
      then error ~loc (ClashSymbol pr.pr_name.id_string);
      { s with inst_lemma = Spr.add pr s.inst_lemma }
    | CSgoal (loc,p) ->
      let pr = find_prop_ns p t.th_export in
      if Spr.mem pr s.inst_lemma || Spr.mem pr s.inst_goal
      then error ~loc (ClashSymbol pr.pr_name.id_string);
      { s with inst_goal = Spr.add pr s.inst_goal }
  in
  List.fold_left add_inst empty_inst s

let add_use_clone env lenv th loc (use, subst) =
  if Debug.test_flag debug_parse_only then th else
  let use_or_clone th =
    let q, id = split_qualid use.use_theory in
    let t = find_theory env lenv q id in
    if Debug.test_flag Glob.flag then
      Glob.use (match use.use_theory with Qident x | Qdot (_,x) -> x.id_loc) t.th_name;
    match subst with
    | None -> use_export th t
    | Some s ->
        warn_clone_not_abstract loc t;
        clone_export th t (type_inst th t s)
  in
  let use_or_clone th = match use.use_import with
    | Some (import, use_as) ->
        (* use T = namespace T use_export T end *)
        let th = open_namespace th use_as in
        let th = use_or_clone th in
        close_namespace th import
    | None ->
        use_or_clone th
  in
  Loc.try1 loc use_or_clone th

let close_theory lenv th =
  if Debug.test_flag debug_parse_only then lenv else
  let th = close_theory th in
  let id = th.th_name.id_string in
  let loc = th.th_name.Ident.id_loc in
  if Mstr.mem id lenv then error ?loc (ClashTheory id);
  Mstr.add id th lenv

let close_namespace loc import th =
  Loc.try2 loc close_namespace th import

(* incremental parsing *)

let open_file, close_file =
  let lenv = Stack.create () in
  let uc   = Stack.create () in
  let open_file env path =
    Stack.push Mstr.empty lenv;
    let open_theory id =
      Stack.push (Theory.create_theory ~path (Denv.create_user_id id)) uc in
    let close_theory () =
      Stack.push (close_theory (Stack.pop lenv) (Stack.pop uc)) lenv in
    let open_namespace name =
      Stack.push (Theory.open_namespace (Stack.pop uc) name) uc in
    let close_namespace loc imp =
      Stack.push (close_namespace loc imp (Stack.pop uc)) uc in
    let new_decl loc d =
      Stack.push (add_decl loc (Stack.pop uc) d) uc in
    let use_clone loc use =
      let lenv = Stack.top lenv in
      Stack.push (add_use_clone env lenv (Stack.pop uc) loc use) uc in
    { open_theory = open_theory;
      close_theory = close_theory;
      open_namespace = open_namespace;
      close_namespace = close_namespace;
      new_decl = new_decl;
      use_clone = use_clone;
      open_module = (fun _ -> assert false);
      close_module = (fun _ -> assert false);
      new_pdecl = (fun _ -> assert false); }
  in
  let close_file () = Stack.pop lenv in
  open_file, close_file

(*
Local Variables:
compile-command: "unset LANG; make -C ../.."
End:
*)
