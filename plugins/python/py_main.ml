(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3
open Pmodule
open Py_ast
open Ptree
open Wstdlib

let debug = Debug.register_flag "python"
  ~desc:"mini-python plugin debug flag"

(* NO! this will be executed at plugin load, thus
disabling the warning for ALL WHY3 USERS even if they don't
use the python front-end
let () = Debug.set_flag Dterm.debug_ignore_unused_var
*)

let mk_id ~loc name =
  { id_str = name; id_ats = []; id_loc = loc }

let mk_prime id =
  { id with id_str = id.id_str ^ "'" }
let mk_prime_n =
  let n = ref 0 in
  fun id -> incr n; { id with id_str = id.id_str ^ "'" ^ string_of_int !n }

let id_infix ~loc s = mk_id ~loc (Ident.op_infix s)
let infix  ~loc s = Qident (id_infix ~loc s)
let prefix ~loc s = Qident (mk_id ~loc (Ident.op_prefix s))
let get_op ~loc   = Qident (mk_id ~loc (Ident.op_get ""))
let set_op ~loc   = Qident (mk_id ~loc (Ident.op_set ""))

let mk_expr ~loc d =
  { expr_desc = d; expr_loc = loc }
let mk_pat ~loc d =
  { pat_desc = d; pat_loc = loc }
let mk_unit ~loc =
  mk_expr ~loc (Etuple [])
let mk_var ~loc id =
  mk_expr ~loc (Eident (Qident id))
let mk_pure t =
  mk_expr ~loc:t.term_loc (Epure t)

let mk_ref ~loc e =
  mk_expr ~loc (Eapply (mk_expr ~loc Eref, e))
let mk_lref ~loc id =
  mk_expr ~loc (Easref (Qident id))

let array_set ~loc a i v =
  mk_expr ~loc (Eidapp (set_op ~loc, [a; i; v]))
let constant ~loc i =
  mk_expr ~loc (Econst (Constant.int_const_of_int i))
let constant_s ~loc s =
  let int_lit = Number.(int_literal ILitDec ~neg:false s) in
  mk_expr ~loc (Econst (Constant.ConstInt int_lit))
let len ~loc =
  Qident (mk_id ~loc "len")

let array_make ~loc n v =
  mk_expr ~loc (Eidapp (Qdot (Qident (mk_id ~loc "Python"), mk_id ~loc "make"),
                        [n; v]))
let array_empty ~loc =
  mk_expr ~loc (Eidapp (Qdot (Qident (mk_id ~loc "Python"), mk_id ~loc "empty"), [mk_unit ~loc]))
let set_ref id =
  { id with id_ats = ATstr Pmodule.ref_attr :: id.id_ats }

let empty_spec = {
  sp_pre     = [];
  sp_post    = [];
  sp_xpost   = [];
  sp_reads   = [];
  sp_writes  = [];
  sp_alias   = [];
  sp_variant = [];
  sp_checkrw = false;
  sp_diverge = false;
  sp_partial = false;
}

type env = {
  vars: ident Mstr.t;
}

let empty_env =
  { vars = Mstr.empty }

let is_const (e: Py_ast.expr list) =
  match List.nth e 2 with
  | {Py_ast.expr_desc=Eint "1";_}  -> 1
  | {Py_ast.expr_desc=Eunop (Uneg, {Py_ast.expr_desc=Eint "1";_});_} -> -1
  | _ -> 0

let add_var env id =
  { vars = Mstr.add id.id_str id env.vars }
let add_param env (id, _) =
  add_var env id

let for_vars ~loc x =
  let x = x.id_str in
  mk_id ~loc (x ^ "'index"), mk_id ~loc (x ^ "'list")

let rec has_stmt p = function
  | Dstmt s -> p s || begin match s.stmt_desc with
      | Sbreak | Scontinue  | Sreturn _ | Sassign _ | Slabel _ | Spass _
      | Seval _ | Sset _ | Sblock _ | Sassert _ | Swhile _ | Scall_lemma _
      -> false
    | Sif (_, bl1, bl2) -> has_stmtl p bl1 || has_stmtl p bl2
    | Sfor (_, _, _, bl) -> has_stmtl p bl end
  | _ -> false
and has_stmtl p bl = List.exists (has_stmt p) bl

let rec expr_has_call id e = match e.Py_ast.expr_desc with
  | Enone | Ebool _ | Eint _ | Estring _ | Py_ast.Eident _ -> false
  | Emake (e1, e2) | Eget (e1, e2) | Ebinop (_, e1, e2) ->
    expr_has_call id e1 || expr_has_call id e2
  | Econd(c,e1,e2) -> expr_has_call id c || expr_has_call id e1 || expr_has_call id e2
  | Eunop (_, e1) -> expr_has_call id e1
  | Edot (e, f, el) -> id.id_str = f.id_str || List.exists (expr_has_call id) (e::el)
  | Ecall (f, el) -> id.id_str = f.id_str || List.exists (expr_has_call id) el
  | Elist el -> List.exists (expr_has_call id) el
  | Py_ast.Etuple el -> List.exists (expr_has_call id) el

let rec stmt_has_call id s = match s.stmt_desc with
  | Sbreak | Scontinue | Slabel _ | Sassert _ | Spass _ -> false
  | Sreturn e | Sassign (_, e) | Seval e -> expr_has_call id e
  | Sblock s -> block_has_call id s
  | Scall_lemma (f, _) -> id.id_str = f.id_str
  | Sset (e1, e2, e3) ->
    expr_has_call id e1 || expr_has_call id e2 || expr_has_call id e3
  | Sif (e, s1, s2) -> expr_has_call id e || block_has_call id s1 || block_has_call id s2
  | Sfor (_, e, _, s) | Swhile (e, _, _, s) -> expr_has_call id e || block_has_call id s
and block_has_call id = has_stmtl (stmt_has_call id)

let rec is_list (e: Py_ast.expr) =
  match e.Py_ast.expr_desc with
  | Py_ast.Ecall (f, _) when f.id_str = "slice" -> true
  | Py_ast.Ebinop (Py_ast.Badd, e, _) -> is_list e
  | Py_ast.Edot (_, m, _) -> m.id_str = "copy"
  | Py_ast.Elist _ | Py_ast.Emake _ -> true
  | _ -> false

let rec expr env {Py_ast.expr_loc = loc; Py_ast.expr_desc = d } = match d with
  | Py_ast.Enone ->
    mk_unit ~loc
  | Py_ast.Ebool b ->
    mk_expr ~loc (if b then Etrue else Efalse)
  | Py_ast.Eint s ->
    constant_s ~loc s
  | Py_ast.Estring _s ->
    mk_unit ~loc (*FIXME*)
  | Py_ast.Eident id ->
    if not (Mstr.mem id.id_str env.vars) then
      Loc.errorm ~loc "unbound variable %s" id.id_str;
     mk_expr ~loc (Eident (Qident id))
  | Py_ast.Econd (c, e1, e2) ->
    let c = expr env c and e1 = expr env e1 and e2 = expr env e2 in
    mk_expr ~loc (Eif(c,e1,e2))
  | Py_ast.Ebinop (op, e1, e2) ->
    let isl = is_list e1 in
    let e1 = expr env e1 in
    let e2 = expr env e2 in
    mk_expr ~loc (match op with
      | Py_ast.Band -> Eand (e1, e2)
      | Py_ast.Bor  -> Eor  (e1, e2)
      | Py_ast.Badd when isl ->
         let id = mk_id ~loc "add_list" in
         Eidapp (Qident id, [e1; e2])
      | Py_ast.Badd -> Eidapp (infix ~loc "+",  [e1; e2])
      | Py_ast.Bsub -> Eidapp (infix ~loc "-",  [e1; e2])
      | Py_ast.Bmul -> Eidapp (infix ~loc "*",  [e1; e2])
      | Py_ast.Bdiv -> Eidapp (infix ~loc "//", [e1; e2])
      | Py_ast.Bmod -> Eidapp (infix ~loc "%",  [e1; e2])
      | Py_ast.Beq  -> Einnfix (e1, id_infix ~loc "=",  e2)
      | Py_ast.Bneq -> Einnfix (e1, id_infix ~loc "<>", e2)
      | Py_ast.Blt  -> Einnfix (e1, id_infix ~loc "<",  e2)
      | Py_ast.Ble  -> Einnfix (e1, id_infix ~loc "<=", e2)
      | Py_ast.Bgt  -> Einnfix (e1, id_infix ~loc ">",  e2)
      | Py_ast.Bge  -> Einnfix (e1, id_infix ~loc ">=", e2)
    )
  | Py_ast.Eunop (Py_ast.Uneg, e) ->
    mk_expr ~loc (Eidapp (prefix ~loc "-", [expr env e]))
  | Py_ast.Eunop (Py_ast.Unot, e) ->
    mk_expr ~loc (Enot (expr env e))

  | Py_ast.Edot (e, f, el) ->
    let el = List.map (expr env) (e::el) in
    let id = Qdot (Qident (mk_id ~loc "Python"), f) in
    mk_expr ~loc (Eidapp (id, el))

  | Py_ast.Ecall ({id_str="slice"} as id, [e1;e2;e3]) ->

    let zero = expr env ({Py_ast.expr_loc = loc; Py_ast.expr_desc = Eint "0"}) in
    let e1' = mk_id ~loc "e1'" in
    let e1_var = mk_var ~loc e1' in

    let len = mk_expr ~loc (Eidapp (Qident (mk_id ~loc "len"), [e1_var])) in

    let e2, e3 = match e2, e3 with
      | {Py_ast.expr_desc=Py_ast.Enone}, {Py_ast.expr_desc=Py_ast.Enone} -> zero, len
      | _                              , {Py_ast.expr_desc=Py_ast.Enone} -> expr env e2, len
      | {Py_ast.expr_desc=Py_ast.Enone}, _                               -> zero, expr env e3
      | _                              , _                               -> expr env e2, expr env e3
    in

    let id = Qdot (Qident (mk_id ~loc "Python"), id) in

    mk_expr ~loc (Elet (e1', false, Expr.RKnone, expr env e1,
      mk_expr ~loc (Eidapp (id, [e1_var;e2;e3]))
    ))

  | Py_ast.Ecall ({id_str="range"} as id, els) when List.length els < 4 ->
    let zero = {Py_ast.expr_loc = loc; Py_ast.expr_desc = Eint "0"} in
    let from_to_step, id = match els with
                        | [e]        -> [zero; e], id
                        | [e1;e2]    -> [e1; e2], id
                        | [e1;e2;e3] -> [e1; e2; e3], mk_id ~loc "range3"
                        | _          -> assert false
    in
    let el = List.map (expr env) from_to_step in
    mk_expr ~loc (Eidapp (Qident id, el))

  | Py_ast.Ecall ({id_str="print"}, el) ->
    let eval res e =
      mk_expr ~loc (Elet (mk_id ~loc "_", false, Expr.RKnone, expr env e, res)) in
    List.fold_left eval (mk_unit ~loc) el
  | Py_ast.Ecall (id, el) ->
    let el = if el = [] then [mk_unit ~loc] else List.map (expr env) el in
    mk_expr ~loc (Eidapp (Qident id, el))
  | Py_ast.Emake (e1, e2) -> (* [e1]*e2 *)
    array_make ~loc (expr env e2) (expr env e1)
  | Py_ast.Elist [] ->
    array_empty ~loc
  | Py_ast.Elist (e :: el) ->
    let n = 1 + List.length el in
    let n = constant ~loc n in
    let e = expr env e in
    let id = mk_id ~loc "new array" in
    mk_expr ~loc (Elet (id, false, Expr.RKnone, array_make ~loc n e,
    let i = ref 0 in
    let init seq e =
      incr i; let i = constant ~loc !i in
      let assign = array_set ~loc (mk_var ~loc id) i (expr env e) in
      mk_expr ~loc (Esequence (assign, seq)) in
    List.fold_left init (mk_var ~loc id) el))
  | Py_ast.Eget (e1, e2) ->
    mk_expr ~loc (Eidapp (get_op ~loc, [expr env e1; expr env e2]))
  | Py_ast.Etuple el -> mk_expr ~loc (Etuple (List.map (expr env) el))

let no_params ~loc = [loc, None, false, Some (PTtuple [])]

let mk_for_params exps loc env =

  let mk_op1 op ub = mk_expr ~loc (Eidapp (infix ~loc op, [expr env ub; constant ~loc 1])) in
  let mk_minus1 ub = mk_op1 "-" ub in
  let mk_plus1 ub = mk_op1 "+" ub in

  match exps with
  | [e1] ->
      let zero = {Py_ast.expr_loc = loc; Py_ast.expr_desc = Eint "0"} in
      expr env zero, mk_minus1 e1, Expr.To
  | [e1;e2] ->
      expr env e1, mk_minus1 e2, Expr.To
  | [e1;e2;_] ->
      begin match is_const exps with
      |  1 -> expr env e1, mk_minus1 e2, Expr.To
      | -1 -> expr env e1, mk_plus1 e2, Expr.DownTo
      | _  -> assert false
      end
  | _ -> assert false

let rec new_vars env (e: Py_ast.expr) =
  match e.Py_ast.expr_desc with
  | Py_ast.Eident id ->
      if Mstr.mem id.id_str env.vars then [] else [id]
  | Py_ast.Etuple el ->
      List.sort_uniq compare (List.concat (List.map (new_vars env) el))
  | _ -> []

(*
  (r1,..)..(rn,..) := e1,...em
  ==> match e1,...em with (r'1,..)..(r'n,..) ->
      r1 := r'1; .. let ri := r'i in ...
 *)

let rec build_pat1 (e1: Py_ast.expr) =
  let loc = e1.Py_ast.expr_loc in
  match e1.Py_ast.expr_desc with
  | Py_ast.Etuple el1 ->
      mk_pat ~loc (Ptuple (List.map build_pat1 el1))
  | Py_ast.Eident id ->
      mk_pat ~loc:id.id_loc (Pvar (mk_prime id))
  | _ ->
      let id = mk_id ~loc "_" in
      mk_pat ~loc (Pvar (mk_prime_n id))

let rec build_pat2 (e1: Py_ast.expr) (e2: expr) =
  let loc = e1.Py_ast.expr_loc in
  match e1.Py_ast.expr_desc, e2.expr_desc with
  | Py_ast.Etuple el1, Etuple el2 ->
      if List.length el1 = List.length el2 then
        mk_pat ~loc (Ptuple (List.map2 build_pat2 el1 el2))
      else
        Loc.errorm ~loc "illegal assignment"
  | Py_ast.Etuple el1, _ ->
      mk_pat ~loc (Ptuple (List.map build_pat1 el1))
  | Py_ast.Eident id, _ ->
      mk_pat ~loc:id.id_loc (Pvar (mk_prime id))
  | _ ->
      let id = mk_id ~loc "_" in
      mk_pat ~loc:id.id_loc (Pvar (mk_prime_n id))

let rec flatten_updates (e: Py_ast.expr) (p: pattern) =
  match e.Py_ast.expr_desc, p.pat_desc with
  | Py_ast.Etuple le, Ptuple lp -> List.concat (List.map2 flatten_updates le lp)
  | _, Pvar _ -> [e, p]
  | _ -> failwith "flatten_updates"

let rec gen_updates env lp cnt =
  match lp with
  | [] -> cnt
  | ({ Py_ast.expr_desc = Py_ast.Eident id },
     { pat_desc = Pvar id'; pat_loc = loc }) :: lp'
        when Mstr.mem id.id_str env.vars ->
      let a = mk_expr ~loc (Eassign [mk_lref ~loc id, None, mk_var ~loc id']) in
      mk_expr ~loc (Esequence (a, gen_updates env lp' cnt))
  | ({ Py_ast.expr_desc = Py_ast.Eident id},
     { pat_desc = Pvar id'; pat_loc = loc }) :: lp' ->
      mk_expr ~loc
        (Elet (set_ref id, false, Expr.RKnone, mk_ref ~loc (mk_var ~loc id'),
               gen_updates env lp' cnt))
  | ({ Py_ast.expr_desc = Eget (e1,e2) },
     { pat_desc = Pvar id'; pat_loc = loc }) :: lp' ->
      let a =
        array_set ~loc:e1.Py_ast.expr_loc (expr env e1) (expr env e2) (mk_var ~loc id') in
      mk_expr ~loc (Esequence (a, gen_updates env lp' cnt))
  | (e,_) :: _ ->
      Loc.errorm ~loc:e.Py_ast.expr_loc "invalid lhs in assignment"

let rec stmt env {Py_ast.stmt_loc = loc; Py_ast.stmt_desc = d } =
  match d with
  | Py_ast.Sblock s ->
    block env ~loc s
  | Py_ast.Seval e ->
    let id = mk_id ~loc "_'" in
    mk_expr ~loc (Elet (id, false, Expr.RKnone, expr env e, mk_unit ~loc))
  | Py_ast.Scall_lemma (f, lt) ->
    let id = mk_id ~loc "_'" in
    let call = Eidapp (Qident f, List.map mk_pure lt) in
    mk_expr ~loc
      (Elet (id, false, Expr.RKnone, mk_expr ~loc call, mk_unit ~loc))
  | Py_ast.Sif (e, s1, s2) ->
    mk_expr ~loc (Eif (expr env e, block env ~loc s1, block env ~loc s2))
  | Py_ast.Sreturn e ->
    mk_expr ~loc (Eraise (Qident (mk_id ~loc Ptree_helpers.return_id), Some (expr env e)))
  | Py_ast.Sassign (lhs, e) ->
     (*
       r1,...rn = e1,...en ==>
       match e1,... en with r1',... rn' -> r1:=r1'; ... rn := rn'
      *)
     let e = expr env e in
     let p = build_pat2 lhs e in
     let lp = flatten_updates lhs p in
     let u = gen_updates env lp (mk_unit ~loc) in
     mk_expr ~loc (Ematch (e, [p, u], []))

  | Py_ast.Sset (e1, e2, e3) ->
    array_set ~loc (expr env e1) (expr env e2) (expr env e3)
  | Py_ast.Sassert (k, t) ->
    mk_expr ~loc (Eassert (k, t))
  | Py_ast.Swhile (e, inv, var, s) ->
    let id_b = mk_id ~loc Ptree_helpers.break_id in
    let id_c = mk_id ~loc Ptree_helpers.continue_id in
    let body = block env ~loc s in
    let body = mk_expr ~loc (Eoptexn (id_c, Ity.MaskVisible, body)) in
    let loop = mk_expr ~loc (Ewhile (expr env e, inv, var, body)) in
    mk_expr ~loc (Eoptexn (id_b, Ity.MaskVisible, loop))
  | Py_ast.Sbreak ->
    mk_expr ~loc (Eraise (Qident (mk_id ~loc Ptree_helpers.break_id), None))
  | Py_ast.Scontinue ->
    mk_expr ~loc (Eraise (Qident (mk_id ~loc Ptree_helpers.continue_id), None))
  | Py_ast.Slabel _ ->
    mk_unit ~loc (* ignore lonely marks *)
  | Py_ast.Spass (ty, sp) ->
     mk_expr ~loc
       (Eany ([], Expr.RKnone, ty, mk_pat ~loc Pwild, Ity.MaskVisible, sp))
    (* make a special case for
         for id in range(e1, [e2, e3]) *)
  | Py_ast.Sfor (id, {Py_ast.expr_desc=Ecall ({id_str="range"}, exps)},
                 inv, body)
    when (List.length exps = 3 && (let c = is_const exps in c = -1 || c = 1)) ->
    let lb, ub, direction = mk_for_params exps loc env in
    let body = block ~loc (add_var env id) body in
    let body =
      mk_expr ~loc (Eoptexn (mk_id ~loc Ptree_helpers.continue_id, Ity.MaskVisible, body)) in
    let body = mk_expr ~loc (Elet (set_ref id, false, Expr.RKnone,
                                   mk_ref ~loc (mk_var ~loc id), body)) in
    let loop = mk_expr ~loc (Efor (id, lb, direction, ub, inv, body)) in
    mk_expr ~loc (Eoptexn (mk_id ~loc Ptree_helpers.break_id, Ity.MaskVisible, loop))

  | Py_ast.Sfor (id, {Py_ast.expr_desc=Ecall ({id_str="range"}, exps)},
                 inv, body)
    when (List.length exps < 3) ->
    let lb, ub, direction = mk_for_params exps loc env in
    let body = block ~loc (add_var env id) body in
    let body =
      mk_expr ~loc (Eoptexn (mk_id ~loc Ptree_helpers.continue_id, Ity.MaskVisible, body)) in
    let body = mk_expr ~loc (Elet (set_ref id, false, Expr.RKnone,
                                   mk_ref ~loc (mk_var ~loc id), body)) in
    let loop = mk_expr ~loc (Efor (id, lb, direction, ub, inv, body)) in
    mk_expr ~loc (Eoptexn (mk_id ~loc Ptree_helpers.break_id, Ity.MaskVisible, loop))
  (* otherwise, translate
       for id in e:
         #@ invariant inv
         body
    to
       let l = e in
       for i'index = 0 to len(l)-1 do
         invariant { I }
         let id = ref l[i'index] in
         body
       done
    *)
  | Py_ast.Sfor (id, e, inv, body) ->
    let e = expr env e in
    let i, l = for_vars ~loc id in
    let lb = constant ~loc 0 in
    let lenl = mk_expr ~loc (Eidapp (len ~loc, [mk_var ~loc l])) in
    let ub = mk_expr ~loc (Eidapp (infix ~loc "-", [lenl; constant ~loc 1])) in
    let li = mk_expr ~loc (Eidapp (get_op ~loc, [mk_var ~loc l; mk_var ~loc i])) in
    let body = block ~loc (add_var env id) body in
    let body = mk_expr ~loc (Eoptexn (mk_id ~loc Ptree_helpers.continue_id, Ity.MaskVisible, body)) in
    let body = mk_expr ~loc (Elet (set_ref id, false, Expr.RKnone,
                                   mk_ref ~loc li, body)) in
    let loop = mk_expr ~loc (Efor (i, lb, Expr.To, ub, inv, body)) in
    let loop = mk_expr ~loc (Elet (l, false, Expr.RKnone, e, loop)) in
    mk_expr ~loc (Eoptexn (mk_id ~loc Ptree_helpers.break_id, Ity.MaskVisible, loop))

and block env ~loc = function
  | [] ->
    mk_unit ~loc
  | Dstmt { stmt_loc = loc; stmt_desc = Slabel id } :: sl ->
    mk_expr ~loc (Elabel (id, block env ~loc sl))
  | Dstmt { Py_ast.stmt_loc=loc; stmt_desc = Py_ast.Sassign (lhs, e) } :: sl ->
     let ids = new_vars env lhs in
     let env' =  List.fold_left add_var env ids in
     let e = expr env e in
     let p = build_pat2 lhs e in
     let lp = flatten_updates lhs p in
     let u = gen_updates env lp (block env' ~loc sl) in
     mk_expr ~loc (Ematch (e, [p, u], []))
  | Dstmt ({ Py_ast.stmt_loc = loc } as s) :: sl ->
    let s = stmt env s in
    if sl = [] then s else mk_expr ~loc (Esequence (s, block env ~loc sl))
  | Ddef (id, idl, ty, sp, bl, fct) :: sl ->
    (* f(x1,...,xn): body ==>
      let f x1 ... xn =
        let x1 = ref x1 in ... let xn = ref xn in
        try body with Return x -> x *)
    let param (id, ty) = id.id_loc, Some id, false, ty in
    let params = if idl = [] then no_params ~loc else List.map param idl in
    let p = mk_pat ~loc Pwild in
    let is_rec = block_has_call id bl in
    let s = block env ~loc sl in
    (match bl with
       | [Py_ast.Dstmt {stmt_desc=Py_ast.Sreturn e}] when fct ->
           let env' = List.fold_left add_param empty_env idl in
           let e = expr env' e in
           let d =
             if is_rec then
               Drec ([id,false,Expr.RKfunc,params,ty,p,Ity.MaskVisible,sp,e])
             else
               let e = Efun (params, ty, p, Ity.MaskVisible, sp, e) in
               Dlet (id, false, Expr.RKfunc, mk_expr ~loc e) in
           Typing.add_decl id.id_loc d;
           s
       | _ ->
           let env' = List.fold_left add_param env idl in
           let body = block env' ~loc:id.id_loc bl in
           let body =
             let loc = id.id_loc in
             let id = mk_id ~loc Ptree_helpers.return_id in
             { body with expr_desc = Eoptexn (id, Ity.MaskVisible, body) } in
           let local bl (id, _) =
             let loc = id.id_loc in
             let ref = mk_ref ~loc (mk_var ~loc id) in
             mk_expr ~loc (Elet (set_ref id, false, Expr.RKnone, ref, bl)) in
           let body = List.fold_left local body idl in
           let kind = if fct then Expr.RKlocal else Expr.RKnone in
           let e =
             if is_rec then
               Erec ([id, false, kind, params, ty, p, Ity.MaskVisible, sp, body], s)
             else
               let e = Efun (params, ty, p, Ity.MaskVisible, sp, body) in
               Elet (id, false, kind, mk_expr ~loc e, s)
           in
           mk_expr ~loc e)
  | (Py_ast.Dimport _ | Py_ast.Dlogic _) :: sl ->
    block env ~loc sl
  | Py_ast.Dconst (id, e) :: sl ->
    let e = expr env e in
    let d = Dlet (id, false, Expr.RKfunc, e) in
    Typing.add_decl id.id_loc d;
    let e = Elet (id, false, Expr.RKnone, e,
                  block ~loc (add_var env id) sl) in
    mk_expr ~loc e
  | Py_ast.Dprop (pk, id, t) :: sl ->
    Typing.add_decl id.id_loc (Dprop (pk, id, t));
    block env ~loc sl

let logic_param (id, ty) =
  id.id_loc, Some id, false, ty

let logic = function
  | Py_ast.Dlogic (id, idl, ty, None, def) ->
    let d = { ld_loc = id.id_loc;
              ld_ident = id;
              ld_params = List.map logic_param idl;
              ld_type = ty;
              ld_def = def } in
    Typing.add_decl id.id_loc (Dlogic [d])
  | Py_ast.Dlogic (id, idl, Some ty, Some var, Some def) ->
     let loc = id.id_loc in
     let p = mk_pat ~loc (Pvar id) in
     let s = { Ptree_helpers.empty_spec with sp_variant = [var,None] } in
     let e = mk_expr ~loc (Epure def) in
     let pl = List.map (fun (id,ty) -> loc,Some id,false,Some ty) idl in
     let dr =
       Drec ([id, true, Expr.RKfunc, pl, Some ty, p, Ity.MaskVisible, s, e]) in
     Typing.add_decl id.id_loc dr
  | Py_ast.Dlogic (id, idl, None, _, def) ->
    let d = { ld_loc = id.id_loc;
              ld_ident = id;
              ld_params = List.map logic_param idl;
              ld_type = None;
              ld_def = def } in
    Typing.add_decl id.id_loc (Dlogic [d])
  | _ -> ()

let translate ~loc dl =
  List.iter logic dl;
  let bl = block empty_env ~loc dl in
  let p = mk_pat ~loc Pwild in
  let fd = Efun (no_params ~loc, None, p, Ity.MaskVisible, empty_spec, bl) in
  let main = Dlet (mk_id ~loc "main", false, Expr.RKnone, mk_expr ~loc fd) in
  Typing.add_decl loc main

let read_channel env path file c =
  let f : Py_ast.file = Py_lexer.parse file c in
  Debug.dprintf debug "%s parsed successfully.@." file;
  let loc = Loc.user_position file 0 0 0 0 in
  let file = Filename.basename file in
  let file = Filename.chop_extension file in
  let name = Strings.capitalize file in
  Debug.dprintf debug "building module %s.@." name;
  Typing.open_file env path;
  Typing.open_module (mk_id ~loc name);
  let use_import (f, m) =
    let m = mk_id ~loc m in
    let qid = Qdot (Qident (mk_id ~loc f), m) in
    let decl = Ptree.Duseimport(loc,false,[(qid,None)]) in
    Typing.add_decl loc decl in
  List.iter use_import
    ["int", "Int"; "ref", "Refint"; "python", "Python"];
  translate ~loc f;
  Typing.close_module loc;
  let mm = Typing.close_file () in
  if path = [] && Debug.test_flag debug then begin
    let add_m _ m modm = Ident.Mid.add m.mod_theory.Theory.th_name m modm in
    let print_m _ m = Pmodule.print_module Format.err_formatter m in
    Ident.Mid.iter print_m (Mstr.fold add_m mm Ident.Mid.empty)
  end;
  mm

let () =
  Env.register_format mlw_language "python" ["py"] read_channel
    ~desc:"mini-Python format"

(* Python pretty-printer, to print tasks with a little bit
   of Python syntax *)

open Term
open Format
open Pretty

(* python print_binop *)
let print_binop ~asym fmt = function
  | Tand when asym -> pp_print_string fmt "&&"
  | Tor when asym  -> pp_print_string fmt "||"
  | Tand           -> pp_print_string fmt "and"
  | Tor            -> pp_print_string fmt "or"
  | Timplies       -> pp_print_string fmt "->"
  | Tiff           -> pp_print_string fmt "<->"

(* Register the transformations functions *)
let rec python_ext_printer print_any fmt a =
  match a with
  | Pp_term (t, pri) ->
      begin match t.t_node with
        | Tapp (ls, [t1; t2]) when ls_equal ls ps_equ ->
            (* == *)
            fprintf fmt (protect_on (pri > 0) "@[%a == %a@]")
              (python_ext_printer print_any) (Pp_term (t1, 0))
              (python_ext_printer print_any) (Pp_term (t2, 0))
        | Tnot {t_node = Tapp (ls, [t1; t2]) } when ls_equal ls ps_equ ->
            (* != *)
            fprintf fmt (protect_on (pri > 0) "@[%a != %a@]")
              (python_ext_printer print_any) (Pp_term (t1, 0))
              (python_ext_printer print_any) (Pp_term (t2, 0))
        | Tbinop (b, f1, f2) ->
            (* and, or *)
            let asym = Ident.Sattr.mem asym_split f1.t_attrs in
            let p = prio_binop b in
            fprintf fmt (protect_on (pri > p) "@[%a %a@ %a@]")
              (python_ext_printer print_any) (Pp_term (f1, (p + 1)))
              (print_binop ~asym) b
              (python_ext_printer print_any) (Pp_term (f2, p))
        | _ -> print_any fmt a
      end
  | _ -> print_any fmt a

let () = Itp_server.add_registered_lang "python" (fun _ -> python_ext_printer)

let () = Args_wrapper.set_argument_parsing_functions "python"
    ~parse_term:(fun _ lb -> Py_lexer.parse_term lb)
    ~parse_term_list:(fun _ lb -> Py_lexer.parse_term_list lb)
    ~parse_list_ident:(fun lb -> Py_lexer.parse_list_ident lb)
    (* TODO for qualids, add a similar funciton *)
    ~parse_qualid:(fun lb -> Lexer.parse_qualid lb)
    ~parse_list_qualid:(fun lb -> Lexer.parse_list_qualid lb)
