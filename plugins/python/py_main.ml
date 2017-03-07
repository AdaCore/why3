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

open Why3
open Mlw_module
open Py_ast
open Ptree
open Stdlib

let debug = Debug.register_flag "python"
  ~desc:"mini-python plugin debug flag"
let () = Debug.set_flag Dterm.debug_ignore_unused_var

let mk_id ~loc name =
  { id_str = name; id_lab = []; id_loc = loc }

let infix  ~loc s = Qident (mk_id ~loc ("infix "  ^ s))
let prefix ~loc s = Qident (mk_id ~loc ("prefix " ^ s))
let mixfix ~loc s = Qident (mk_id ~loc ("mixfix " ^ s))

let mk_expr ~loc d =
  { expr_desc = d; expr_loc = loc }
let mk_term ~loc d =
  { term_desc = d; term_loc = loc }
let mk_pat ~loc d =
  { pat_desc = d; pat_loc = loc }
let mk_unit ~loc =
  mk_expr ~loc (Etuple [])
let mk_var ~loc id =
  mk_expr ~loc (Eident (Qident id))
let mk_tvar ~loc id =
  mk_term ~loc (Tident (Qident id))
let mk_ref ~loc e =
  mk_expr ~loc (Eidapp (Qident (mk_id ~loc "ref"), [e]))
let deref_id ~loc id =
  mk_expr ~loc (Eidapp (prefix ~loc "!", [mk_expr ~loc (Eident (Qident id))]))
let array_set ~loc a i v =
  mk_expr ~loc (Eidapp (mixfix ~loc "[]<-", [a; i; v]))
let constant ~loc s =
  mk_expr ~loc (Econst (Number.ConstInt (Number.int_const_dec s)))
let len ~loc =
  Qident (mk_id ~loc "len")
let break ~loc =
  Qident (mk_id ~loc "Break")
let break_handler ~loc =
  [break ~loc, None, mk_unit ~loc]
let return ~loc =
  Qident (mk_id ~loc "Return")
let return_handler ~loc =
  let x = mk_id ~loc "x" in
  [return ~loc, Some (mk_pat ~loc (Pvar x)), mk_var ~loc x]
let array_make ~loc n v =
  mk_expr ~loc (Eidapp (Qdot (Qident (mk_id ~loc "Array"), mk_id ~loc "make"),
                        [n; v]))

let empty_spec = {
  sp_pre     = [];
  sp_post    = [];
  sp_xpost   = [];
  sp_reads   = [];
  sp_writes  = [];
  sp_variant = [];
  sp_checkrw = false;
  sp_diverge = false;
}

type env = {
  vars: ident Mstr.t;
  for_index: int;
}

let empty_env =
  { vars = Mstr.empty;
    for_index = 0; }

let add_var env id =
  { env with vars = Mstr.add id.id_str id env.vars }

let for_vars ~loc env =
  let i = env.for_index in
  let env = { env with for_index = i + 1 } in
  let i = string_of_int env.for_index in
  mk_id ~loc ("for index " ^ i ), mk_id ~loc ("for list " ^ i), env

(* dereference all variables from the environment *)
let deref env t =
  let deref _ ({id_loc=loc} as id) t =
    let tid = mk_term ~loc (Tident (Qident id)) in
    let tid = mk_term ~loc (Tidapp (prefix ~loc "!", [tid])) in
    mk_term ~loc:t.term_loc (Tlet (id, tid, t)) in
  Mstr.fold deref env.vars t

let loop_annotation env a =
  { loop_invariant = List.map (deref env) a.loop_invariant;
    loop_variant   = List.map (fun (t, o) -> deref env t, o) a.loop_variant }

let add_loop_invariant i a =
  { a with loop_invariant = i :: a.loop_invariant }

let rec has_break s = match s.stmt_desc with
  | Sbreak -> true
  | Sreturn _ | Sassign _ | Slabel _
  | Seval _ | Sset _ | Sassert _ | Swhile _ -> false
  | Sif (_, bl1, bl2) -> has_breakl bl1 || has_breakl bl2
  | Sfor (_, _, _, bl) -> has_breakl bl
and has_breakl bl = List.exists has_break bl

let rec has_return s = match s.stmt_desc with
  | Sreturn _ -> true
  | Sbreak | Sassign _ | Slabel _
  | Seval _ | Sset _ | Sassert _ -> false
  | Sif (_, bl1, bl2) -> has_returnl bl1 || has_returnl bl2
  | Swhile (_, _, bl) | Sfor (_, _, _, bl) -> has_returnl bl
and has_returnl bl = List.exists has_return bl

let rec expr env {Py_ast.expr_loc = loc; Py_ast.expr_desc = d } = match d with
  | Py_ast.Enone ->
    mk_unit ~loc
  | Py_ast.Ebool b ->
    mk_expr ~loc (if b then Etrue else Efalse)
  | Py_ast.Eint s ->
    constant ~loc s
  | Py_ast.Estring _s ->
    mk_unit ~loc (*FIXME*)
  | Py_ast.Eident id ->
    if not (Mstr.mem id.id_str env.vars) then
      Loc.errorm ~loc "unbound variable %s" id.id_str;
    deref_id ~loc id
  | Py_ast.Ebinop (op, e1, e2) ->
    let e1 = expr env e1 in
    let e2 = expr env e2 in
    mk_expr ~loc (match op with
      | Py_ast.Band -> Elazy (e1, LazyAnd, e2)
      | Py_ast.Bor  -> Elazy (e1, LazyOr,  e2)
      | Py_ast.Badd -> Eidapp (infix ~loc "+", [e1; e2])
      | Py_ast.Bsub -> Eidapp (infix ~loc "-", [e1; e2])
      | Py_ast.Bmul -> Eidapp (infix ~loc "*", [e1; e2])
      | Py_ast.Bdiv -> Eidapp (Qident (mk_id ~loc "div"), [e1; e2])
      | Py_ast.Bmod -> Eidapp (Qident (mk_id ~loc "mod"), [e1; e2])
      | Py_ast.Beq  -> Eidapp (infix ~loc "=", [e1; e2])
      | Py_ast.Bneq -> Eidapp (infix ~loc "<>", [e1; e2])
      | Py_ast.Blt  -> Eidapp (infix ~loc "<", [e1; e2])
      | Py_ast.Ble  -> Eidapp (infix ~loc "<=", [e1; e2])
      | Py_ast.Bgt  -> Eidapp (infix ~loc ">", [e1; e2])
      | Py_ast.Bge  -> Eidapp (infix ~loc ">=", [e1; e2])
    )
  | Py_ast.Eunop (Py_ast.Uneg, e) ->
    mk_expr ~loc (Eidapp (prefix ~loc "-", [expr env e]))
  | Py_ast.Eunop (Py_ast.Unot, e) ->
    mk_expr ~loc (Eidapp (Qident (mk_id ~loc "not"), [expr env e]))
  | Py_ast.Ecall ({id_str="print"}, el) ->
    let eval res e =
      mk_expr ~loc (Elet (mk_id ~loc "_", Gnone, expr env e, res)) in
    List.fold_left eval (mk_unit ~loc) el
  | Py_ast.Ecall (id, el) ->
    mk_expr ~loc (Eidapp (Qident id, List.map (expr env) el))
  | Py_ast.Emake (e1, e2) -> (* [e1]*e2 *)
    array_make ~loc (expr env e2) (expr env e1)
  | Py_ast.Elist [] ->
    array_make ~loc (constant ~loc "0") (constant ~loc "0")
  | Py_ast.Elist el ->
    let n = List.length el in
    let n = constant ~loc (string_of_int n) in
    let id = mk_id ~loc "new array" in
    mk_expr ~loc (Elet (id, Gnone, array_make ~loc n (constant ~loc "0"),
    let i = ref (-1) in
    let init seq e =
      incr i; let i = constant ~loc (string_of_int !i) in
      let assign = array_set ~loc (mk_var ~loc id) i (expr env e) in
      mk_expr ~loc (Esequence (assign, seq)) in
    List.fold_left init (mk_var ~loc id) el))
  | Py_ast.Eget (e1, e2) ->
    mk_expr ~loc (Eidapp (mixfix ~loc "[]", [expr env e1; expr env e2]))

let rec stmt env ({Py_ast.stmt_loc = loc; Py_ast.stmt_desc = d } as s) =
  match d with
  | Py_ast.Seval e ->
    expr env e
  | Py_ast.Sif (e, s1, s2) ->
    mk_expr ~loc (Eif (expr env e, block env ~loc s1, block env ~loc s2))
  | Py_ast.Sreturn e ->
    mk_expr ~loc (Eraise (return ~loc, Some (expr env e)))
  | Py_ast.Sassign (id, e) ->
    let e = expr env e in
    if Mstr.mem id.id_str env.vars then
      let x = let loc = id.id_loc in mk_expr ~loc (Eident (Qident id)) in
      mk_expr ~loc (Einfix (x, mk_id ~loc "infix :=", e))
    else
      block env ~loc [s]
  | Py_ast.Sset (e1, e2, e3) ->
    array_set ~loc (expr env e1) (expr env e2) (expr env e3)
  | Py_ast.Sassert (k, t) ->
    mk_expr ~loc (Eassert (k, deref env t))
  | Py_ast.Swhile (e, ann, s) ->
    let loop = mk_expr ~loc
      (Ewhile (expr env e, loop_annotation env ann, block env ~loc s)) in
    if has_breakl s then mk_expr ~loc (Etry (loop, break_handler ~loc))
    else loop
  | Py_ast.Sbreak ->
    mk_expr ~loc (Eraise (break ~loc, None))
  | Py_ast.Slabel _ ->
    mk_unit ~loc (* ignore lonely marks *)
  (* make a special case for
       for id in range(e1, e2):
    *)
  | Py_ast.Sfor (id, {expr_desc=Ecall ({id_str="range"}, [e1;e2])},
                 inv, body) ->
    let inv = List.map (deref env) inv in
    mk_expr ~loc (Efor (id, expr env e1, To, expr env e2, inv,
    mk_expr ~loc (Elet (id, Gnone, mk_ref ~loc (mk_var ~loc id),
    let env = add_var env id in
    block ~loc env body))))
  (* otherwise, translate
       for id in e:
         #@ invariant inv
         body
    to
       let l = e in
       for i = 0 to len(l)-1 do
         invariant { let id = l[i] in I }
         let id = ref l[i] in
         body
       done
    *)
  | Py_ast.Sfor (id, e, inv, body) ->
    let i, l, env = for_vars ~loc env in
    let e = expr env e in
    mk_expr ~loc (Elet (l, Gnone, e, (* evaluate e only once *)
    let lb = constant ~loc "0" in
    let lenl = mk_expr ~loc (Eidapp (len ~loc, [mk_var ~loc l])) in
    let ub = mk_expr ~loc (Eidapp (infix ~loc "-", [lenl;constant ~loc "1"])) in
    let invariant inv =
      let loc = inv.term_loc in
      let li = mk_term ~loc
        (Tidapp (mixfix ~loc "[]", [mk_tvar ~loc l; mk_tvar ~loc i])) in
      mk_term ~loc (Tlet (id, li, deref env inv)) in
    mk_expr ~loc (Efor (i, lb, To, ub, List.map invariant inv,
    let li = mk_expr ~loc
      (Eidapp (mixfix ~loc "[]", [mk_var ~loc l; mk_var ~loc i])) in
    mk_expr ~loc (Elet (id, Gnone, mk_ref ~loc li,
    let env = add_var env id in
    block ~loc env body
    ))))))

and block env ~loc = function
  | [] ->
    mk_unit ~loc
  | { stmt_loc = loc; stmt_desc = Slabel id } :: sl ->
    mk_expr ~loc (Emark (id, block env ~loc sl))
  | { Py_ast.stmt_loc = loc; stmt_desc = Py_ast.Sassign (id, e) } :: sl
    when not (Mstr.mem id.id_str env.vars) ->
    let e = expr env e in (* check e *before* adding id to environment *)
    let env = add_var env id in
    mk_expr ~loc (Elet (id, Gnone, mk_ref ~loc e, block env ~loc sl))
  | { Py_ast.stmt_loc = loc } as s :: sl ->
    let s = stmt env s in
    if sl = [] then s else mk_expr ~loc (Esequence (s, block env ~loc sl))

let post env (loc, l) =
  loc, List.map (fun (pat, t) -> pat, deref env t) l

let spec env sp =
  assert (sp.sp_xpost = [] && sp.sp_reads = [] && sp.sp_writes = []
    && sp.sp_variant = []);
  { sp with
    sp_pre = List.map (deref env) sp.sp_pre;
    sp_post = List.map (post env) sp.sp_post }

let no_params ~loc = [loc, None, false, Some (PTtuple [])]

(* f(x1,...,xn): body

   let f x1 ... xn =
     let x1 = ref x1 in ... let xn = ref xn in
     try body with Return x -> x *)
let def inc (id, idl, sp, bl) =
  let loc = id.id_loc in
  let env = empty_env in
  let env = List.fold_left add_var env idl in
  let body = block env ~loc bl in
  let body = if has_returnl bl then
      mk_expr ~loc (Etry (body, return_handler ~loc)) else body in
  let local bl id =
    let loc = id.id_loc in
    mk_expr ~loc (Elet (id, Gnone, mk_ref ~loc (mk_var ~loc id), bl)) in
  let body = List.fold_left local body idl in
  let param id = id.id_loc, Some id, false, None in
  let params = if idl = [] then no_params ~loc else List.map param idl in
  let fd = (params, None, body, sp) in
  let d = Dfun (id, Gnone, fd) in
  inc.new_pdecl id.id_loc d

let translate ~loc inc (dl, s) =
  List.iter (def inc) dl;
  let fd = (no_params ~loc, None, block empty_env ~loc s, empty_spec) in
  let main = Dfun (mk_id ~loc "main", Gnone, fd) in
  inc.new_pdecl loc main

let read_channel env path file c =
  let lb = Lexing.from_channel c in
  Loc.set_file file lb;
  let loc = Loc.user_position file 0 0 0 in
  let f = Loc.with_location (Py_parser.file Py_lexer.next_token) lb in
  Debug.dprintf debug "%s parsed successfully.@." file;
  let file = Filename.basename file in
  let file = Filename.chop_extension file in
  let name = String.capitalize file in
  Debug.dprintf debug "building module %s.@." name;
  let inc = Mlw_typing.open_file env path in
  inc.open_module (mk_id ~loc name);
  let use_import (f, m) =
    let q = Qdot (Qident (mk_id ~loc f), mk_id ~loc m) in
    let use = {use_theory = q; use_import = Some (true, m) }, None in
    inc.use_clone loc use in
  List.iter use_import
    ["int", "Int"; "ref", "Refint"; "python", "Python"];
  translate ~loc inc f;
  inc.close_module ();
  let mm, _ as res = Mlw_typing.close_file () in
  if path = [] && Debug.test_flag debug then begin
    let add_m _ m modm = Ident.Mid.add m.mod_theory.Theory.th_name m modm in
    let modm = Mstr.fold add_m mm Ident.Mid.empty in
    let print_m _ m = Format.eprintf
      "@[<hov 2>module %a@\n%a@]@\nend@\n@." Pretty.print_th m.mod_theory
      (Pp.print_list Pp.newline2 Mlw_pretty.print_pdecl) m.mod_decls in
    Ident.Mid.iter print_m modm
  end;
  res

let () =
  Env.register_format mlw_language "python" ["py"] read_channel
    ~desc:"mini-Python format"
