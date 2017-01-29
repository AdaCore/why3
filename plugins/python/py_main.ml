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
open Ptree
open Stdlib

let debug = Debug.register_flag "mini-python"
  ~desc:"mini-python plugin debug flag"

let mk_id ?(loc=Loc.dummy_position) name =
  { id_str = name; id_lab = []; id_loc = loc }

let mk_expr ?(loc=Loc.dummy_position) d =
  { expr_desc = d; expr_loc = loc }
let mk_unit ~loc =
  mk_expr ~loc (Etuple [])

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
  vars: unit Hstr.t;
}

let infix  ~loc s = Qident (mk_id ~loc ("infix "  ^ s))
let prefix ~loc s = Qident (mk_id ~loc ("prefix " ^ s))

let rec expr env {Py_ast.expr_loc = loc; Py_ast.expr_desc = d } = match d with
  | Py_ast.Enone ->
    mk_unit ~loc
  | Py_ast.Ebool b ->
    mk_expr ~loc (if b then Etrue else Efalse)
  | Py_ast.Eint s ->
    mk_expr ~loc (Econst (Number.ConstInt (Number.int_const_dec s)))
  | Py_ast.Estring _s ->
    assert false (*TODO*)
  | Py_ast.Eident id ->
    if not (Hstr.mem env.vars id.id_str) then
      Loc.errorm ~loc "unbound variable %s" id.id_str;
    mk_expr ~loc (Eidapp (prefix ~loc "!", [mk_expr ~loc (Eident (Qident id))]))
  | Py_ast.Ebinop (op, e1, e2) ->
    let e1 = expr env e1 in
    let e2 = expr env e2 in
    mk_expr ~loc (match op with
      | Py_ast.Band -> Elazy (e1, LazyAnd, e2)
      | Py_ast.Bor  -> Elazy (e1, LazyOr,  e2)
      | Py_ast.Badd -> Eidapp (infix ~loc "+", [e1; e2])
      | Py_ast.Bsub -> Eidapp (infix ~loc "-", [e1; e2])
      | Py_ast.Bmul -> Eidapp (infix ~loc "*", [e1; e2])
      | Py_ast.Bdiv -> assert false (*TODO*)
      | Py_ast.Bmod -> assert false (*TODO*)
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
  | Py_ast.Ecall (id, el) ->
    assert false (*TODO*)
  | Py_ast.Elist el ->
    assert false
  | Py_ast.Eget (e1, e2) ->
    assert false (*TODO*)

let rec stmt env ({Py_ast.stmt_loc = loc; Py_ast.stmt_desc = d } as s) =
  match d with
  | Py_ast.Sblock sl ->
    block env loc sl
  | Py_ast.Seval e ->
    expr env e
  | Py_ast.Sprint e ->
    mk_expr ~loc (Elet (mk_id ~loc "_", Gnone, expr env e, mk_unit ~loc))
  | Py_ast.Sif (e, s1, s2) ->
    mk_expr ~loc (Eif (expr env e, stmt env s1, stmt env s2))
  | Py_ast.Swhile (e, ann, s) ->
    mk_expr ~loc (Ewhile (expr env e, ann, stmt env s))
  | Py_ast.Sreturn e ->
    assert false (*TODO*)
  | Py_ast.Sassign (id, e) ->
    let e = expr env e in
    if Hstr.mem env.vars id.id_str then
      let x = let loc = id.id_loc in mk_expr ~loc (Eident (Qident id)) in
      mk_expr ~loc (Einfix (x, mk_id ~loc "infix :=", e))
    else
      block env loc [s]
  | Py_ast.Sfor (id, e, s) ->
    assert false (*TODO*)
  | Py_ast.Sset (e1, e2, e3) ->
    assert false (*TODO*)

and block env loc = function
  | [] ->
    mk_unit ~loc
  | { Py_ast.stmt_loc = loc; stmt_desc = Py_ast.Sassign (id, e) } :: sl
    when not (Hstr.mem env.vars id.id_str) ->
    let e = expr env e in (* check e *before* adding id to environment *)
    Hstr.add env.vars id.id_str ();
    let e1 = mk_expr ~loc (Eidapp (Qident (mk_id ~loc "ref"), [e])) in
    mk_expr ~loc (Elet (id, Gnone, e1, block env loc sl))
  | { Py_ast.stmt_loc = loc } as s :: sl ->
    mk_expr ~loc (Esequence (stmt env s, block env loc sl))

let translate inc (_dl, s) =
  let params = [Loc.dummy_position, None, false, Some (PTtuple [])] in
  let env = { vars = Hstr.create 32 } in
  let fd = (params, None, stmt env s, empty_spec) in
  let main = Dfun (mk_id "main", Gnone, fd) in
  inc.new_pdecl Loc.dummy_position main

let read_channel env path file c =
  let lb = Lexing.from_channel c in
  Loc.set_file file lb;
  let f = Loc.with_location (Py_parser.file Py_lexer.next_token) lb in
  Debug.dprintf debug "%s parsed successfully.@." file;
  let file = Filename.basename file in
  let file = Filename.chop_extension file in
  let name = String.capitalize_ascii file in
  Debug.dprintf debug "building module %s.@." name;
  let inc = Mlw_typing.open_file env path in
  inc.open_module (mk_id name);
  let use_import (f, m) =
    let q = Qdot (Qident (mk_id f), mk_id m) in
    let use = {use_theory = q; use_import = Some (true, m) }, None in
    inc.use_clone  Loc.dummy_position use in
  List.iter use_import ["int", "Int"; "ref", "Ref"; "seq", "Seq"];
  translate inc f;
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
