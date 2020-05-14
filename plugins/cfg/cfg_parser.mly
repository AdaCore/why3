(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

%{

  open Why3
  open Cfg_ast

  let floc s e = Loc.extract (s,e)

(*
  let mk_cfgexpr d s e = { cfg_expr_desc = d; cfg_expr_loc = floc s e }
*)
  let mk_cfginstr d s e = { cfg_instr_desc = d; cfg_instr_loc = floc s e }

%}

(* extra tokens *)
%token CFG GOTO VAR

%start cfgfile
%type <Cfg_ast.cfg_file> cfgfile
%type <Cfg_ast.binder list> vardecl

%%

cfgfile:
  | ml=cfgmodule* EOF { ml }
;

cfgmodule:
  | MODULE id=attrs(uident_nq) dl=cfgdecl* END
    { (id,dl) }

cfgdecl:
  | module_decl_parsing_only { Dmlw_decl $1 }
  | LET CFG dl=with_list1(recdefn) { Dletcfg dl }
;

recdefn:
  | id=attrs(lident_rich) args=binders COLON ret=return_named sp=spec EQUAL
      v=vardecls b=block bl=labelblock*
    { let pat, ty, _mask = ret in
      let spec = apply_return pat sp in
      (id, args, ty, pat, spec, v, b, bl) }
;

vardecls:
  | /* epsilon */ { [] }
  | vardecl vardecls { $1 @ $2 }
;

vardecl:
  | VAR b=binder SEMICOLON { b }
;

labelblock:
  | id = attrs(uident) b=block  { (id,b) }
;

block:
  | LEFTBRC semicolon_list1(instr) RIGHTBRC { $2 }
;

instr:
  | GOTO uident
    { mk_cfginstr (CFGgoto $2) $startpos $endpos }
  | contract_expr
    { mk_cfginstr (CFGexpr $1) $startpos $endpos }
(*
  | lident LARROW cfgexpr
    { mk_cfginstr (CFGassign ($1,$3)) $startpos $endpos }
  | k=assertion_kind id=option(ident_nq) LEFTBRC t=term RIGHTBRC
    { let (n,k)=k in
      mk_cfginstr (CFGassert(k, name_term id n t)) $startpos $endpos }
*)
;

(*
cfgexpr:
  | TRUE
    { mk_cfgexpr CFGtrue $startpos $endpos }
  | FALSE
    { mk_cfgexpr CFGfalse $startpos $endpos }
  | numeral
    { mk_cfgexpr (CFGconst $1) $startpos $endpos }
;
*)
