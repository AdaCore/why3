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

  open Cfg_ast

  let mk_cfgexpr d s e = { cfgexpr_desc = d; cfgexpr_loc = floc s e }

%}

(* extra token *)
%token CFG

%start cfgfile
%type <Cfg_ast.cfg> cfgfile

%%

cfgfile:
| ml=cfgmodule* EOF { ml }
;

cfgmodule:
| MODULE id=attrs(uident_nq) dl=cfgdecl* END
    { (id,dl) }

cfgdecl:
| module_decl_parsing_only { Dmlw_decl $1 }
| LET CFG with_list1(recdefn) { Dletcfg $2 }
;

recdefn:
| id=attrs(lident_rich) args=binders COLON ret=return_named sp=spec EQUAL b=body
    { let pat, ty, _mask = ret in
      let spec = apply_return pat sp in
      (id, args, ret, ty, pat, spec, b) }
;

body:
  | cfgexpr { $1 }
;

cfgexpr:
| TRUE { mk_cfgexpr CFGtrue $startpos $endpos }
;
