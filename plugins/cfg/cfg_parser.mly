(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
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

  let mk_cfginstr d s e = { cfg_instr_desc = d; cfg_instr_loc = floc s e }
  let mk_cfgterm d s e = { cfg_term_desc = d; cfg_term_loc = floc s e }

%}

(* extra tokens *)
%token CFG GOTO VAR SWITCH

%start cfgfile
%type <Cfg_ast.cfg_file> cfgfile
%type <Cfg_ast.cfg_instr list * Cfg_ast.cfg_term> sequence
%type <Cfg_ast.switch_branch list> cases

%%

cfgfile:
  | ml=cfgmodule* EOF { ml }
;

cfgmodule:
  | id=module_head_parsing_only dl=cfgdecl* END
    { (id,dl) }

cfgdecl:
  | scope_head_parsing_only cfgdecl* END
      { let loc,import,qid = $1 in (Cfg_ast.Dscope(loc,import,qid,$2))}
  | IMPORT uqualid { (Dmlw_decl (Dimport $2)) }
  | d = pure_decl | d = prog_decl | d = meta_decl { Dmlw_decl d }
  | use_clone_parsing_only { Dmlw_decl $1 }
  | LET CFG f=recdefn { Dletcfg f }
  | LET REC CFG dl=with_list1(recdefn) { Dreccfg dl }
;

recdefn:
  | cf_name=attrs(lident_rich) cf_args=binders COLON ret=return_named sp=spec EQUAL
      cf_attrs=attr* cf_locals=vardecls cf_block0=block cf_blocks=labelblock*
    { let cf_pat, cf_retty, cf_mask = ret in
      let cf_spec = apply_return cf_pat sp in
      { cf_name; cf_args; cf_retty; cf_pat; cf_mask; cf_spec; cf_attrs;
        cf_locals; cf_block0; cf_blocks } }
;

vardecls:
  | /* epsilon */ { [] }
  | vardecl vardecls { $1 @ $2 }
;

vardecl:
  | g=ghost_opt VAR vl=attrs(lident_nq)* COLON t=ty init=init_opt SEMICOLON
    { List.map (fun id -> (g,id,t, init)) vl }
;

init_opt:
| /* epsilon */ { None }
| EQUAL contract_expr { Some($2) }

ghost_opt:
  | /* epsilon */ { false }
  | GHOST         { true }

labelblock:
  | id = attrs(uident) b=block  { (id,b) }
;

block:
  | LEFTBRC sequence RIGHTBRC { $2 }
;

sequence:
  | terminator { ([], $1) }
  | x=instr SEMICOLON xl = sequence { (x :: fst xl, snd xl) }
;

instr:
  | contract_expr
    { mk_cfginstr (CFGexpr $1) $startpos $endpos }
  | VARIANT LEFTBRC t=term RIGHTBRC
    { mk_cfginstr (CFGinvariant [Variant, None, t, ref None]) $startpos $endpos }
  | INVARIANT nm=option(ident) LEFTBRC t=term RIGHTBRC
    { mk_cfginstr (CFGinvariant [Invariant, nm, t, ref None]) $startpos $endpos }
;

terminator :
  | GOTO uident
    { mk_cfgterm (CFGgoto $2) $startpos $endpos }
  | SWITCH LEFTPAR contract_expr RIGHTPAR cases END
    { mk_cfgterm (CFGswitch ($3,$5)) $startpos $endpos }
  | RETURN contract_expr
    { mk_cfgterm (CFGreturn $2) $startpos $endpos }
  | ABSURD
    { mk_cfgterm CFGabsurd $startpos $endpos }
;

cases:
  | BAR match_case(terminator)
    { [$2] }
  | BAR match_case(terminator) cases
    { $2 :: $3 }
;
