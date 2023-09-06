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

(*
why3 prove --format=coma -
why3 prove file.coma


p [z] {x} (h) =
  { 1=2 } any
  / f {x} = g <(int,int)> {42} (h) {42}
  / g < 'a > = any
  / h (foo) = (fun {x} -> any) < int >
  / h (foo [y z] {x} (bar )) = any

q [z] =
  any
*)

%{
open Why3
open Ptree
open Coma_syntax

let floc s e = Loc.extract (s,e)

let mk_pexpr d b e = { pexpr_desc = d; pexpr_loc = floc b e }
let mk_defn d b e = { pdefn_desc = d; pdefn_loc = floc b e }

%}

%token BANG QUESTION SLASH

%start <Coma_syntax.pdefn list> top_level
%start <unit> dummy

%%

top_level:
| defn* EOF   { $1 }

defn:
| id=lident w=prewrites p=coma_params EQUAL e=coma_expr
  { let d = { pdefn_name = id; pdefn_writes = w;
              pdefn_params = p; pdefn_body = e } in
    mk_defn d $startpos $endpos }

local_defn:
| id=lident w=prewrites p=coma_params EQUAL e=coma_expr1
  { let d = { pdefn_name = id; pdefn_writes = w;
              pdefn_params = p; pdefn_body = e } in
    mk_defn d $startpos $endpos }

coma_expr:
| e=coma_expr1 dl=loption(coma_slash)
  { (* FIXME: parse REC keyword? *)
    let e = if dl=[] then e.pexpr_desc else PEdef (e, false, dl) in
    mk_pexpr e $startpos $endpos }

coma_slash:
| SLASH dl=separated_nonempty_list(SLASH, local_defn)
  { dl }

coma_expr1:
| d = coma_desc1
  { mk_pexpr d $startpos $endpos }

coma_desc1:
| LEFTBRC t=term RIGHTBRC e=coma_expr1
  { PEcut (t, e) }
| BANG e=coma_expr1
  { PEbox e }
| QUESTION e=coma_expr1
  { PEwox e }
| e=coma_expr2 al=coma_arg*
  { let app e a = mk_pexpr (PEapp (e, a)) $startpos $endpos in
    let e = List.fold_left app e al in
    e.pexpr_desc }

coma_expr2:
| d = coma_desc2
  { mk_pexpr d $startpos $endpos }

coma_desc2:
| x=lident
  { PEsym x }
| ANY
  { PEany }
| LEFTPAR FUN p=coma_params ARROW e=coma_expr RIGHTPAR
  { PElam (p, e) }
| LEFTPAR e=coma_expr RIGHTPAR
  { e.pexpr_desc }

prewrites:
| w = loption(prewrites_)
  { w }

prewrites_:
| LEFTSQ w=lident* RIGHTSQ
  { w }

coma_arg:
| LT ty=ty GT
  { At ty }
| LEFTBRC t=term RIGHTBRC
  { Av t }
| AMP x=lident
  { Ar x }
| LEFTPAR e=coma_expr RIGHTPAR
  { Ac e }

coma_params:
| tp=loption(tparam) pl=coma_param*
  { tp @ pl }

tparam:
| LT l=coma_tvar* GT
  { l }
coma_tvar:
| x=QUOTE_LIDENT
  { PPt (mk_id x $startpos $endpos) }

coma_param:
| LEFTBRC id=lident RIGHTBRC
  { PPv id }
| LEFTPAR id=lident w=prewrites p=coma_params RIGHTPAR
  { PPc (id, w, p) }

/* silent Menhir's errors about unreachable non terminal symbols */

dummy:
| module_head_parsing_only scope_head_parsing_only dummy_decl* EOF
    { }

dummy_decl:
| meta_decl {}
| use_clone_parsing_only {}
| prog_decl {}
| pure_decl {}
