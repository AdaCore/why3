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

%{
open Why3
open Coma_syntax

let mk_pexpr d loc = { pexpr_desc = d; pexpr_loc = Loc.extract loc }
let mk_defn d loc = { pdefn_desc = d; pdefn_loc = Loc.extract loc }

%}

%token BANG QUESTION 

%start <Coma_syntax.pfile> top_level
%start <unit> dummy

%%

top_level:
| uses* defn* EOF
  { $1, $2 }

uses:
| USE EXPORT tqualid
    { Puseexport $3 }
| USE boption(IMPORT) n = tqualid q = option(preceded(AS, uident))
    { let loc = floc $startpos $endpos in
      if $2 && q = None then Loc.warning ~loc ~id:warn_redundant_import
        "the keyword `import' is redundant here and can be omitted";
      (Puseimport ($2, n, q) ) }

defn:
| LET id=lident w=prewrites p=coma_params EQUAL e=coma_prog
  { let d = { pdefn_name = id; pdefn_writes = w;
              pdefn_params = p; pdefn_body = e } in
    mk_defn d $loc }

local_defn(X):
| id=lident w=prewrites p=coma_params X e=coma_expr
  { let d = { pdefn_name = id; pdefn_writes = w;
              pdefn_params = p; pdefn_body = e } in
    mk_defn d $loc }

coma_prog:
| e=coma_expr
  { e }
/* | e=coma_prog DOT dl=separated_nonempty_list(BAR, local_defn(EQUAL))
  { mk_pexpr (PEdef (e, false, dl)) $startpos $endpos }
| e=coma_prog DOT dl=separated_nonempty_list(BAR, local_defn(ARROW))
  { mk_pexpr (PEdef (e, true, dl)) $startpos $endpos }
| e=coma_prog DOT l=separated_nonempty_list(BAR, coma_alloc)
  { mk_pexpr (PEset (e, l)) $startpos $endpos } */
| e=coma_prog AS dl=separated_nonempty_list(BAR, local_defn(EQUAL))
  { mk_pexpr (PEdef (e, false, dl)) $loc }
| e=coma_prog AS dl=separated_nonempty_list(BAR, local_defn(ARROW))
  { mk_pexpr (PEdef (e, true, dl)) $loc }
| e=coma_prog AS l=separated_nonempty_list(BAR, coma_alloc)
  { mk_pexpr (PEset (e, l)) $loc }

coma_alloc:
| AMP id=lident ty=oftyp EQUAL LEFTBRC t=term RIGHTBRC { id, t, ty }

coma_expr:
| d = coma_desc
  { mk_pexpr d $loc }

coma_desc:
| LEFTBRC t=term RIGHTBRC e=coma_expr
  { PEcut (t, e) }
| BANG e=coma_expr
  { PEbox e }
| QUESTION e=coma_expr
  { PEwox e }
| e=coma_expr2 al=coma_arg*
  { let app e a = mk_pexpr (PEapp (e, a)) $loc in
    let e = List.fold_left app e al in
    e.pexpr_desc }

coma_expr2:
| d = coma_desc2
  { mk_pexpr d $loc }

coma_desc2:
| x=lident
  { PEsym x }
| ANY
  { PEany }
| c=coma_closure
  { c.pexpr_desc }
| LEFTPAR e=coma_prog RIGHTPAR
  { e.pexpr_desc }

coma_closure:
| LEFTPAR FUN p=coma_params ARROW e=coma_prog RIGHTPAR
  { let d = PElam (p, e) in
    mk_pexpr d $loc }

prewrites:
| w = loption(prewrites_)
  { w }

prewrites_:
| LEFTSQ w=lident* RIGHTSQ
  { w }

coma_arg:
| LT ty=ty GT
  { PAt ty }
| LEFTBRC t=term RIGHTBRC
  { PAv t }
| AMP x=lident
  { PAr x }
| LEFTPAR e=coma_prog RIGHTPAR
  { PAc e }
| c=coma_closure
  { PAc c }

coma_params:
| pl=coma_param*
  { (List.flatten pl) }

coma_tvar:
| x=QUOTE_LIDENT
  { PPt (mk_id x $startpos $endpos) }

coma_param:
| LT l=coma_tvar* GT
  { l }
| LEFTPAR AMP lid=separated_nonempty_list(AMP, lident) t=oftyp RIGHTPAR
  { List.map (fun id -> PPr (id, t)) lid }
| LEFTBRC lid=lident+ t=oftyp RIGHTBRC
  { List.map (fun id -> PPv (id, t)) lid }
| LEFTPAR id=lident w=prewrites p=coma_params RIGHTPAR
  { [PPc (id, w, p)] }

oftyp:
| COLON t=ty { t }

/* silent Menhir's errors about unreachable non terminal symbols */

dummy:
| module_head_parsing_only scope_head_parsing_only dummy_decl* EOF
    { }

dummy_decl:
| meta_decl {}
| use_clone_parsing_only {}
| prog_decl {}
| pure_decl {}
