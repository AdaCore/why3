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

%token BANG QUESTION LEFTMINBRC RIGHTMINBRC

%start <Coma_syntax.pfile> top_level
%start <unit> dummy

%%

top_level:
| coma_top_lvl* EOF
  { let loc = floc $startpos $startpos in
    [{id_str = "Coma"; id_ats = []; id_loc = loc}, $1] }
| coma_module+ EOF
  { $1 }

coma_module:
| MODULE attrs(uident_nq) coma_top_lvl* END
  { $2, $3 }

uses:
| USE EXPORT tqualid
  { Puseexport $3 }
| USE boption(IMPORT) n = tqualid q = option(preceded(AS, uident))
  { let loc = floc $startpos $endpos in
    if $2 && q = None then Loc.warning warn_redundant_import ~loc
      "the keyword `import' is redundant here and can be omitted";
    (Puseimport ($2, n, q) ) }

// | TYPE qualid ty_var* EQUAL ty {  }

/* ty_var:
| attrs(quote_lident) { $1 } */

coma_top_lvl:
| LET REC separated_nonempty_list(WITH, defn(EQUAL))
  { Blo $3 }
| LET defn(EQUAL)
  { Def $2 }
/* | LET coma_let*
  { Lets $2 } */
| pure_decl
  { Pld $1 }
| uses
  { Use (Loc.extract $loc, $1) }

defn(X):
| id=attrs(lident_nq) w=prewrites p=coma_params X e=coma_prog
  { let d = { pdefn_name = id; pdefn_writes = w;
              pdefn_params = p; pdefn_body = e } in
    mk_defn d $loc }

coma_prog:
| e=coma_expr bl=coma_bloc*
  { List.fold_left (fun acc b -> (b acc)) e bl }

coma_bloc:
| LEFTSQ l=separated_nonempty_list(BAR, coma_let) RIGHTSQ
  { fun e -> (mk_pexpr (PElet (e, l)) $loc) }
| LEFTSQ dl=separated_nonempty_list(BAR, defn(EQUAL)) RIGHTSQ
  { fun e -> (mk_pexpr (PEdef (e, false, dl)) $loc) }
| LEFTSQ dl=separated_nonempty_list(BAR, defn(ARROW)) RIGHTSQ
  { fun e -> (mk_pexpr (PEdef (e, true, dl)) $loc) }

coma_let:
| AMP id=attrs(lident_nq) ty=oftyp EQUAL t=term
  { id, t, ty, true }
| id=attrs(lident_nq) ty=oftyp EQUAL t=term
  { id, t, ty, false }

coma_set:
| AMP id=lident LARROW t=term { id, t }

coma_expr:
| d = coma_desc
  { mk_pexpr d $loc }

coma_desc:
| LEFTBRC t=term RIGHTBRC e=coma_expr
  { PEcut (t, true, e) }
| LEFTMINBRC t=term RIGHTMINBRC e=coma_expr
  { PEcut (t, false, e) }
| LEFTSQ l=separated_nonempty_list(BAR, coma_set) RIGHTSQ e=coma_expr
  { PEset (e, l) }
| LEFTPAR BANG e=coma_prog RIGHTPAR
  { PEbox e }
| LEFTPAR QUESTION e=coma_prog RIGHTPAR
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
| LEFTPAR FUN p=coma_param+ ARROW e=coma_prog RIGHTPAR
  { let d = PElam (List.flatten p, e) in
    mk_pexpr d $loc }
| LEFTPAR ARROW e=coma_prog RIGHTPAR
  { let d = PElam ([], e) in
    mk_pexpr d $loc }

%inline prewrites:
| LEFTSQ w=lident* RIGHTSQ
  { w }
| (* epsilon *)
  { [] }

coma_arg:
| LT ty=ty GT
  { PAt ty }
| LEFTBRC t=term RIGHTBRC
  { PAv t }
| AMP x=lident
  { PAr x }
| LEFTPAR e=coma_prog RIGHTPAR
  { PAc e }
| li=lident
  { let d = mk_pexpr (PEsym li) $loc in
    PAc d }
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
| LEFTPAR lid=coma_binder+ t=oftyp RIGHTPAR
  { List.map (fun (b,id) -> if b then PPr (id,t) else PPv (id,t)) lid }
| LEFTPAR id=attrs(lident_nq) w=prewrites p=coma_params RIGHTPAR
  { [PPc (id, w, p)] }
| LEFTBRC t=term RIGHTBRC
  { [PPa (t,true)] }
| LEFTMINBRC t=term RIGHTMINBRC
  { [PPa (t,false)] }
| LEFTBRC DOTDOT RIGHTBRC | LEFTMINBRC DOTDOT RIGHTMINBRC
  { [PPo] }
| LEFTBRC RIGHTBRC | LEFTMINBRC RIGHTMINBRC
  { [PPb] }
| LEFTSQ l=separated_nonempty_list(BAR, coma_let) RIGHTSQ
  { [PPl l] }

coma_binder:
| id=attrs(lident_nq)
  { false, id }
| AMP id=attrs(lident_nq)
  { true, id }

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
