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

coma_top_lvl:
| LET ioption(REC) separated_nonempty_list(WITH, defn(EQUAL))
  { Blo $3 }
| pure_decl
  { Mlw $1 }
| meta_decl
  { Mlw $1 }
| uses
  { Use $1 }

defn(X):
| id=attrs(lword_nq) w=prewrites p=coma_params X e=coma_prog
  { mk_defn { pdefn_name = id; pdefn_writes = w;
              pdefn_params = p; pdefn_body = e } $loc }

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
| AMP id=attrs(lword_nq) ty=oftyp EQUAL t=term
  { id, t, ty, true }
| id=attrs(lword_nq) ty=oftyp EQUAL t=term
  { id, t, ty, false }

coma_set:
| AMP id=lword LARROW t=term { id, t }

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
| x=lqword
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
| LEFTSQ w=lword* RIGHTSQ
  { w }
| (* epsilon *)
  { [] }

coma_arg:
| LT ty=ty GT
  { PAt ty }
| LEFTBRC t=term RIGHTBRC
  { PAv t }
| AMP x=lword
  { PAr x }
| LEFTPAR e=coma_prog RIGHTPAR
  { PAc e }
| li=lqword
  { let d = mk_pexpr (PEsym li) $loc in
    PAc d }
| c=coma_closure
  { PAc c }

coma_params:
| pl=coma_param*
  { (List.flatten pl) }

coma_tvar:
| x=quote_lident
  { PPt x }

coma_param:
| LT l=coma_tvar* GT
  { l }
| LEFTPAR lid=coma_binder+ t=oftyp RIGHTPAR
  { List.map (fun (b,id) -> if b then PPr (id,t) else PPv (id,t)) lid }
| LEFTPAR id=attrs(lword_nq) w=prewrites p=coma_params RIGHTPAR
  { [PPc (id, w, p)] }
| LEFTBRC t=term RIGHTBRC
  { [PPa (t,true)] }
| LEFTMINBRC t=term RIGHTMINBRC
  { [PPa (t,false)] }
| LEFTBRC DOTDOT RIGHTBRC
  { [PPo] }
| LEFTBRC RIGHTBRC
  { [PPb] }
| LEFTSQ l=separated_nonempty_list(BAR, coma_let) RIGHTSQ
  { [PPl l] }

coma_binder:
| id=attrs(lword_nq)
  { false, id }
| AMP id=attrs(lword_nq)
  { true, id }

oftyp:
| COLON t=ty { t }

lqword:
| lword                  { Qident $1 }
| uqualid DOT lword      { Qdot ($1, $3) }

lword:
| lident    { $1 }
| lkeyword  { mk_id $1 $startpos $endpos }

lword_nq:
| lident_nq { $1 }
| lkeyword  { mk_id $1 $startpos $endpos }

lkeyword:
| ABSURD { "absurd" }
| RETURN { "return" }
| ABSTRACT { "abstract" }
| ALIAS { "alias" }
(* | ANY { "any" } *)
| AS { "as" }
| ASSERT { "assert" }
| ASSUME { "assume" }
| AT { "at" }
(* | AXIOM { "axiom" } *)
| BEGIN { "begin" }
| BREAK { "break" }
| BY { "by" }
| CHECK { "check" }
| CLONE { "clone" }
(* | COINDUCTIVE { "coinductive" } *)
(* | CONSTANT { "constant" } *)
| CONTINUE { "continue" }
| DIVERGES { "diverges" }
| DO { "do" }
| DONE { "done" }
| DOWNTO { "downto" }
| ELSE { "else" }
(* | END { "end" } *)
| ENSURES { "ensures" }
| EPSILON { "epsilon" }
| EXCEPTION { "exception" }
| EXISTS { "exists" }
| EXPORT { "export" }
| FALSE { "false" }
| FOR { "for" }
| FORALL { "forall" }
(* | FUN { "fun" } *)
(* | FUNCTION { "function" } *)
| GHOST { "ghost" }
(* | GOAL { "goal" } *)
| IF { "if" }
| IMPORT { "import" }
| IN { "in" }
(* | INDUCTIVE { "inductive" } *)
| INVARIANT { "invariant" }
| LABEL { "label" }
(* | LEMMA { "lemma" } *)
(* | LET { "let" } *)
| MATCH { "match" }
(* | META { "meta" } *)
(* | MODULE { "module" } *)
| MUTABLE { "mutable" }
| NOT { "not" }
| OLD { "old" }
| PARTIAL { "partial" }
(* | PREDICATE { "predicate" } *)
| PRIVATE { "private" }
| PURE { "pure" }
| RAISE { "raise" }
| RAISES { "raises" }
| READS { "reads" }
| REC { "rec" }
| REQUIRES { "requires" }
| RETURNS { "returns" }
| SCOPE { "scope" }
| SO { "so" }
| THEN { "then" }
| THEORY { "theory" }
| TO { "to" }
| TRUE { "true" }
| TRY { "try" }
(* | TYPE { "type" } *)
(* | USE { "use" } *)
| VAL { "val" }
| VARIANT { "variant" }
| WHILE { "while" }
(* | WITH { "with" } *)
| WRITES { "writes" }

/* silent Menhir's errors about unreachable non terminal symbols */

dummy:
| module_head_parsing_only scope_head_parsing_only dummy_decl* EOF
    { }

dummy_decl:
| meta_decl {}
| use_clone_parsing_only {}
| prog_decl {}
| pure_decl {}
