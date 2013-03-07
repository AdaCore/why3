/********************************************************************/
/*                                                                  */
/*  The Why3 Verification Platform   /   The Why3 Development Team  */
/*  Copyright 2010-2013   --   INRIA - CNRS - Paris-Sud University  */
/*                                                                  */
/*  This software is distributed under the terms of the GNU Lesser  */
/*  General Public License version 2.1, with the special exception  */
/*  on linking described in file LICENSE.                           */
/*                                                                  */
/********************************************************************/

%{

open Tptp_ast

let loc () = (symbol_start_pos (), symbol_end_pos ())
let floc () = Why3.Loc.extract (loc ())

(* dead code
let loc_i i = (rhs_start_pos i, rhs_end_pos i)
let floc_i i = Why3.Loc.extract (loc_i i)
let loc_ij i j = (rhs_start_pos i, rhs_end_pos j)
let floc_ij i j = Why3.Loc.extract (loc_ij i j)
*)

let mk_e n = { e_node = n ; e_loc = floc () }

exception UnsupportedRole of string

let () = Why3.Exn_printer.register (fun fmt exn -> match exn with
  | Parse_error -> Format.fprintf fmt "syntax error"
  | UnsupportedRole s -> Format.fprintf fmt "unsupported role %s" s
  | _ -> raise exn)
%}

/* tokens */

%token <string> LWORD UWORD
%token <Tptp_ast.defined_word> DWORD
%token <string> SINGLE_QUOTED DISTINCT_OBJECT
%token <Tptp_ast.num_integer> INTNUM
%token <Tptp_ast.num_rational> RATNUM
%token <Tptp_ast.num_real> REALNUM

/* keywords */

%token ASSUMPTION AXIOM CNF CONJECTURE DEFINITION FOF
%token HYPOTHESIS INCLUDE LEMMA NEGATED_CONJECTURE TFF
%token THEOREM TYPE

/* symbols */

%token DOT COMMA COLON LEFTPAR RIGHTPAR LEFTSQ RIGHTSQ
%token LONGARROW LARROW RARROW LRARROW NLRARROW NAMP NBAR
%token TILDE EQUAL NEQUAL STAR GT PI BANG QUES BAR AMP
%token LET_TT LET_FT LET_TF LET_FF ITE_T ITE_F

%token SLASH_STAR_SLASH EOF

/* entry points */

%type <Tptp_ast.tptp_file> tptp_file
%start tptp_file
%%

tptp_file:
| list0_input EOF { $1 }
;

list0_input:
| /* epsilon */     { [] }
| input list0_input { $1 :: $2 }
;

input:
| kind LEFTPAR name COMMA role COMMA top_formula annotation RIGHTPAR DOT
  { Formula ($1, $3, $5, $7, floc ()) }
| INCLUDE LEFTPAR SINGLE_QUOTED formula_selection RIGHTPAR DOT
  { Include ($3, $4, floc ()) }
;

kind:
| TFF { TFF }
| FOF { FOF }
| CNF { CNF }
;

role:
| AXIOM               { Axiom }
| HYPOTHESIS          { Hypothesis }
| DEFINITION          { Definition }
| ASSUMPTION          { Assumption }
| LEMMA               { Lemma }
| THEOREM             { Theorem }
| CONJECTURE          { Conjecture }
| NEGATED_CONJECTURE  { Negated_conjecture }
| TYPE                { Type }
| LWORD               { raise (UnsupportedRole $1) }
;

top_formula:
| formula     { LogicFormula $1 }
| typed_atom  { $1 }
| sequent     { $1 }
;

/* formula and term */

formula:
| nonassoc_formula  { $1 }
| or_formula        { $1 }
| and_formula       { $1 }
| unitary_formula   { $1 }
;

nonassoc_formula:
| unitary_formula nassoc unitary_formula  { mk_e (Ebin ($2,$1,$3)) }
;

or_formula:
| unitary_formula BAR unitary_formula     { mk_e (Ebin (BOor,$1,$3)) }
| or_formula BAR unitary_formula          { mk_e (Ebin (BOor,$1,$3)) }
;

and_formula:
| unitary_formula AMP unitary_formula     { mk_e (Ebin (BOand,$1,$3)) }
| and_formula AMP unitary_formula         { mk_e (Ebin (BOand,$1,$3)) }
;

unitary_formula:
| ITE_F LEFTPAR formula COMMA formula COMMA formula RIGHTPAR
  { mk_e (Eite ($3,$5,$7)) }
| LET_FF LEFTPAR formula_def COMMA formula RIGHTPAR
  { mk_e (Elet ($3,$5)) }
| LET_TF LEFTPAR term_def COMMA formula RIGHTPAR
  { mk_e (Elet ($3,$5)) }
| quant LEFTSQ varlist RIGHTSQ COLON unitary_formula
  { mk_e (Eqnt ($1,$3,$6)) }
| TILDE unitary_formula
  { mk_e (Enot $2) }
| term NEQUAL term
  { mk_e (Enot (mk_e (Eequ ($1,$3)))) }
| term EQUAL term
  { mk_e (Eequ ($1,$3)) }
| LEFTPAR formula RIGHTPAR
  { $2 }
| plain_term
  { $1 }
;

term:
| ITE_T LEFTPAR formula COMMA term COMMA term RIGHTPAR
  { mk_e (Eite ($3,$5,$7)) }
| LET_FT LEFTPAR formula_def COMMA term RIGHTPAR
  { mk_e (Elet ($3,$5)) }
| LET_TT LEFTPAR term_def COMMA term RIGHTPAR
  { mk_e (Elet ($3,$5)) }
| DISTINCT_OBJECT
  { mk_e (Edob $1) }
| number
  { mk_e (Enum $1) }
| plain_term
  { $1 }
;

plain_term:
| DWORD                                   { mk_e (Edef ($1,[])) }
| DWORD LEFTPAR arguments RIGHTPAR        { mk_e (Edef ($1,$3)) }
| atomic_word                             { mk_e (Eapp ($1,[])) }
| atomic_word LEFTPAR arguments RIGHTPAR  { mk_e (Eapp ($1,$3)) }
| var_term                                { $1 }
;

var_term:
| UWORD   { mk_e (Evar $1) }
;

arguments:
| term                  { [$1] }
| term COMMA arguments  { $1 :: $3 }
;

formula_def:
| BANG LEFTSQ varlist RIGHTSQ COLON formula_def_inner
  { mk_e (Eqnt (Qforall,$3,$6)) }
| formula_def_inner
  { $1 }
;

term_def:
| BANG LEFTSQ varlist RIGHTSQ COLON term_def_inner
  { mk_e (Eqnt (Qforall,$3,$6)) }
| term_def_inner
  { $1 }
;

formula_def_inner:
| def_lhs LRARROW formula  { mk_e (Ebin (BOequ,$1,$3)) }
;

term_def_inner:
| def_lhs EQUAL term       { mk_e (Eequ ($1,$3)) }
;

def_lhs:
| atomic_word                                 { mk_e (Eapp ($1,[])) }
| atomic_word LEFTPAR list1_var_term RIGHTPAR { mk_e (Eapp ($1,$3)) }
;

list1_var_term:
| var_term                       { [$1] }
| var_term COMMA list1_var_term  { $1 :: $3 }
;

varlist:
| typed_var                { [$1] }
| typed_var COMMA varlist  { $1 :: $3 }
;

typed_var:
| UWORD                    { $1, mk_e (Edef (DT DTuniv, [])) }
| UWORD COLON atomic_type  { $1, $3 }
;

/* typed_atom */

typed_atom:
| untyped_atom COLON top_type  { TypedAtom ($1,$3) }
| LEFTPAR typed_atom RIGHTPAR  { $2 }
;

untyped_atom:
| atomic_word  { $1 }
;

top_type:
| atomic_type      { [],([],$1) }
| mapping_type     { [],$1 }
| quantified_type  { $1 }
;

quantified_type:
| PI LEFTSQ varlist RIGHTSQ COLON monotype  { $3,$6 }
| LEFTPAR quantified_type RIGHTPAR          { $2 }
;

monotype:
| atomic_type                    { [],$1 }
| LEFTPAR mapping_type RIGHTPAR  { $2 }
;

mapping_type:
| unitary_type GT atomic_type    { $1,$3 }
| LEFTPAR mapping_type RIGHTPAR  { $2 }
;

unitary_type:
| atomic_type                  { [$1] }
| LEFTPAR xprod_type RIGHTPAR  { $2 }
;

xprod_type:
| atomic_type STAR atomic_type  { [$1;$3] }
| xprod_type STAR atomic_type   { $1 @ [$3] }
| LEFTPAR xprod_type RIGHTPAR   { $2 }
;

/* atomic type */

atomic_type:
| DWORD                                           { mk_e (Edef ($1,[])) }
| atomic_word                                     { mk_e (Eapp ($1,[])) }
| atomic_word LEFTPAR list1_atomic_type RIGHTPAR  { mk_e (Eapp ($1,$3)) }
| var_term                                        { $1 }
;

list1_atomic_type:
| atomic_type                          { [$1] }
| atomic_type COMMA list1_atomic_type  { $1 :: $3 }
;

/* sequent */

sequent:
| tuple LONGARROW tuple     { Sequent ($1,$3) }
| LEFTPAR sequent RIGHTPAR  { $2 }
;

tuple:
| LEFTSQ RIGHTSQ                { [] }
| LEFTSQ list1_formula RIGHTSQ  { $2 }
;

list1_formula:
| formula                     { [$1] }
| formula COMMA list1_formula { $1 :: $3 }
;

/* misc */

quant:
| BANG      { Qforall }
| QUES      { Qexists }
;

nassoc:
| LARROW    { BOpmi }
| RARROW    { BOimp }
| LRARROW   { BOequ }
| NLRARROW  { BOnequ }
| NAMP      { BOnand }
| NBAR      { BOnor }
;

number:
| INTNUM  { Nint $1 }
| RATNUM  { Nrat $1 }
| REALNUM { Nreal $1 }
;

atomic_word:
| LWORD          { $1 }
| SINGLE_QUOTED  { $1 }
| reserved_word  { $1 }
;

reserved_word:
| ASSUMPTION          { "assumption" }
| AXIOM               { "axiom" }
| CNF                 { "cnf" }
| CONJECTURE          { "conjecture" }
| DEFINITION          { "definition" }
| FOF                 { "fof" }
| HYPOTHESIS          { "hypothesis" }
| INCLUDE             { "include" }
| LEMMA               { "lemma" }
| NEGATED_CONJECTURE  { "negated_conjecture" }
| TFF                 { "tff" }
| THEOREM             { "theorem" }
| TYPE                { "type" }
;

/* TODO: add support for annotations */
annotation:
| /* epsilon */ { () }
;

formula_selection:
| /* epsilon */                   { [] }
| COMMA LEFTSQ list1_name RIGHTSQ { $3 }
;

list1_name:
| name                  { [$1] }
| name COMMA list1_name { $1 :: $3 }
;

name:
| atomic_word   { $1 }
| INTNUM        { $1 }
;

/*
Local Variables:
compile-command: "unset LANG; make -C ../.."
End:
*/
