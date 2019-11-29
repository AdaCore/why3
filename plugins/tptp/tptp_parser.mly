(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

%{
open Tptp_ast

let mk_expr n s e = { e_node = n; e_loc = Why3.Loc.extract (s,e) }

let remove_quotes s = String.sub s 1 (String.length s - 2)

exception UnsupportedRole of string

let () = Why3.Exn_printer.register (fun fmt exn -> match exn with
  | UnsupportedRole s -> Format.fprintf fmt "unsupported role %s" s
  | Error -> Format.fprintf fmt "syntax error"
  | _ -> raise exn)
%}

(* tokens *)

%token <string> LWORD UWORD
%token <Tptp_ast.defined_word> DWORD
%token <string> SINGLE_QUOTED DISTINCT_OBJECT
%token <Tptp_ast.num_integer> INTPOSNUM
%token <Tptp_ast.num_integer> INTNEGNUM
%token <Tptp_ast.num_rational> RATPOSNUM
%token <Tptp_ast.num_rational> RATNEGNUM
%token <Tptp_ast.num_real> REALPOSNUM
%token <Tptp_ast.num_real> REALNEGNUM

(* keywords *)

%token ASSUMPTION AXIOM CNFK CONJECTURE COROLLARY DEFINITION FOFK
%token HYPOTHESIS INCLUDE LEMMA NEGATED_CONJECTURE TFFK
%token THEOREM TYPE

(* symbols *)

%token DOT COMMA COLON LEFTPAR RIGHTPAR LEFTSQ RIGHTSQ
%token LONGARROW LARROW RARROW LRARROW NLRARROW NAMP NBAR
%token TILDE EQUAL NEQUAL STAR GT PI BANG QUES BAR AMP
%token LET_TT LET_FT LET_TF LET_FF ITE_T ITE_F

%token EOF

(* entry points *)

%start <Tptp_ast.tptp_file> tptp_file
%%

tptp_file:
| input* EOF { $1 }

input:
| kind LEFTPAR name COMMA role COMMA top_formula annotation RIGHTPAR DOT
  { Formula ($1, $3, $5, $7, Why3.Loc.extract ($startpos, $endpos)) }
| INCLUDE LEFTPAR SINGLE_QUOTED formula_selection RIGHTPAR DOT
  { Include (remove_quotes $3, $4, Why3.Loc.extract ($startpos, $endpos)) }

kind:
| TFFK { TFF }
| FOFK { FOF }
| CNFK { CNF }

role:
| AXIOM               { Axiom }
| HYPOTHESIS          { Hypothesis }
| DEFINITION          { Definition }
| ASSUMPTION          { Assumption }
| LEMMA               { Lemma }
| THEOREM             { Theorem }
| CONJECTURE          { Conjecture }
| COROLLARY           { Corollary }
| NEGATED_CONJECTURE  { Negated_conjecture }
| TYPE                { Type }
| LWORD               { raise (UnsupportedRole $1) }

top_formula:
| formula     { LogicFormula $1 }
| typed_atom  { $1 }
| sequent     { $1 }

(* formula and term *)

expr(X):
| X { mk_expr $1 $startpos $endpos }

formula:
| expr(nonassoc_formula)  { $1 }
| expr(or_formula)        { $1 }
| expr(and_formula)       { $1 }
| unitary_formula         { $1 }

nonassoc_formula:
| unitary_formula nassoc unitary_formula  { Ebin ($2,$1,$3) }

or_formula:
| unitary_formula BAR unitary_formula     { Ebin (BOor,$1,$3) }
| expr(or_formula) BAR unitary_formula    { Ebin (BOor,$1,$3) }

and_formula:
| unitary_formula AMP unitary_formula     { Ebin (BOand,$1,$3) }
| expr(and_formula) AMP unitary_formula   { Ebin (BOand,$1,$3) }

unitary_formula:
| expr(unitary_formula_)    { $1 }
| LEFTPAR formula RIGHTPAR  { $2 }

unitary_formula_:
| ITE_F LEFTPAR formula COMMA formula COMMA formula RIGHTPAR
  { Eite ($3,$5,$7) }
| LET_FF LEFTPAR expr(formula_def) COMMA formula RIGHTPAR
  { Elet ($3,$5) }
| LET_TF LEFTPAR expr(term_def) COMMA formula RIGHTPAR
  { Elet ($3,$5) }
| quant LEFTSQ varlist RIGHTSQ COLON unitary_formula
  { Eqnt ($1,$3,$6) }
| TILDE unitary_formula
  { Enot $2 }
| term NEQUAL term
  { Enot (mk_expr (Eequ ($1,$3)) $startpos $endpos) }
| term EQUAL term
  { Eequ ($1,$3) }
| plain_term
  { $1 }

term:
| expr(term_) { $1 }

term_:
| ITE_T LEFTPAR formula COMMA term COMMA term RIGHTPAR
  { Eite ($3,$5,$7) }
| LET_FT LEFTPAR expr(formula_def) COMMA term RIGHTPAR
  { Elet ($3,$5) }
| LET_TT LEFTPAR expr(term_def) COMMA term RIGHTPAR
  { Elet ($3,$5) }
| DISTINCT_OBJECT
  { Edob $1 }
| pos_number
  { Enum $1 }
| neg_number
  { Edef (DF DFumin, [mk_expr (Enum $1) $startpos $endpos]) }
| plain_term
  { $1 }

plain_term:
| DWORD paren_list(term)        { Edef ($1,$2) }
| atomic_word paren_list(term)  { Eapp ($1,$2) }
| var_term                      { $1 }

var_term:
| UWORD { Evar $1 }

formula_def:
| BANG LEFTSQ varlist RIGHTSQ COLON expr(formula_def) { Eqnt (Qforall,$3,$6) }
| formula_def_inner                                   { $1 }

term_def:
| BANG LEFTSQ varlist RIGHTSQ COLON expr(term_def)    { Eqnt (Qforall,$3,$6) }
| term_def_inner                                      { $1 }

formula_def_inner:
| expr(def_lhs) LRARROW formula       { Ebin (BOequ,$1,$3) }
| LEFTPAR formula_def_inner RIGHTPAR  { $2 }

term_def_inner:
| expr(def_lhs) EQUAL term        { Eequ ($1,$3) }
| LEFTPAR term_def_inner RIGHTPAR { $2 }

def_lhs:
| atomic_word paren_list(expr(var_term)) { Eapp ($1,$2) }

varlist:
| comma_list(typed_var) { $1 }

typed_var:
| UWORD
  { $1, mk_expr (Edef (DT DTuniv, [])) $startpos $endpos }
| UWORD COLON atomic_type
  { $1, $3 }

(* typed_atom *)

typed_atom:
| untyped_atom COLON top_type  { TypedAtom ($1,$3) }
| LEFTPAR typed_atom RIGHTPAR  { $2 }

untyped_atom:
| atomic_word { $1 }

top_type:
| atomic_type               { [],([],$1) }
| mapping_type              { [],$1 }
| quantified_type           { $1 }
| LEFTPAR top_type RIGHTPAR { $2 }

quantified_type:
| PI LEFTSQ varlist RIGHTSQ COLON monotype  { $3,$6 }

monotype:
| atomic_type                    { [],$1 }
| LEFTPAR mapping_type RIGHTPAR  { $2 }

mapping_type:
| unitary_type GT atomic_type    { $1,$3 }

unitary_type:
| atomic_type                  { [$1] }
| LEFTPAR xprod_type RIGHTPAR  { $2 }

xprod_type:
| atomic_type STAR atomic_type  { [$1;$3] }
| xprod_type STAR atomic_type   { $1 @ [$3] }

(* atomic type *)

atomic_type:
| expr(atomic_type_)  { $1 }

atomic_type_:
| DWORD                               { Edef ($1,[]) }
| atomic_word paren_list(atomic_type) { Eapp ($1,$2) }
| var_term                            { $1 }

(* sequent *)

sequent:
| tuple LONGARROW tuple     { Sequent ($1,$3) }
| LEFTPAR sequent RIGHTPAR  { $2 }

tuple:
| LEFTSQ fl = separated_list(COMMA,formula) RIGHTSQ  { fl }

(* misc *)

quant:
| BANG      { Qforall }
| QUES      { Qexists }

nassoc:
| LARROW    { BOpmi }
| RARROW    { BOimp }
| LRARROW   { BOequ }
| NLRARROW  { BOnequ }
| NAMP      { BOnand }
| NBAR      { BOnor }

pos_number:
| INTPOSNUM  { Nint $1 }
| RATPOSNUM  { Nrat $1 }
| REALPOSNUM { Nreal $1 }

neg_number:
| INTNEGNUM  { Nint $1 }
| RATNEGNUM  { Nrat $1 }
| REALNEGNUM { Nreal $1 }

atomic_word:
| LWORD          { $1 }
| SINGLE_QUOTED  { $1 }
| reserved_word  { $1 }

reserved_word:
| ASSUMPTION          { "assumption" }
| AXIOM               { "axiom" }
| CNFK                { "cnf" }
| CONJECTURE          { "conjecture" }
| DEFINITION          { "definition" }
| FOFK                { "fof" }
| HYPOTHESIS          { "hypothesis" }
| INCLUDE             { "include" }
| LEMMA               { "lemma" }
| NEGATED_CONJECTURE  { "negated_conjecture" }
| TFFK                { "tff" }
| THEOREM             { "theorem" }
| TYPE                { "type" }

(* TODO: add support for annotations *)
annotation:
| (* epsilon *) { () }

formula_selection:
| (* epsilon *)                         { [] }
| COMMA LEFTSQ comma_list(name) RIGHTSQ { $3 }

name:
| atomic_word { $1 }
| INTPOSNUM   { $1 }
| INTNEGNUM   { "-" ^ $1 }

paren_list(X):
| (* epsilon *)                   { [] }
| LEFTPAR comma_list(X) RIGHTPAR  { $2 }

comma_list(X):
| separated_nonempty_list(COMMA,X)  { $1 }
