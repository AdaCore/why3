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

%{
  open Why3
  open Ptree
  open Py_ast

  let floc s e = Loc.extract (s,e)
  let mk_id id s e = { id_str = id; id_lab = []; id_loc = floc s e }
  let mk_term d s e = { term_desc = d; term_loc = floc s e }
  let mk_expr loc d = { expr_desc = d; expr_loc = loc }
  let mk_stmt loc d = { stmt_desc = d; stmt_loc = loc }

  let variant_union v1 v2 = match v1, v2 with
    | _, [] -> v1
    | [], _ -> v2
    | _, ({term_loc = loc},_)::_ -> Loc.errorm ~loc
        "multiple `variant' clauses are not allowed"

  let empty_annotation =
    { loop_invariant = []; loop_variant = [] }

%}

%token <string> INTEGER
%token <string> STRING
%token <Py_ast.binop> CMP
%token <string> IDENT
%token DEF IF ELSE RETURN PRINT WHILE FOR IN AND OR NOT NONE TRUE FALSE
%token EOF
%token LP RP LSQ RSQ COMMA EQUAL COLON BEGIN END NEWLINE
%token PLUS MINUS TIMES DIV MOD

/* annotations */
%token INVARIANT VARIANT

%left OR
%left AND
%nonassoc NOT
%nonassoc CMP
%left PLUS MINUS
%left TIMES DIV MOD
%nonassoc unary_minus
%nonassoc LSQ

%start file

%type <Py_ast.file> file

%%

file:
| NEWLINE? dl = list(def) b = list(stmt) EOF
    { dl, { stmt_desc = Sblock b; stmt_loc = floc $startpos(b) $endpos(b) } }
;

def:
| DEF f = ident LP x = separated_list(COMMA, ident) RP
  COLON s = suite
    { f, x, s }
;

expr:
| d = expr_desc
   { mk_expr (floc $startpos $endpos) d }
;

expr_desc:
| NONE
    { Enone }
| TRUE
    { Ebool true }
| FALSE
    { Ebool false }
| c = INTEGER
    { Eint c }
| s = STRING
    { Estring s }
| id = ident
    { Eident id }
| e1 = expr LSQ e2 = expr RSQ
    { Eget (e1, e2) }
| MINUS e1 = expr %prec unary_minus
    { Eunop (Uneg, e1) }
| NOT e1 = expr
    { Eunop (Unot, e1) }
| e1 = expr o = binop e2 = expr
    { Ebinop (o, e1, e2) }
| f = ident LP e = separated_list(COMMA, expr) RP
    { Ecall (f, e) }
| LSQ l = separated_list(COMMA, expr) RSQ
    { Elist l }
| LP e = expr RP
    { e.expr_desc }
;

%inline binop:
| PLUS  { Badd }
| MINUS { Bsub }
| TIMES { Bmul }
| DIV   { Bdiv }
| MOD   { Bmod }
| c=CMP { c    }
| AND   { Band }
| OR    { Bor  }
;

located(X):
| X { mk_stmt (floc $startpos $endpos) $1 }
;

suite: located(suite_desc) { $1 };

suite_desc:
| s = simple_stmt NEWLINE
    { s.stmt_desc }
| NEWLINE BEGIN l = nonempty_list(stmt) END
    { Sblock l }
;

stmt: located(stmt_desc) { $1 };

stmt_desc:
| s = simple_stmt NEWLINE
    { s.stmt_desc }
| IF c = expr COLON s = suite
    { Sif (c, s, mk_stmt (floc $startpos $endpos) (Sblock [])) }
| IF c = expr COLON s1 = suite ELSE COLON s2 = suite
    { Sif (c, s1, s2) }
| WHILE e = expr COLON s = simple_stmt NEWLINE
    { Swhile (e, empty_annotation, s) }
| WHILE e = expr COLON NEWLINE BEGIN a=loop_annotation l=nonempty_list(stmt) END
    { Swhile (e, a, mk_stmt (floc $startpos(l) $endpos(l)) (Sblock l)) }
| FOR x = ident IN e = expr COLON s = suite
    { Sfor (x, e, s) }
;

loop_annotation:
| (* epsilon *)
    { empty_annotation }
| invariant loop_annotation
    { let a = $2 in { a with loop_invariant = $1 :: a.loop_invariant } }
| variant loop_annotation
    { let a = $2 in { a with loop_variant = variant_union $1 a.loop_variant } }

invariant:
| INVARIANT i=term { i }

variant:
| VARIANT l=comma_list1(term) { List.map (fun t -> t, None) l }

simple_stmt: located(simple_stmt_desc) { $1 };

simple_stmt_desc:
| RETURN e = expr
    { Sreturn e }
| id = ident EQUAL e = expr
    { Sassign (id, e) }
| e1 = expr LSQ e2 = expr RSQ EQUAL e3 = expr
    { Sset (e1, e2, e3) }
| PRINT e = expr
    { Sprint e }
| e = expr
    { Seval e }
;

ident:
  id = IDENT { mk_id id $startpos $endpos }
;

/* logic */

mk_term(X): d = X { mk_term d $startpos $endpos }

term: t = mk_term(term_) { t }

term_:
| ident       { Tident (Qident $1) }
| INTEGER     { Tconst (Number.ConstInt ((Number.int_const_dec $1))) }
| TRUE        { Ttrue }
| FALSE       { Tfalse }

comma_list1(X):
| separated_nonempty_list(COMMA, X) { $1 }
