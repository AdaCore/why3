
%{
  open Py_ast
%}

%token <Py_ast.constant> CST
%token <Py_ast.binop> CMP
%token <string> IDENT
%token DEF IF ELSE RETURN PRINT FOR IN AND OR NOT
%token EOF
%token LP RP LSQ RSQ COMMA EQUAL COLON BEGIN END NEWLINE
%token PLUS MINUS TIMES DIV MOD

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
    { dl, Sblock b }
;

def:
| DEF f = ident LP x = separated_list(COMMA, ident) RP
  COLON s = suite
    { f, x, s }
;

expr:
| c = CST
    { Ecst c }
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
    { e }
;

suite:
| s = simple_stmt NEWLINE
    { s }
| NEWLINE BEGIN l = nonempty_list(stmt) END
    { Sblock l }
;

stmt:
| s = simple_stmt NEWLINE
    { s }
| IF c = expr COLON s = suite
    { Sif (c, s, Sblock []) }
| IF c = expr COLON s1 = suite ELSE COLON s2 = suite
    { Sif (c, s1, s2) }
| FOR x = ident IN e = expr COLON s = suite
    { Sfor (x, e, s) }
;

simple_stmt:
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

ident:
  id = IDENT { id }
;


