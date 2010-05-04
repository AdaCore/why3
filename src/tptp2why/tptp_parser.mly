
%{

  open TptpTree

%}


(** set of tokens *)

%token<string> INT
%token LPAREN RPAREN LBRACKET RBRACKET
%token DOT COMMA COLON
%token PIPE AND ARROW LRARROW EQUAL NEQUAL NOT
%token BANG QUESTION
%token QUOTE

%token<string> UIDENT
%token<string> LIDENT
%token<string> SINGLEQUOTED
%token FOF AXIOM CONJECTURE INCLUDE
%token EOF



%start<TptpTree.decl list> tptp
%start<TptpTree.decl> decl

%%

tptp:
| e = decl es = decl* EOF
  { e :: es }
| error
  { Printf.printf "error at lexing pos %i\n" $endpos.Lexing.pos_lnum; assert false }

decl:
| FOF LPAREN name = lident COMMA ty = decl_type COMMA f = fmla RPAREN DOT
  { Fof (name, ty, f) }
| INCLUDE LPAREN p = SINGLEQUOTED RPAREN DOT
  { Include p }

decl_type:
| AXIOM { Axiom }
| CONJECTURE { Conjecture }


fmla:
| quant = quantifier LBRACKET vars = separated_nonempty_list(COMMA, variable) RBRACKET
  COLON f = fmla
  { FQuant (quant, vars, f) }
| LPAREN f = fmla RPAREN
  { f }
| f1 = fmla op = logic_binop f2 = fmla
  { FBinop (op, f1, f2) }
| op = logic_unop f = fmla
  { FUnop (op, f) }
| funct = lident LPAREN terms = separated_list(COMMA, term) RPAREN
  { FPred (funct, terms) }
| t1 = term op = term_binop t2 = term
  { FTermBinop (op, t1, t2) }


term:
| atom = lident
  { TAtom atom }
| c = INT
  { TConst c }
| var = uident
  { TVar var }
| funct = lident LPAREN terms = separated_list(COMMA, term) RPAREN
  { TFunctor (funct, terms) }


lident:
| i = SINGLEQUOTED { i }
| i = LIDENT { i }
uident:
| i = UIDENT { i }
%inline variable:
| i = uident { i }
%inline quantifier:
| BANG { Forall }
| QUESTION { Exist }
%inline logic_binop:
| PIPE { Or }
| AND { And }
| ARROW { Implies }
| LRARROW { Equiv }
%inline logic_unop:
| NOT { Not }
%inline term_binop:
| EQUAL { Equal }
| NEQUAL { NotEqual }
