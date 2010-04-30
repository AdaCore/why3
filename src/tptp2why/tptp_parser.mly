
%{

  open TptpTree
  open Tptp_lexer

%}


(** set of tokens *)


%token<int> INT
%token LPAREN RPAREN LBRACKET RBRACKET
%token DOT COMMA COLON
%token PIPE AND ARROW LRARROW EQUAL NEQUAL NOT
%token BANG QUESTION
%token QUOTE

%token FOF AXIOM CONJECTURE UIDENT LIDENT

%token EOL



%start<tptp> tptp
%start<fmla> fmla

%%

tptp:
| e = decl EOL es = decl*
  { e :: es }

decl:
| FOF LPAREN name = lident COMMA ty = decl_type COMMA f = fmla RPAREN DOT
  { FOF (name, ty, f) }

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
| atom = INT
  { TAtom atom }
| var = uident
  { TVar var }
| funct = lident LPAREN terms = separated_list(COMMA, term) RPAREN
  { TFunctor (funct, terms) }


lident:
| QUOTE i=LIDENT QUOTE { "'" ^ i ^ "'" }
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
