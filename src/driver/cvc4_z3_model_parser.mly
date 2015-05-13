%{
%}

%start <Data_structures.model_element list> output

%token <string> ATOM
%token STORE
%token CONST
%token AS
%token <string> INT_STR
%token <string> MINUS_INT_STR
%token LPAREN RPAREN
%token EOF
%%

output:
| EOF { [] }
| non_lparen_text LPAREN pairs RPAREN { $3 }

non_lparen_text:
| {}
| ATOM non_lparen_text {}

pairs:
| { [] }
| LPAREN term value RPAREN pairs { (Data_structures.create_model_element $2 $3)::$5 }

term:
| ATOM { $1 }
| LPAREN term_list RPAREN { "(" ^ $2 ^ ")" }

term_list:
| { "" }
| term term_list { $1 ^ $2 }

value:
| integer { $1 }
| array { Data_structures.Array $1 }
| term { Data_structures.Other $1 }
(*| term { Data_structures.Other $1 }*)

integer:
| INT_STR { Data_structures.Integer $1 }
| LPAREN MINUS_INT_STR RPAREN { Data_structures.Integer $2 }

array:
| LPAREN AS CONST array_skipped_part integer RPAREN { Data_structures.array_create_constant $5 }
| LPAREN STORE array integer integer RPAREN { Data_structures.array_add_element $3 $4 $5  }

array_skipped_part:
| term {}
