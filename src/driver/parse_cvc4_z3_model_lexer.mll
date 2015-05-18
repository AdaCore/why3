{
  open Parse_cvc4_z3_model_parser
  exception SyntaxError
}

let atom = [^'('')'' ''\t''\n']
let space = [' ''\t''\n']

rule token = parse
  | '\n'
    { token lexbuf }
  | space+ as space_str
      { SPACE (space_str) }
  | "store" { STORE }
  | "const" { CONST }
  | "as" { AS }
  | '('
      { LPAREN }
  | ')'
      { RPAREN }
  | ['0'-'9']+ as integer
      { INT_STR (integer) }
  | '-'space*(['0'-'9']+ as integer) { MINUS_INT_STR ("-"^integer) }
  | atom+ as at { ATOM (at) }
  | eof
      { EOF }
    (* | space { SPACE } *)
  | _
	{ raise SyntaxError }

