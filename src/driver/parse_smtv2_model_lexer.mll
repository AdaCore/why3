{
  open Parse_smtv2_model_parser
  exception SyntaxError
}

let atom = [^'('')'' ''\t''\n']
let space = [' ''\t''\n']
let num = ['0'-'9']+

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
  | num as integer
      { INT_STR (integer) }
  | "(_ bv"(num as bv_value)" "num")" { BITVECTOR_VALUE (int_of_string bv_value)  }
  | '-'space*(['0'-'9']+ as integer) { MINUS_INT_STR ("-"^integer) }
  | atom+ as at { ATOM (at) }
  | eof
      { EOF }
    (* | space { SPACE } *)
  | _
	{ raise SyntaxError }
