
{
  type tok = FOF | CONJECTURE | AXIOM 

  let keywords = Hashtbl.create 97
  let () =
    List.iter
      (fun (x,y) -> Hashtbl.add keywords x y)
      [
  "fof", FOF;
  "conjecture", CONJECTURE;
  "axiom", AXIOM
      ]

  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

}

let newline = '\n'
let space = [' ' '\t' '\r']
let lalpha = ['a'-'z' '_']
let ualpha = ['A'-'Z']
let alpha = lalpha | ualpha
let digit = ['0'-'9']
let lident = lalpha (alpha | digit | '\'')*
let uident = ualpha (alpha | digit | '\'')*
let decimal_literal =
  ['0'-'9'] ['0'-'9' '_']*
let hex_literal =
  '0' ['x' 'X'] ['0'-'9' 'A'-'F' 'a'-'f']['0'-'9' 'A'-'F' 'a'-'f' '_']*
let oct_literal =
  '0' ['o' 'O'] ['0'-'7'] ['0'-'7' '_']*
let bin_literal =
  '0' ['b' 'B'] ['0'-'1'] ['0'-'1' '_']*
let int_literal =
  decimal_literal | hex_literal | oct_literal | bin_literal
let hexadigit = ['0'-'9' 'a'-'f' 'A'-'F']


rule token = parse
  | newline
      { newline lexbuf; token lexbuf }
  | space+
      { token lexbuf }
  | '_'
      { UNDERSCORE }
  | lident as id
      { try Hashtbl.find keywords id with Not_found -> LIDENT id }
  | uident as id
      { UIDENT id }
  | int_literal as s
      { INTEGER s }
  | "%"
      { COMMENT; comment lexbuf }
  | "'"
      { QUOTE }
  | "\""
      { QUOTE }
  | ","
      { COMMA }
  | "("
      { LEFTPAR }
  | ")"
      { RIGHTPAR }
  | ":"
      { COLON }
  | "=>"
      { ARROW }
  | "<=>"
      { LRARROW }
  | "."
      { DOT }
  | "|"
      { PIPE }
  | "="
      { EQUAL }
  | "!="
      { NEQUAL }
  | "["
      { LBRACKET }
  | "]"
      { RBRACKET }
  | eof
      { EOF }
and comment = parse (* read until newline *)
  | newline
    { token lexbuf }
  | _
    { comment lexbuf }
