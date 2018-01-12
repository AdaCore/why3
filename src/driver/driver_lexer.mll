(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

{
  open Format
  open Lexing
  open Driver_parser

  exception IllegalCharacter of char

  let () = Exn_printer.register (fun fmt e -> match e with
    | IllegalCharacter c -> fprintf fmt "illegal character %c" c
    | _ -> raise e)

  let keywords = Hashtbl.create 97
  let () =
    List.iter
      (fun (x,y) -> Hashtbl.add keywords x y)
      [ "theory", THEORY;
        "end", END;
        "syntax", SYNTAX;
        "overriding", OVERRIDING;
        "remove", REMOVE;
        "meta", META;
        "prelude", PRELUDE;
        "printer", PRINTER;
	"steps", STEPS;
	"model_parser", MODEL_PARSER;
        "valid", VALID;
        "invalid", INVALID;
        "timeout", TIMEOUT;
        "outofmemory", OUTOFMEMORY;
        "steplimitexceeded", STEPLIMITEXCEEDED;
        "time",    TIME;
        "unknown", UNKNOWN;
        "fail", FAIL;
        "constant", CONSTANT;
        "function", FUNCTION;
        "predicate", PREDICATE;
        "type", TYPE;
        "prop", PROP;
        "allprops", ALL;
        "filename", FILENAME;
        "transformation", TRANSFORM;
        "plugin", PLUGIN;
        "blacklist", BLACKLIST;
        (* WhyML *)
        "module", MODULE;
        "exception", EXCEPTION;
        "val", VAL;
        "converter", CONVERTER;
        "literal", LITERAL;
      ]

}

let space = [' ' '\t' '\r']
let alpha = ['a'-'z' 'A'-'Z' '_']
let digit = ['0'-'9']
let ident = alpha (alpha | digit | '\'')*

let op_char = ['=' '<' '>' '~' '+' '-' '*' '/' '%'
               '!' '$' '&' '?' '@' '^' '.' ':' '|' '#']

rule token = parse
  | '\n'
      { new_line lexbuf; token lexbuf }
  | space+
      { token lexbuf }
  | "(*)"
      { LEFTPAR_STAR_RIGHTPAR }
  | "(*"
      { Lexlib.comment lexbuf; token lexbuf }
  | '_'
      { UNDERSCORE }
  | ident as id
      { try Hashtbl.find keywords id with Not_found -> IDENT id }
  | digit+ as i
      { INTEGER (int_of_string i) }
  | "<-"
      { LARROW }
  | "["
      { LEFTSQ }
  | "]"
      { RIGHTSQ }
  | "("
      { LEFTPAR }
  | ")"
      { RIGHTPAR }
  | "."
      { DOT }
  | ","
      { COMMA }
  | "'"
      { QUOTE }
  | op_char+ as op
      { OPERATOR op }
  | "\""
      { STRING (Lexlib.string lexbuf) }
  | "import" space*  "\""
      { INPUT (Lexlib.string lexbuf) }
  | eof
      { EOF }
  | _ as c
      { raise (IllegalCharacter c) }

{
  let parse_file_gen parse input_lexbuf lexbuf =
    let s = Stack.create () in
    Stack.push lexbuf s;
    let rec multifile lex_dumb =
      let lexbuf = Stack.top s in
      let tok = token lexbuf in
      Loc.transfer_loc lexbuf lex_dumb;
      match tok with
        | INPUT filename ->
          let dirname = Filename.dirname lexbuf.lex_curr_p.pos_fname in
          let filename = Sysutil.absolutize_filename dirname filename in
          Stack.push (input_lexbuf filename) s;
          multifile lex_dumb
        | EOF -> ignore (Stack.pop s);
          if Stack.is_empty s then EOF else multifile lex_dumb
        | _ -> tok in
    let lex_dumb = Lexing.from_function (fun _ _ -> assert false) in
    Loc.transfer_loc lexbuf lex_dumb;
    Loc.with_location (parse multifile) lex_dumb

  let parse_file = parse_file_gen Driver_parser.file
  let parse_file_extract = parse_file_gen Driver_parser.file_extract
}
