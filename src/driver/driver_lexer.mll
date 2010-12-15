(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

{
  open Format
  open Lexing
  open Driver_parser
  open Lexer

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
	"remove", REMOVE;
	"meta", META;
	"cloned", CLONED;
	"prelude", PRELUDE;
	"printer", PRINTER;
	"valid", VALID;
	"invalid", INVALID;
        "timeout", TIMEOUT;
        "time",    TIME;
	"unknown", UNKNOWN;
	"fail", FAIL;
        "logic", LOGIC;
        "type", TYPE;
        "prop", PROP;
        "filename", FILENAME;
        "transformation", TRANSFORM;
        "plugin", PLUGIN
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
      { newline lexbuf; token lexbuf }
  | space+
      { token lexbuf }
  | "(*)"
      { LEFTPAR_STAR_RIGHTPAR }
  | "(*"
      { comment lexbuf; token lexbuf }
  | '_'
      { UNDERSCORE }
  | ident as id
      { try Hashtbl.find keywords id with Not_found -> IDENT id }
  | digit+ as i
      { INTEGER (int_of_string i) }
  | "("
      { LEFTPAR }
  | ")"
      { RIGHTPAR }
  | "."
      { DOT }
  | ","
      { COMMA }
  | op_char+ as op
      { OPERATOR op }
  | "\""
      { STRING (string lexbuf) }
  | eof
      { EOF }
  | _ as c
      { raise (IllegalCharacter c) }

{
  let loc lb = (lexeme_start_p lb, lexeme_end_p lb)

  let with_location f lb =
    try f lb with e -> raise (Loc.Located (loc lb, e))

  let parse_file = with_location (Driver_parser.file token)
}
