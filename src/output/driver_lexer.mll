(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
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

  let keywords = Hashtbl.create 97
  let () = 
    List.iter 
      (fun (x,y) -> Hashtbl.add keywords x y)
      [ "theory", THEORY;
	"end", END;
	"syntax", SYNTAX;
	"remove", REMOVE;
	"tag", TAG;
	"cloned", CLONED;
	"prelude", PRELUDE;
	"printer", PRINTER;
	"call_on_file", CALL_ON_FILE;
	"call_on_stdin", CALL_ON_STDIN;
	"valid", VALID;
	"invalid", INVALID;
	"unknown", UNKNOWN;
	"fail", FAIL;
      ]

}

let space = [' ' '\t' '\r']
let alpha = ['a'-'z' 'A'-'Z' '_']
let digit = ['0'-'9']
let ident = alpha (alpha | digit | '\'')*

rule token = parse
  | '\n'
      { newline lexbuf; token lexbuf }
  | space+  
      { token lexbuf }
  | "(*"
      { comment lexbuf; token lexbuf }
  | '_' 
      { UNDERSCORE }
  | ident as id
      { try Hashtbl.find keywords id with Not_found -> IDENT id }
  | "<>" | "<" | "<=" | ">" | ">=" 
  | "="
  | "+" | "-"
  | "*" | "/" | "%" as op
      { OPERATOR op }
  | "("
      { LEFTPAR }
  | ")"
      { RIGHTPAR }
  | "."
      { DOT }
  | "\""
      { STRING (string lexbuf) }
  | eof 
      { EOF }
  | _ as c
      { raise (Error (IllegalCharacter c)) }

{
  let loc lb = (lexeme_start_p lb, lexeme_end_p lb)

  let with_location f lb =
    try f lb with e -> raise (Loc.Located (loc lb, e))

  let parse_file = with_location (Driver_parser.file token)
}
