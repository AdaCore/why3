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

  type error = 
    | IllegalCharacter of char
    | UnterminatedComment
    | UnterminatedString

  exception Error of error

  let report fmt = function
    | IllegalCharacter c -> fprintf fmt "illegal character %c" c
    | UnterminatedComment -> fprintf fmt "unterminated comment"
    | UnterminatedString -> fprintf fmt "unterminated string"

  let keywords = Hashtbl.create 97
  let () = 
    List.iter 
      (fun (x,y) -> Hashtbl.add keywords x y)
      [ "theory", THEORY;
	"end", END;
	"syntax", SYNTAX;
	"remove", REMOVE;
	"tag", TAG;
      ]

  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- 
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

  let string_buf = Buffer.create 1024

  let char_for_backslash = function
    | 'n' -> '\n'
    | 't' -> '\t'
    | c -> c

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
      { Buffer.clear string_buf; string lexbuf }
  | eof 
      { EOF }
  | _ as c
      { raise (Error (IllegalCharacter c)) }

and comment = parse
  | "*)" 
      { () }
  | "(*" 
      { comment lexbuf; comment lexbuf }
  | '\n'
      { newline lexbuf; comment lexbuf }
  | eof
      { raise (Error UnterminatedComment) }
  | _ 
      { comment lexbuf }

and string = parse
  | "\""
      { STRING (Buffer.contents string_buf) }
  | "\\" (_ as c)
      { Buffer.add_char string_buf (char_for_backslash c); string lexbuf }
  | '\n'
      { newline lexbuf; Buffer.add_char string_buf '\n'; string lexbuf }
  | eof
      { raise (Error UnterminatedString) }
  | _ as c
      { Buffer.add_char string_buf c; string lexbuf }

{
  let loc lb = (lexeme_start_p lb, lexeme_end_p lb)

  let with_location f lb =
    try f lb with e -> raise (Loc.Located (loc lb, e))

  let parse_file = with_location (Driver_parser.file token)
}
