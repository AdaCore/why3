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
  open Why
  open Lexer
  open Term
  open Pgm_parser

  exception UnterminatedLogic
  exception IllegalCharacter of char

  let () = Exn_printer.register (fun fmt exn -> match exn with
    | UnterminatedLogic -> fprintf fmt "unterminated logic block"
    | IllegalCharacter c -> fprintf fmt "illegal character %c" c
    | Parsing.Parse_error -> fprintf fmt "syntax error"
    | _ -> raise exn)

  let keywords = Hashtbl.create 97
  let () = 
    List.iter 
      (fun (x,y) -> Hashtbl.add keywords x y)
      [ "absurd", ABSURD;
	"and", AND;
	"any", ANY;
	"as", AS;
	"assert", ASSERT;
	"assume", ASSUME;
	"begin", BEGIN;
        "check", CHECK;
	"do", DO;
	"done", DONE;
        "else", ELSE;
	"end", END;
	"exception", EXCEPTION; 
	"for", FOR;
	"fun", FUN;
	"ghost", GHOST;
	"if", IF;
	"in", IN;
	"invariant", INVARIANT;
	"label", LABEL;
	"let", LET;
	"match", MATCH;
	"not", NOT;
	"of", OF;
	"parameter", PARAMETER;
	"raise", RAISE;
	"raises", RAISES;
	"reads", READS;
	"rec", REC;
	"then", THEN;
	"try", TRY;
	"type", TYPE;
	"variant", VARIANT;
	"while", WHILE;
	"with", WITH;
        "writes", WRITES;
      ]
	
  let update_loc lexbuf file line chars =
    let pos = lexbuf.lex_curr_p in
    let new_file = match file with None -> pos.pos_fname | Some s -> s in
    lexbuf.lex_curr_p <- 
      { pos with
	  pos_fname = new_file;
	  pos_lnum = int_of_string line;
	  pos_bol = pos.pos_cnum - int_of_string chars;
      }

  let logic_start_loc = ref Loc.dummy_position
  let logic_buffer = Buffer.create 1024

  let loc lb = (lexeme_start_p lb, lexeme_end_p lb)

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

let op_char_1 = ['=' '<' '>' '~']
let op_char_2 = ['+' '-']
let op_char_3 = ['*' '/' '%']
let op_char_4 = ['!' '$' '&' '?' '@' '^' '.' ':' '|' '#']
let op_char_34 = op_char_3 | op_char_4
let op_char_234 = op_char_2 | op_char_34
let op_char_1234 = op_char_1 | op_char_234

let op_char_pref = ['!' '?']

rule token = parse
  | "#" space* ("\"" ([^ '\010' '\013' '"' ]* as file) "\"")?
    space* (digit+ as line) space* (digit+ as char) space* "#"
      { update_loc lexbuf file line char; token lexbuf }
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
  | (digit+ as i) ("" as f) ['e' 'E'] (['-' '+']? digit+ as e)
  | (digit+ as i) '.' (digit* as f) (['e' 'E'] (['-' '+']? digit+ as e))?
  | (digit* as i) '.' (digit+ as f) (['e' 'E'] (['-' '+']? digit+ as e))?
      { REAL (RConstDecimal (i, f, Util.option_map remove_leading_plus e)) }
  | '0' ['x' 'X'] ((hexadigit* as i) '.' (hexadigit+ as f) 
                  |(hexadigit+ as i) '.' (hexadigit* as f)
		  |(hexadigit+ as i) ("" as f))
    ['p' 'P'] (['-' '+']? digit+ as e)
      { REAL (RConstHexa (i, f, remove_leading_plus e)) }
  | "(*)"
      { LEFTPAR_STAR_RIGHTPAR }
  | "(*"
      { comment lexbuf; token lexbuf }
  | "'"
      { QUOTE }
  | "`"
      { BACKQUOTE }
  | ","
      { COMMA }
  | "("
      { LEFTPAR }
  | ")"
      { RIGHTPAR }
  | ":"
      { COLON }
  | ";"
      { SEMICOLON }
  | ":="
      { COLONEQUAL }
  | "->"
      { ARROW }
  | "="
      { EQUAL }
  | "<>"
      { LTGT }
  | "@"
      { AT }
  | "."
      { DOT }
  | "["
      { LEFTSQ }
  | "]"
      { RIGHTSQ }
  | "{"
      { logic_start_loc := loc lexbuf; 
	let s = logic lexbuf in
	LOGIC ((fst !logic_start_loc, snd (loc lexbuf)), s) }
  (* FIXME: allow newlines as well *)
  | "{" space* "}"
      { LOGIC (loc lexbuf, "true") }
  | "{{"
      { LEFTBLEFTB }
  | "}}"
      { RIGHTBRIGHTB }
  | "|"
      { BAR }
  | "||"
      { BARBAR }
  | "&&" 
      { AMPAMP }
  | op_char_pref op_char_4* as s
      { OPPREF s }
  | op_char_1234* op_char_1 op_char_1234* as s
      { OP1 s }
  | op_char_234*  op_char_2 op_char_234*  as s
      { OP2 s }
  | op_char_34*   op_char_3 op_char_34*  as s
      { OP3 s }
  | op_char_4+ as s
      { OP4 s }
  | "\""
      { STRING (string lexbuf) }
  | eof 
      { EOF }
  | _ as c
      { raise (IllegalCharacter c) }

and logic = parse
  | "}"
      { let s = Buffer.contents logic_buffer in
	Buffer.clear logic_buffer;
	s }
  | newline
      { newline lexbuf; Buffer.add_char logic_buffer '\n'; logic lexbuf }
  | eof
      { raise (Loc.Located (!logic_start_loc, UnterminatedLogic)) }
  | _ as c
      { Buffer.add_char logic_buffer c; logic lexbuf }


{

  let parse_file = with_location (file token)

}

(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. testl"
End: 
*)

