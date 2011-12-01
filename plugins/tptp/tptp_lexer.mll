(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
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
  open Tptp_ast
  open Tptp_parser
  open Tptp_typing

  (* lexical errors *)

  exception IllegalCharacter of char
  exception UnterminatedComment
  exception UnterminatedString

  let () = Exn_printer.register (fun fmt e -> match e with
    | IllegalCharacter c -> fprintf fmt "illegal character %c" c
    | UnterminatedComment -> fprintf fmt "unterminated comment"
    | UnterminatedString -> fprintf fmt "unterminated string"
    | DoubleDollarWord -> fprintf fmt "system-specifics are not supported"
    | _ -> raise e)

  let defwords = Hashtbl.create 97
  let () = List.iter (fun (x,y) -> Hashtbl.add defwords x y) [
    "ceiling", CEILING;
    "difference", DIFFERENCE;
    "distinct", DISTINCT;
    "false", FALSE;
    "floor", FLOOR;
    "greater", GREATER;
    "greatereq", GREATEREQ;
    "i", ITYPE;
    "int", INT;
    "is_int", IS_INT;
    "is_rat", IS_RAT;
    "ite_f", ITEF;
    "ite_t", ITET;
    "iType", ITYPE;
    "less", LESS;
    "lesseq", LESSEQ;
    "o", OTYPE;
    "oType", OTYPE;
    "product", PRODUCT;
    "quotient", QUOTIENT;
    "quotient_e", QUOTIENT_E;
    "quotient_t", QUOTIENT_T;
    "quotient_f", QUOTIENT_F;
    "rat", RAT;
    "real", REAL;
    "remainder_e", REMAINDER_E;
    "remainder_t", REMAINDER_T;
    "remainder_f", REMAINDER_F;
    "round", ROUND;
    "sum", SUM;
    "to_int", TO_INT;
    "to_rat", TO_RAT;
    "to_real", TO_REAL;
    "true", TRUE;
    "truncate", TRUNCATE;
    "tType", TTYPE;
    "uminus", UMINUS;
  ]

  let keywords = Hashtbl.create 97
  let () = List.iter (fun (x,y) -> Hashtbl.add keywords x y) [
    "assumption", ASSUMPTION;
    "axiom", AXIOM;
    "cnf", CNF;
    "conjecture", CONJECTURE;
    "definition", DEFINITION;
    "fof", FOF;
    "hypothesis", HYPOTHESIS;
    "include", INCLUDE;
    "lemma", LEMMA;
    "negated_conjecture", NEGATED_CONJECTURE;
    "tff", TFF;
    "theorem", THEOREM;
    "type", TYPE;
  ]

  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

  let comment_start_loc = ref Loc.dummy_position

  let loc lb = Loc.extract (lexeme_start_p lb, lexeme_end_p lb)
}

let newline = '\n'
let space = [' ' '\t' '\r']

let lalpha = ['a'-'z']
let ualpha = ['A'-'Z']
let digit  = ['0'-'9']
let nzero  = ['1'-'9']

let alnum = lalpha | ualpha | digit | '_'
let lword = lalpha alnum*
let uword = ualpha alnum*

let positive = nzero digit*
let natural  = '0' | positive

let sq_char = [' '-'&' '('-'[' ']'-'~'] | '\\' ['\\' '\'']
let do_char = [' '-'!' '#'-'[' ']'-'~'] | '\\' ['\\' '"']

rule token = parse
  | newline
      { newline lexbuf; token lexbuf }
  | space+
      { token lexbuf }
  | lword as id
      { try Hashtbl.find keywords id with Not_found -> LWORD id }
  | uword as id
      { UWORD id }
  | '\'' (sq_char+ as sq) '\''
      { SINGLE_QUOTED sq }
  | '"' (do_char* as dob) '"'
      { DISTINCT_OBJECT dob }
  | '$' (lword as id)
      { DWORD id }
  | "$$" lword
      { raise DoubleDollarWord }
  | '+'? (natural as s)
  | '-'   natural as s
      { INTEGER s }
  | '+'? (natural as n) '/' (positive as d)
  | ('-'  natural as n) '/' (positive as d)
      { RATIONAL (n,d) }
  | '+'? (natural as i) ('.' (digit+ as f))? (['e' 'E'] ('+'? (natural as e)))?
  | ('-'  natural as i) ('.' (digit+ as f))? (['e' 'E'] ('+'? (natural as e)))?
  | '+'? (natural as i) ('.' (digit+ as f))? (['e' 'E'] ('-'   natural as e))?
  | ('-'  natural as i) ('.' (digit+ as f))? (['e' 'E'] ('-'   natural as e))?
      { REAL (i,f,e) }
  | "/*/"
      { SLASH_STAR_SLASH }
  | "/*"
      { comment_start_loc := loc lexbuf; comment_block lexbuf; token lexbuf }
  | "%"
      { comment_start_loc := loc lexbuf; comment_line  lexbuf; token lexbuf }
  | ","
      { COMMA }
  | "("
      { LEFTPAR }
  | ")"
      { RIGHTPAR }
  | "["
      { LEFTSQ }
  | "]"
      { RIGHTSQ }
  | ":"
      { COLON }
  | "-->"
      { LONGARROW }
  | "<="
      { LARROW }
  | "=>"
      { RARROW }
  | "<=>"
      { LRARROW }
  | "<~>"
      { NLRARROW }
  | "~&"
      { NAMP }
  | "~|"
      { NBAR }
  | "~"
      { TILDE }
  | "."
      { DOT }
  | "="
      { EQUAL }
  | "!="
      { NEQUAL }
  | "*"
      { STAR }
  | ">"
      { GT }
  | "!>"
      { PI }
  | "!"
      { BANG }
  | "?"
      { QUES }
  | eof
      { EOF }
  | _ as c
      { raise (IllegalCharacter c) }

and comment_block = parse
  | "*/"
      { () }
  | newline
      { newline lexbuf; comment lexbuf }
  | eof
      { raise (Loc.Located (!comment_start_loc, UnterminatedComment)) }
  | _
      { comment lexbuf }

and comment_line = parse
  | newline
      { newline lexbuf; () }
  | eof
      { () }
  | _
      { comment lexbuf }

{
  let with_location f lb =
    if Debug.test_flag Debug.stack_trace then f lb else
    try f lb with
      | Loc.Located _ as e -> raise e
      | e -> raise (Loc.Located (loc lb, e))

  let read_channel env path file c =
    let lb = Lexing.from_channel c in
    Loc.set_file file lb;
    let ast = with_location (tptp_file token) lb in
    tptp_typing env path ast

  let () = Env.register_format "why" ["why"] read_channel
}

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. test"
End:
*)

