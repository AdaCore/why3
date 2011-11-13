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

  (* lexical errors *)

  exception IllegalCharacter of char
  exception UnterminatedComment
  exception UnterminatedString

  let () = Exn_printer.register (fun fmt e -> match e with
    | IllegalCharacter c -> fprintf fmt "illegal character %c" c
    | UnterminatedComment -> fprintf fmt "unterminated comment"
    | UnterminatedString -> fprintf fmt "unterminated string"
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

  let string_start_loc = ref Loc.dummy_position
  let string_buf = Buffer.create 1024

  let comment_start_loc = ref Loc.dummy_position

  let char_for_backslash = function
    | 'n' -> '\n'
    | 't' -> '\t'
    | c -> c

  let update_loc lexbuf file line chars =
    let pos = lexbuf.lex_curr_p in
    let new_file = match file with None -> pos.pos_fname | Some s -> s in
    lexbuf.lex_curr_p <- { pos with
      pos_fname = new_file;
      pos_lnum = int_of_string line;
      pos_bol = pos.pos_cnum - int_of_string chars;
    }

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
let negative = '-' natural

rule token = parse
  | newline
      { newline lexbuf; token lexbuf }
  | space+
      { token lexbuf }
  | lword as id
      { try Hashtbl.find keywords id with Not_found -> LWORD id }
  | uword as id
      { UWORD id }
  | '+'? (natural as s)
      { INTEGER s }
  | negative as s
      { INTEGER s }
  | '+'? (natural as n) '/' (natural as d)
      { RATIONAL (n,d) }
  | (negative as n) '/' (natural as d)
      { RATIONAL (n,d) }


  |  
  | nzero 
  | ['0'-'9'] ['0'-'9' '_']* as s
      { INTEGER (IConstDecimal (remove_underscores s)) }
  | '0' ['x' 'X'] (['0'-'9' 'A'-'F' 'a'-'f']['0'-'9' 'A'-'F' 'a'-'f' '_']* as s)
      { INTEGER (IConstHexa (remove_underscores s)) }
  | '0' ['o' 'O'] (['0'-'7'] ['0'-'7' '_']* as s)
      { INTEGER (IConstOctal (remove_underscores s)) }
  | '0' ['b' 'B'] (['0'-'1'] ['0'-'1' '_']* as s)
      { INTEGER (IConstBinary (remove_underscores s)) }
  | (digit+ as i) ("" as f) ['e' 'E'] (['-' '+']? digit+ as e)
  | (digit+ as i) '.' (digit* as f) (['e' 'E'] (['-' '+']? digit+ as e))?
  | (digit* as i) '.' (digit+ as f) (['e' 'E'] (['-' '+']? digit+ as e))?
      { FLOAT (RConstDecimal (i, f, Util.option_map remove_leading_plus e)) }
  | '0' ['x' 'X'] ((hexadigit* as i) '.' (hexadigit+ as f)
                  |(hexadigit+ as i) '.' (hexadigit* as f)
                  |(hexadigit+ as i) ("" as f))
    ['p' 'P'] (['-' '+']? digit+ as e)
      { FLOAT (RConstHexa (i, f, remove_leading_plus e)) }
  | "(*)"
      { LEFTPAR_STAR_RIGHTPAR }
  | "(*"
      { comment_start_loc := loc lexbuf; comment lexbuf; token lexbuf }
  | "'"
      { QUOTE }
  | ","
      { COMMA }
  | "("
      { LEFTPAR }
  | ")"
      { RIGHTPAR }
  | "{"
      { LEFTBRC }
  | "}"
      { RIGHTBRC }
  | "{|"
      { LEFTREC }
  | "|}"
      { RIGHTREC }
  | ":"
      { COLON }
  | ";"
      { SEMICOLON }
  | "->"
      { ARROW }
  | "<-"
      { LARROW }
  | "<->"
      { LRARROW }
  | "&&"
      { AMPAMP }
  | "||"
      { BARBAR }
  | "/\\"
      { AND }
  | "\\/"
      { OR }
   | "\\"
      { LAMBDA }
  | "\\?"
      { PRED }
  | "\\!"
      { FUNC }
  | "."
      { DOT }
  | "|"
      { BAR }
  | "="
      { EQUAL }
  | "<>"
      { LTGT }
  | "["
      { LEFTSQ }
  | "]"
      { RIGHTSQ }
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
      { string_start_loc := loc lexbuf; STRING (string lexbuf) }
  | eof
      { EOF }
  | _ as c
      { raise (IllegalCharacter c) }

and comment = parse
  | "(*)"
      { comment lexbuf }
  | "*)"
      { () }
  | "(*"
      { comment lexbuf; comment lexbuf }
  | newline
      { newline lexbuf; comment lexbuf }
  | eof
      { raise (Loc.Located (!comment_start_loc, UnterminatedComment)) }
  | _
      { comment lexbuf }

and string = parse
  | "\""
      { let s = Buffer.contents string_buf in
        Buffer.clear string_buf;
        s }
  | "\\" (_ as c)
      { Buffer.add_char string_buf (char_for_backslash c); string lexbuf }
  | newline
      { newline lexbuf; Buffer.add_char string_buf '\n'; string lexbuf }
  | eof
      { raise (Loc.Located (!string_start_loc, UnterminatedString)) }
  | _ as c
      { Buffer.add_char string_buf c; string lexbuf }

{
  let with_location f lb =
    if Debug.test_flag Debug.stack_trace then f lb else
    try f lb with
      | Loc.Located _ as e -> raise e
      | e -> raise (Loc.Located (loc lb, e))

  let parse_logic_file env path lb =
    pre_logic_file token (Lexing.from_string "") env path;
    with_location (logic_file token) lb

  let parse_program_file = with_location (program_file token)

  let token_counter lb =
    let rec loop in_annot a p =
      match token lb with
        | LEFTBRC -> assert (not in_annot); loop true a p
        | RIGHTBRC -> assert in_annot; loop false a p
        | EOF -> assert (not in_annot); (a,p)
        | _ ->
            if in_annot
            then loop in_annot (a+1) p
            else loop in_annot a (p+1)
    in
    loop false 0 0 
 
  let read_channel env path file c =
    let lb = Lexing.from_channel c in
    Loc.set_file file lb;
    parse_logic_file env path lb

  let () = Env.register_format "why" ["why"] read_channel

}

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. test"
End:
*)

