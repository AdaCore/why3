(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

{
  open Format
  open Lexing
  open Tptp_ast
  open Tptp_parser

  open Why3

  (* lexical errors *)

  exception IllegalCharacter of char
  exception UnterminatedComment
(* dead code
  exception UnterminatedString
*)
  exception UnknownDDW of string
  exception UnknownDW of string

  let () = Exn_printer.register (fun fmt e -> match e with
    | IllegalCharacter c -> fprintf fmt "illegal character %c" c
    | UnterminatedComment -> fprintf fmt "unterminated comment"
(* dead code
    | UnterminatedString -> fprintf fmt "unterminated string"
*)
    | UnknownDDW s -> fprintf fmt "unknown system_word %s" s
    | UnknownDW s -> fprintf fmt "unknown defined_word %s" s
    | _ -> raise e)

  let defwords = Hashtbl.create 97
  let () = List.iter (fun (x,y) -> Hashtbl.add defwords x y) [
    "ceiling", DWORD (DF DFceil);
    "difference", DWORD (DF DFdiff);
    "distinct", DWORD (DP DPdistinct);
    "false", DWORD (DP DPfalse);
    "floor", DWORD (DF DFfloor);
    "greater", DWORD (DP DPgreater);
    "greatereq", DWORD (DP DPgreatereq);
    "i", DWORD (DT DTuniv);
    "int", DWORD (DT DTint);
    "is_int", DWORD (DP DPisint);
    "is_rat", DWORD (DP DPisrat);
    "ite_f", ITE_F;
    "ite_t", ITE_T;
    "iType", DWORD (DT DTuniv);
    "let_tt", LET_TT;
    "let_ft", LET_FT;
    "let_tf", LET_TF;
    "let_ff", LET_FF;
    "less", DWORD (DP DPless);
    "lesseq", DWORD (DP DPlesseq);
    "o", DWORD (DT DTprop);
    "oType", DWORD (DT DTprop);
    "product", DWORD (DF DFprod);
    "quotient", DWORD (DF DFquot);
    "quotient_e", DWORD (DF DFquot_e);
    "quotient_t", DWORD (DF DFquot_t);
    "quotient_f", DWORD (DF DFquot_f);
    "rat", DWORD (DT DTrat);
    "real", DWORD (DT DTreal);
    "remainder_e", DWORD (DF DFrem_e);
    "remainder_t", DWORD (DF DFrem_t);
    "remainder_f", DWORD (DF DFrem_f);
    "round", DWORD (DF DFround);
    "sum", DWORD (DF DFsum);
    "to_int", DWORD (DF DFtoint);
    "to_rat", DWORD (DF DFtorat);
    "to_real", DWORD (DF DFtoreal);
    "true", DWORD (DP DPtrue);
    "truncate", DWORD (DF DFtrunc);
    "tType", DWORD (DT DTtype);
    "uminus", DWORD (DF DFumin);
  ]

  let keywords = Hashtbl.create 97
  let () = List.iter (fun (x,y) -> Hashtbl.add keywords x y) [
    "assumption", ASSUMPTION;
    "axiom", AXIOM;
    "cnf", CNF;
    "conjecture", CONJECTURE;
    "corollary", COROLLARY;
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
  | '\'' (lword as id) '\''
      { LWORD id }
  | '\'' sq_char+ '\'' as sq
      { SINGLE_QUOTED sq }
  | '"' (do_char* as dob) '"'
      { DISTINCT_OBJECT dob }
  | "$_"
      { DWORD (DT DTdummy) }
  | '$' (lword as id)
      { try Hashtbl.find defwords id with Not_found -> raise (UnknownDW id) }
  | "$$" (lword as id)
      { raise (UnknownDDW id) }
  | '+'? (natural as s)
      { INTPOSNUM s }
  | '-'  (natural as s)
      { INTNEGNUM s }
  | '+'? (natural as n) '/' (positive as d)
      { RATPOSNUM (n,d) }
  | '-'  (natural as n) '/' (positive as d)
      { RATNEGNUM (n,d) }
  | '+'? (natural as i) ('.' (digit+ as f))? (['e' 'E'] ('+'? (natural as e)))?
  | '+'? (natural as i) ('.' (digit+ as f))? (['e' 'E'] ('-'   natural as e))?
      { REALPOSNUM (i,f,e) }
  | '-'  (natural as i) ('.' (digit+ as f))? (['e' 'E'] ('+'? (natural as e)))?
  | '-'  (natural as i) ('.' (digit+ as f))? (['e' 'E'] ('-'   natural as e))?
      { REALNEGNUM (i,f,e) }
  | "/*/"
      { SLASH_STAR_SLASH }
  | "/*"
      { comment_start_loc := loc lexbuf; comment_block lexbuf; token lexbuf }
  | "%"
      { comment_start_loc := loc lexbuf; comment_line  lexbuf; token lexbuf }
  | "."
      { DOT }
  | ","
      { COMMA }
  | ":"
      { COLON }
  | "("
      { LEFTPAR }
  | ")"
      { RIGHTPAR }
  | "["
      { LEFTSQ }
  | "]"
      { RIGHTSQ }
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
  | "&"
      { AMP }
  | "|"
      { BAR }
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
      { newline lexbuf; comment_block lexbuf }
  | eof
      { raise (Loc.Located (!comment_start_loc, UnterminatedComment)) }
  | _
      { comment_block lexbuf }

and comment_line = parse
  | newline
      { newline lexbuf; () }
  | eof
      { () }
  | _
      { comment_line lexbuf }

{

  let read_channel env path file c =
    let lb = Lexing.from_channel c in
    Loc.set_file file lb;
    let ast = Loc.with_location (tptp_file token) lb in
    Tptp_typing.typecheck env path ast

  let () = Env.register_format Env.base_language "tptp" ["p";"ax"] read_channel
    ~desc:"TPTP format (CNF FOF FOFX TFF)"

}

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. test"
End:
*)

