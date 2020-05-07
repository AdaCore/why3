(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* This is a copy of [src/parser/lexer.mll], with the following minor changes:

* [open Parser] -> [open Cfg_tokens]

* addition of keywords:

  [
    "cfg", CFG;
    "goto", GOTO;
  ]

*)

{
  open Why3
  open Cfg_tokens

  let keywords = Hashtbl.create 97
  let () =
    List.iter
      (fun (x,y) -> Hashtbl.add keywords x y)
      (* keep the following files synchronized:

         doc/ext/why3.py
         src/trywhy3/mode-why3.js
         src/why3doc/doc_lexer.mll
         share/emacs/why3.el
         share/vim/syntax/why3.vim
       *)
      [
    "cfg", CFG;
    "goto", GOTO;
        "abstract", ABSTRACT;
        "absurd", ABSURD;
        "alias", ALIAS;
        "any", ANY;
        "as", AS;
        "assert", ASSERT;
        "assume", ASSUME;
        "at", AT;
        "axiom", AXIOM;
        "begin", BEGIN;
        "break", BREAK;
        "by", BY;
        "check", CHECK;
        "clone", CLONE;
        "coinductive", COINDUCTIVE;
        "constant", CONSTANT;
        "continue", CONTINUE;
        "diverges", DIVERGES;
        "do", DO;
        "done", DONE;
        "downto", DOWNTO;
        "else", ELSE;
        "end", END;
        "ensures", ENSURES;
        "epsilon", EPSILON;
        "exception", EXCEPTION;
        "exists", EXISTS;
        "export", EXPORT;
        "false", FALSE;
        "float", FLOAT; (* contextual *)
        "for", FOR;
        "forall", FORALL;
        "fun", FUN;
        "function", FUNCTION;
        "ghost", GHOST;
        "goal", GOAL;
        "if", IF;
        "import", IMPORT;
        "in", IN;
        "inductive", INDUCTIVE;
        "invariant", INVARIANT;
        "label", LABEL;
        "lemma", LEMMA;
        "let", LET;
        "match", MATCH;
        "meta", META;
        "module", MODULE;
        "mutable", MUTABLE;
        "not", NOT;
        "old", OLD;
        "partial", PARTIAL;
        "predicate", PREDICATE;
        "private", PRIVATE;
        "pure", PURE;
        "raise", RAISE;
        "raises", RAISES;
        "range", RANGE; (* contextual *)
        "reads", READS;
        "rec", REC;
        "ref", REF; (* contextual *)
        "requires", REQUIRES;
        "return", RETURN;
        "returns", RETURNS;
        "scope", SCOPE;
        "so", SO;
        "then", THEN;
        "theory", THEORY;
        "to", TO;
        "true", TRUE;
        "try", TRY;
        "type", TYPE;
        "use", USE;
        "val", VAL;
        "variant", VARIANT;
        "while", WHILE;
        "with", WITH;
        "writes", WRITES;
      ]
}

let space = [' ' '\t' '\r']
let quote = '\''

let bin     = ['0' '1']
let oct     = ['0'-'7']
let dec     = ['0'-'9']
let hex     = ['0'-'9' 'a'-'f' 'A'-'F']

let bin_sep = ['0' '1' '_']
let oct_sep = ['0'-'7' '_']
let dec_sep = ['0'-'9' '_']
let hex_sep = ['0'-'9' 'a'-'f' 'A'-'F' '_']

let lalpha = ['a'-'z']
let ualpha = ['A'-'Z']
let alpha  = ['a'-'z' 'A'-'Z']

let suffix = (alpha | quote* dec_sep)* quote*
let lident = ['a'-'z' '_'] suffix
let uident = ['A'-'Z'] suffix

let core_suffix = quote alpha suffix
let core_lident = lident core_suffix+
let core_uident = uident core_suffix+

let op_char_1 = ['=' '<' '>' '~']
let op_char_2 = ['+' '-']
let op_char_3 = ['*' '/' '\\' '%']
let op_char_4 = ['!' '$' '&' '?' '@' '^' '.' ':' '|' '#']
let op_char_34 = op_char_3 | op_char_4
let op_char_234 = op_char_2 | op_char_34
let op_char_1234 = op_char_1 | op_char_234

let op_char_pref = ['!' '?']

rule token = parse
  | "[##" space* ("\"" ([^ '\010' '\013' '"' ]* as file) "\"")?
    space* (dec+ as line) space* (dec+ as char) space* "]"
      { Lexlib.update_loc lexbuf file (int_of_string line) (int_of_string char);
        token lexbuf }
  | "[#" space* "\"" ([^ '\010' '\013' '"' ]* as file) "\""
    space* (dec+ as line) space* (dec+ as bchar) space*
    (dec+ as echar) space* "]"
      { POSITION (Loc.user_position file (int_of_string line)
                 (int_of_string bchar) (int_of_string echar)) }
  | "[@" space* ([^ ' ' '\n' ']']+ (' '+ [^ ' ' '\n' ']']+)* as lbl) space* ']'
      { ATTRIBUTE lbl }
  | '\n'
      { Lexing.new_line lexbuf; token lexbuf }
  | space+
      { token lexbuf }
  | '_'
      { UNDERSCORE }
  | lident as id
      { try Hashtbl.find keywords id with Not_found -> LIDENT id }
  | core_lident as id
      { CORE_LIDENT id }
  | uident as id
      { UIDENT id }
  | core_uident as id
      { CORE_UIDENT id }
  | dec dec_sep* as s
      { INTEGER Number.(int_literal ILitDec ~neg:false (Lexlib.remove_underscores s)) }
  | '0' ['x' 'X'] (hex hex_sep* as s)
      { INTEGER Number.(int_literal ILitHex ~neg:false (Lexlib.remove_underscores s)) }
  | '0' ['o' 'O'] (oct oct_sep* as s)
      { INTEGER Number.(int_literal ILitOct ~neg:false (Lexlib.remove_underscores s)) }
  | '0' ['b' 'B'] (bin bin_sep* as s)
      { INTEGER Number.(int_literal ILitBin ~neg:false (Lexlib.remove_underscores s)) }
  | (dec+ as i) ".."
      { Lexlib.backjump lexbuf 2; INTEGER Number.(int_literal ILitDec ~neg:false i) }
  | '0' ['x' 'X'] (hex+ as i) ".."
      { Lexlib.backjump lexbuf 2; INTEGER Number.(int_literal ILitHex ~neg:false i) }
  | (dec+ as i)     ("" as f)    ['e' 'E'] (['-' '+']? dec+ as e)
  | (dec+ as i) '.' (dec* as f) (['e' 'E'] (['-' '+']? dec+ as e))?
  | (dec* as i) '.' (dec+ as f) (['e' 'E'] (['-' '+']? dec+ as e))?
      { REAL (Number.real_literal ~radix:10 ~neg:false ~int:i ~frac:f ~exp:(Opt.map Lexlib.remove_leading_plus e)) }
  | '0' ['x' 'X'] (hex+ as i) ("" as f) ['p' 'P'] (['-' '+']? dec+ as e)
  | '0' ['x' 'X'] (hex+ as i) '.' (hex* as f)
        (['p' 'P'] (['-' '+']? dec+ as e))?
  | '0' ['x' 'X'] (hex* as i) '.' (hex+ as f)
        (['p' 'P'] (['-' '+']? dec+ as e))?
      { REAL (Number.real_literal ~radix:16 ~neg:false ~int:i ~frac:f ~exp:(Opt.map Lexlib.remove_leading_plus e)) }
  | "(*)"
      { Lexlib.backjump lexbuf 2; LEFTPAR }
  | "(*"
      { Lexlib.comment lexbuf; token lexbuf }
  | "'" (lalpha suffix as id)
      { QUOTE_LIDENT id }
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
  | ":"
      { COLON }
  | ";"
      { SEMICOLON }
  | "->"
      { ARROW }
  | "->'"
      { Lexlib.backjump lexbuf 1; ARROW }
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
  | "."
      { DOT }
  | ".."
      { DOTDOT }
  | "&"
      { AMP }
  | "|"
      { BAR }
  | "<"
      { LT }
  | ">"
      { GT }
  | "<>"
      { LTGT }
  | "="
      { EQUAL }
  | "-"
      { MINUS }
  | "["
      { LEFTSQ }
  | "]"
      { RIGHTSQ }
  | "]" (quote+ as s)
      { RIGHTSQ_QUOTE s }
  | ")" ('\'' alpha suffix core_suffix* as s)
      { RIGHTPAR_QUOTE s }
  | ")" ('_' alpha suffix core_suffix* as s)
      { RIGHTPAR_USCORE s }
  | op_char_pref op_char_4* quote* as s
      { OPPREF s }
  | op_char_1234* op_char_1 op_char_1234* quote* as s
      { OP1 s }
  | op_char_234* op_char_2 op_char_234* quote* as s
      { OP2 s }
  | op_char_34* op_char_3 op_char_34* quote* as s
      { OP3 s }
  | op_char_4+ as s
      { OP4 s }
  | "\""
      { STRING (Lexlib.string lexbuf) }
  | eof
      { EOF }
  | _ as c
      { Lexlib.illegal_character c lexbuf }

{

  let () = Exn_printer.register (fun fmt exn -> match exn with
  | Cfg_parser.Error -> Format.fprintf fmt "syntax error"
  | _ -> raise exn)

  let parse_channel file c =
    let lb = Lexing.from_channel c in
    Loc.set_file file lb;
    try
      Cfg_parser.cfgfile token lb
    with
      Cfg_parser.Error as e -> raise (Loc.Located (Loc.extract (lb.lex_start_p,lb.lex_curr_p),e))

}
