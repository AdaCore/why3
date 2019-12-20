(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

{
  open Why3
  open Ada_parser

  let keywords = Hashtbl.create 97
  let () =
    List.iter
      (fun (x,y) -> Hashtbl.add keywords x y)
      [
        "all", ALL; (* Ada specific *)
        "and", AND;  (* Ada specific *)
        "as", AS;
        "by", BY;
        "else", ELSE;
        "end", END;
        "false", FALSE;
        "float", FLOAT;
        "for", FOR; (* Ada specific *)
        "if", IF;
        "in", IN;
        "let", LET;
        "match", MATCH;
        "not", NOT;
        "or", OR; (* Ada specific *)
        "range", RANGE;
        "so", SO;
        "some", SOME; (* Ada specific *)
        "then", THEN;
        "true", TRUE;
        "with", WITH;
        (* programs *)
        "at", AT;
        "begin", BEGIN;
        "fun", FUN;
        "ghost", GHOST;
        "old", OLD;
        "ref", REF;
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

let suffix = (alpha | dec_sep)*
let lident = ['a'-'z' '_'] suffix
let uident = ['A'-'Z'] suffix

let core_suffix = alpha suffix
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
  | quote { QUOTE }
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
  | "=>"
      { DARROW }
  | "->"
      { ARROW }
  | "->'"
      { Lexlib.backjump lexbuf 1; ARROW }
  | "<-"
      { LARROW }
  | "<->"
      { LRARROW }
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
  | "/="
      { LTGT } (* Ada specific *)
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
  | eof
      { EOF }
  | _ as c
      { Lexlib.illegal_character c lexbuf }

{

  open Why3

  let debug = Debug.register_info_flag "print_modules"
    ~desc:"Print@ program@ modules@ after@ typechecking."

  exception Error of string option

  let () = Exn_printer.register (fun fmt exn -> match exn with
  (* This ad hoc switch allows to not edit the automatically generated
     handcrafted.messages in ad hoc ways. *)
  | Error None -> Format.fprintf fmt "syntax error"
  | Error (Some s) -> Format.fprintf fmt "syntax error:\n %s" s
  | _ -> raise exn)

  let build_parsing_function (parser_entry: Lexing.position -> 'a) lb =
    (* This records the last token which was read (for error messages) *)
    let last = ref EOF in
    let module I = Ada_parser.MenhirInterpreter in
    let checkpoint = parser_entry lb.Lexing.lex_curr_p
    and supplier =
      I.lexer_lexbuf_to_supplier (fun x -> let t = token x in last := t; t) lb
    and succeed t = t
    and fail _ =
      let text = Lexing.lexeme lb in
      (* TODO/FIXME: ad-hoc fix for TryWhy3/Str incompatibility *)
      let s = (* TODO changed if Strings.has_prefix "/trywhy3_input." fname
        then None
        else Report.report text !last checkpoint*) Some text in
      (* Typing.close_file is supposedly done at the end of the file in
         parsing.mly. If there is a syntax error, we still need to close it (to
         be able to reload). *)
      Loc.with_location (fun _x -> raise (Error s)) lb
    in
    I.loop_handle succeed fail supplier checkpoint

  let parse_term nt lb =
    Ada_nametable.set_naming_table nt;
    build_parsing_function Ada_parser.Incremental.term_eof lb

  let parse_term_list nt lb =
    Ada_nametable.set_naming_table nt;
    build_parsing_function Ada_parser.Incremental.term_comma_list_eof lb

  let parse_qualid lb = build_parsing_function Ada_parser.Incremental.qualid_eof lb

  let parse_list_ident lb = build_parsing_function Ada_parser.Incremental.ident_comma_list_eof lb

  let parse_list_qualid lb = build_parsing_function Ada_parser.Incremental.qualid_comma_list_eof lb

}
