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

{
  open Lexing
  open Mc_ast
  open Mc_parser

  exception Lexing_error of string

  let () = Why3.Exn_printer.register (fun fmt exn -> match exn with
  | Lexing_error s -> Format.fprintf fmt "syntax error: %s" s
  | _ -> raise exn)

  type state = Code | OneLineSpec | MultiLineSpec
  let state = ref Code

  let id_or_kwd =
    let h1 = Hashtbl.create 32 in
    List.iter (fun (s, tok) -> Hashtbl.add h1 s tok)
      ["if", IF; "else", ELSE;
       "return", RETURN; "while", WHILE;
       "for", FOR; "break", BREAK;
       "void", VOID; "int", INT; "scanf", SCANF;
      ];
    let h2 = Hashtbl.create 32 in
    List.iter (fun (s, tok) -> Hashtbl.add h2 s tok)
      ["true", TRUE; "false", FALSE;
       "forall", FORALL; "exists", EXISTS; "then", THEN; "let", LET; "in", LET;
       "at", AT; "old", OLD;
       "invariant", INVARIANT; "variant", VARIANT;
       "assert", ASSERT; "assume", ASSUME; "check", CHECK;
       "lemma", LEMMA; "axiom", AXIOM; "goal", GOAL;
       "requires", REQUIRES; "ensures", ENSURES;
       "label", LABEL; "function", FUNCTION; "predicate", PREDICATE;
      ];
    fun s ->
      try Hashtbl.find h1 s with Not_found ->
      if !state = Code then IDENT s else
      try Hashtbl.find h2 s with Not_found -> IDENT s

  let string_buffer = Buffer.create 1024

}

let letter = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let ident = letter (letter | digit | '_')*
let integer = ['0'-'9']+
let space = ' ' | '\t'
let comment = "//" [^'@''\n'] [^'\n']*

rule next_token = parse
  | '\n'    { new_line lexbuf;
              if !state = OneLineSpec then state := Code;
              next_token lexbuf }
  | space+  { next_token lexbuf }
  | "//\n"  { new_line lexbuf; next_token lexbuf }
  | comment { next_token lexbuf }
  | '#' space* "include" space* '<' ([^ '>' '\n']* as file) '>' space* '\n'
            { new_line lexbuf; INCLUDE file }
  | "/*"    { comment lexbuf }
  | "*/"    { if !state <> MultiLineSpec
              then raise (Lexing_error "no comment to be closed");
              state := Code;
              next_token lexbuf }
  | "//@"   { state := OneLineSpec; next_token lexbuf }
  | "/*@"   { state := MultiLineSpec; next_token lexbuf }
  | "@"     { if !state <> MultiLineSpec
              then raise (Lexing_error "illegal character '@'");
              next_token lexbuf }
  | ident as id
            { id_or_kwd id }
  | '+'     { PLUS }
  | '-'     { MINUS }
  | '*'     { TIMES }
  | "/"     { DIV }
  | '%'     { MOD }
  | '='     { EQUAL }
  | "+="    { PLUSEQUAL }
  | "-="    { MINUSEQUAL }
  | "*="    { TIMESEQUAL }
  | "/="    { DIVEQUAL }
  | "=="    { CMP Beq }
  | "!="    { CMP Bneq }
  | "<"     { CMP Blt }
  | "<="    { CMP Ble }
  | ">"     { CMP Bgt }
  | ">="    { CMP Bge }
  | '('     { LEFTPAR }
  | ')'     { RIGHTPAR }
  | '['     { LEFTSQ }
  | ']'     { RIGHTSQ }
  | '{'     { LBRC }
  | '}'     { RBRC }
  | ','     { COMMA }
  | ':'     { COLON }
  | ';'     { SEMICOLON }
  | "&&"    { AND }
  | "||"    { OR }
  | "!"     { NOT }
  | "++"    { PLUSPLUS }
  | "--"    { MINUSMINUS }
  | '&'     { AMPERSAND }
  (* logic symbols *)
  | "->"    { ARROW }
  | "<-"    { LARROW }
  | "<->"   { LRARROW }
  | "."     { DOT }
  | integer as s
            { INTEGER s }
  | '"'     { STRING (string lexbuf) }
  | eof     { EOF }
  | _ as c  { raise (Lexing_error ("illegal character: " ^ String.make 1 c)) }

(* skip a comment, then resume next_token *)
and comment = parse
  | "*/" { next_token lexbuf }
  | '\n' { new_line lexbuf; comment lexbuf }
  | _    { comment lexbuf }
  | eof  { raise (Lexing_error "unterminated comment") }

and string = parse
  | '"'
      { let s = Buffer.contents string_buffer in
	Buffer.reset string_buffer;
	s }
  | "\\n"
      { Buffer.add_char string_buffer '\n';
	string lexbuf }
  | "\\\""
      { Buffer.add_char string_buffer '"';
	string lexbuf }
  | _ as c
      { Buffer.add_char string_buffer c;
	string lexbuf }
  | eof
      { raise (Lexing_error "unterminated string") }

{

  let parse file c =
    let lb = Lexing.from_channel c in
    Why3.Loc.set_file file lb;
    Why3.Loc.with_location (Mc_parser.file next_token) lb

  (* Entries for transformations: similar to lexer.mll *)
  let build_parsing_function entry lb = Why3.Loc.with_location (entry next_token) lb

  let parse_term = build_parsing_function Mc_parser.term_eof

  let parse_term_list = build_parsing_function Mc_parser.term_comma_list_eof

  let parse_list_ident = build_parsing_function Mc_parser.ident_comma_list_eof

}
