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
  open Lexing
  open Mc_ast
  open Mc_parser

  exception Lexing_error of string

  let () = Why3.Exn_printer.register (fun fmt exn -> match exn with
  | Lexing_error s -> Format.fprintf fmt "syntax error: %s" s
  | _ -> raise exn)

  let id_or_kwd =
    let h = Hashtbl.create 32 in
    List.iter (fun (s, tok) -> Hashtbl.add h s tok)
      ["if", IF; "else", ELSE;
       "return", RETURN; "while", WHILE;
       "for", FOR; "break", BREAK;
       "void", VOID; "int", INT; "scanf", SCANF;
       (* annotations *)
       "true", TRUE; "false", FALSE;
       "forall", FORALL; "exists", EXISTS; "then", THEN; "let", LET; "in", LET;
       "at", AT; "old", OLD;
      ];
   fun s -> try Hashtbl.find h s with Not_found -> IDENT s

  let annotation =
    let h = Hashtbl.create 32 in
    List.iter (fun (s, tok) -> Hashtbl.add h s tok)
      ["invariant", INVARIANT; "variant", VARIANT;
       "assert", ASSERT; "assume", ASSUME; "check", CHECK;
       "requires", REQUIRES; "ensures", ENSURES;
       "label", LABEL; "function", FUNCTION; "predicate", PREDICATE;
      ];
    fun s -> try Hashtbl.find h s with Not_found ->
      raise (Lexing_error ("no such annotation '" ^ s ^ "'"))

  let string_buffer = Buffer.create 1024

}

let letter = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let ident = letter (letter | digit | '_')*
let integer = ['0'-'9']+
let space = ' ' | '\t'
let comment = "//" [^'@''\n'] [^'\n']*

rule next_token = parse
  | '\n'    { new_line lexbuf; next_token lexbuf }
  | (space | comment)+
            { next_token lexbuf }
  | '#' space* "include" space* '<' ([^ '>' '\n']* as file) '>' space* '\n'
            { new_line lexbuf; INCLUDE file }
  | "/*"    { comment lexbuf }
  | "\\" space* '\n' space* "//@"?
            { next_token lexbuf }
  | "//@" space* (ident as id)
            { annotation id }
  | "//@"    { raise (Lexing_error "expecting an annotation") }
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

}



