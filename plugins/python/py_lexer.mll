(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

{
  open Lexing
  open Py_ast
  open Py_parser

  exception Lexing_error of string

  let () = Why3.Exn_printer.register (fun fmt exn -> match exn with
  | Lexing_error s -> Format.fprintf fmt "syntax error: %s" s
  | _ -> raise exn)

  let id_or_kwd =
    let h = Hashtbl.create 32 in
    List.iter (fun (s, tok) -> Hashtbl.add h s tok)
      ["def", DEF; "if", IF; "else", ELSE; "elif", ELIF;
       "return", RETURN; "while", WHILE;
       "for", FOR; "in", IN;
       "and", AND; "or", OR; "not", NOT;
       "True", TRUE; "False", FALSE; "None", NONE;
       "from", FROM; "import", IMPORT; "break", BREAK;
       (* annotations *)
       "forall", FORALL; "exists", EXISTS; "then", THEN; "let", LET;
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

  let stack = ref [0]  (* indentation stack *)

  let rec unindent n = match !stack with
    | m :: _ when m = n -> []
    | m :: st when m > n -> stack := st; END :: unindent n
    | _ -> raise (Lexing_error "bad indentation")

  let update_stack n =
    match !stack with
    | m :: _ when m < n ->
      stack := n :: !stack;
      [NEWLINE; BEGIN]
    | _ ->
      NEWLINE :: unindent n

}

let letter = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let ident = letter (letter | digit | '_')*
let integer = ['0'-'9']+
let space = ' ' | '\t'
let comment = "#" [^'@''\n'] [^'\n']*

rule next_tokens = parse
  | '\n'    { new_line lexbuf; update_stack (indentation lexbuf) }
  | (space | comment)+
            { next_tokens lexbuf }
  | "\\" space* '\n' space* "#@"?
            { next_tokens lexbuf }
  | "#@" space* (ident as id)
            { [annotation id] }
  | "#@"    { raise (Lexing_error "expecting an annotation") }
  | ident as id
            { [id_or_kwd id] }
  | '+'     { [PLUS] }
  | '-'     { [MINUS] }
  | '*'     { [TIMES] }
  | "//"    { [DIV] }
  | '%'     { [MOD] }
  | '='     { [EQUAL] }
  | "=="    { [CMP Beq] }
  | "!="    { [CMP Bneq] }
  | "<"     { [CMP Blt] }
  | "<="    { [CMP Ble] }
  | ">"     { [CMP Bgt] }
  | ">="    { [CMP Bge] }
  | '('     { [LEFTPAR] }
  | ')'     { [RIGHTPAR] }
  | '['     { [LEFTSQ] }
  | ']'     { [RIGHTSQ] }
  | ','     { [COMMA] }
  | ':'     { [COLON] }
  (* logic symbols *)
  | "->"    { [ARROW] }
  | "<-"    { [LARROW] }
  | "<->"   { [LRARROW] }
  | "."     { [DOT] }
  | integer as s
            { [INTEGER s] }
  | '"'     { [STRING (string lexbuf)] }
  | eof     { [EOF] }
  | _ as c  { raise (Lexing_error ("illegal character: " ^ String.make 1 c)) }

(* count the indentation, i.e. the number of space characters from bol *)
and indentation = parse
  | (space | comment)* '\n'
      (* skip empty lines *)
      { new_line lexbuf; indentation lexbuf }
  | space* as s
      { String.length s }

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

  let next_token =
    let tokens = Queue.create () in
    fun lb ->
      if Queue.is_empty tokens then begin
	let l = next_tokens lb in
	List.iter (fun t -> Queue.add t tokens) l
      end;
      Queue.pop tokens

  let parse file c =
    let lb = Lexing.from_channel c in
    Why3.Loc.set_file file lb;
    stack := [0];  (* reinitialise indentation stack *)
    Why3.Loc.with_location (Py_parser.file next_token) lb

}



