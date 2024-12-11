(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

{
  type sexp =
    | Atom of string
    | List of sexp list

  let rec exists p sexp =
    p sexp || match sexp with
    | Atom _ -> false
    | List l -> List.exists (exists p) l

  exception Error

(* The parsing state is comprised of a stack and an optional result. During scanning,
   the stack contains the values of all currently open s-expressions. After scanning
   one top-level s-expression, this s-expression is the result. *)

  let add x stack =
    match stack with
    | [] ->
        [x] :: stack
    | l :: stack ->
        (x::l) :: stack

  let start_list stack =
    [] :: stack

  let end_list stack =
    match stack with
    | l :: stack ->
        add (List (List.rev l)) stack
    | [] -> raise Error

  let get_sexp stack =
    match stack with
    | [[x]] -> x
    | _ -> raise Error

  let get_sexp_list stack =
    match stack with
    | [l] -> List.rev l
    | _ -> raise Error

  let char_for_backslash = function
    | 'b'  -> '\b'
    | 'a'  -> '\x07'
    | 'e'  -> '\x1B'
    | 'f'  -> '\x0C'
    | 'n'  -> '\n'
    | 'r'  -> '\r'
    | 't'  -> '\t'
    | 'v'  -> '\x0B'
    | _ as c -> c
}

(* FIXME: atom that start with @ may contain parenthesis. Only the case of one pair
   is hardcoded here. More might be possible. *)
let atom  = '@''('[^'\t' '\n' '"' ';' '|'')']+')''_'['0'-'9']+ | [^'(' ')'' ''\t' '\n' '"' ';' '|']+
let space = [' ''\t''\n''\r']+
let nopip = [^ '|']*
let hex2  = ['0'-'9''a'-'f'] ['0'-'9''a'-'f']

rule read st = parse
  | eof                { st }
  | space              { read st lexbuf }
  | ';'                { read_comment st lexbuf }
  | '('                { read (start_list st) lexbuf }
  | ')'                { read (end_list st) lexbuf }
  | "\""               { read_string st (Buffer.create 17) lexbuf }
  | '|' nopip '|' as s { read (add (Atom s) st) lexbuf }
  | atom as s          { read (add (Atom s) st) lexbuf }
  | _                  { raise Error }

and read_comment st = parse
  | eof                { st }
  | '\n'               { read st lexbuf }
  | '\r'               { read st lexbuf }
  | _                  { read_comment st lexbuf }

and read_string st buf = parse
  | eof                { raise Error }
  | "\""               { let s = "\""^Buffer.contents buf^"\"" in
                         read (add (Atom s) st) lexbuf }
  | "\"\""             { Buffer.add_char buf '"';
                         read_string st buf lexbuf }
  | "\\x" (hex2 as s)  { Buffer.add_char buf (Scanf.sscanf s "%2x" Char.chr);
                         read_string st buf lexbuf }
  | "\\" (_ as c)      { Buffer.add_char buf (char_for_backslash c);
                         read_string st buf lexbuf }
  | _ as c             { Buffer.add_char buf c;
                         read_string st buf lexbuf }

{
  let read_list lexbuf = get_sexp_list (read [[]] lexbuf)
  let read lexbuf = get_sexp (read [] lexbuf)
}
