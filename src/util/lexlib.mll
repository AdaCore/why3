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

  let char_for_backslash = function
    | 'n' -> '\n'
    | 't' -> '\t'
    | c -> c

}

let newline = '\r'* '\n'

rule utf8_tail b n = parse
  | eof
      { false }
  | ['\128'-'\191'] as c
      { Buffer.add_char b c;
        n == 1 || utf8_tail b (n - 1) lexbuf }
  | _ { false }

and comment = parse
  | "(*)"
      { comment lexbuf }
  | "*)"
      { () }
  | "(*"
      { comment lexbuf; comment lexbuf }
  | newline
      { new_line lexbuf; comment lexbuf }
  | eof
      { raise Not_found }
  | _
      { comment lexbuf }

and string buf = parse
  | "\""
      { Buffer.contents buf }
  | "\\" newline
      { new_line lexbuf;
        string_skip_spaces buf lexbuf }
  | "\\" (_ as c)
      { Buffer.add_char buf (char_for_backslash c);
        string buf lexbuf }
  | newline
      { new_line lexbuf;
        Buffer.add_char buf '\n';
        string buf lexbuf }
  | eof
      { raise Not_found }
  | _ as c
      { Buffer.add_char buf c;
        string buf lexbuf }

and string_skip_spaces buf = parse
  | [' ' '\t']*
      { string buf lexbuf }

{
  exception UnterminatedComment
  exception UnterminatedString
  exception IllegalCharacter of string

  let () = Exn_printer.register (fun fmt e -> match e with
    | UnterminatedComment -> Format.fprintf fmt "unterminated comment"
    | UnterminatedString -> Format.fprintf fmt "unterminated string"
    | IllegalCharacter s -> Format.fprintf fmt "illegal character %s" s
    | _ -> raise e)

  let loc lb = Loc.extract (lexeme_start_p lb, lexeme_end_p lb)

  let comment lexbuf =
    let start = loc lexbuf in
    try comment lexbuf
    with Not_found -> raise (Loc.Located (start, UnterminatedComment))

  let string lexbuf =
    let start = loc lexbuf in
    try string (Buffer.create 128) lexbuf
    with Not_found -> raise (Loc.Located (start, UnterminatedString))

  let update_loc lexbuf file line chars =
    let pos = lexbuf.lex_curr_p in
    let new_file = match file with None -> pos.pos_fname | Some s -> s in
    lexbuf.lex_curr_p <-
      { pos with
          pos_fname = new_file;
          pos_lnum = line;
          pos_bol = pos.pos_cnum - chars;
      }

  let backjump lexbuf chars =
    if chars < 0 || chars > lexbuf.lex_curr_pos - lexbuf.lex_start_pos then
      invalid_arg "Lexlib.backjump";
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_pos <- lexbuf.lex_curr_pos - chars;
    lexbuf.lex_curr_p <- { pos with pos_cnum = pos.pos_cnum - chars }

  let remove_leading_plus s =
    let n = String.length s in
    if n > 0 && s.[0] = '+' then String.sub s 1 (n-1) else s

  let remove_underscores s =
    if String.contains s '_' then begin
      let count =
        let nb = ref 0 in
        String.iter (fun c -> if c = '_' then incr nb) s;
        !nb in
      let t = Bytes.create (String.length s - count) in
      let i = ref 0 in
      String.iter (fun c -> if c <> '_' then (Bytes.set t !i c; incr i)) s;
      Bytes.unsafe_to_string t
    end else s

  let illegal_character c lexbuf =
    let loc = loc lexbuf in
    let b = Buffer.create 2 in
    Buffer.add_char b c;
    let n =
      match c with
      | '\000'..'\127' -> 0
      | '\192'..'\223' -> 1
      | '\224'..'\239' -> 2
      | '\240'..'\247' -> 3
      | _ -> -1 in
    if n <> 0 && (n == -1 || not (utf8_tail b n lexbuf)) then begin
      (* invalid encoding, convert the first character to a utf8 one *)
      Buffer.reset b;
      let c = Char.code c in
      Buffer.add_char b (Char.chr (0xC0 lor (c lsr 6)));
      Buffer.add_char b (Char.chr (c land 0xBF));
    end;
    (* TODO: check that the buffer does not hold a utf8 character in one of the invalid ranges *)
    raise (Loc.Located (loc, IllegalCharacter (Buffer.contents b)))
}
