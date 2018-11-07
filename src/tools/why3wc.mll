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

(** Count spec/code tokens/lines and comment lines in Why3 source files

    Features and current limitations:
    - blank lines are ignored
    - "type", "constant", and "function" are counted as spec, not code
    - a type containing a mutable field is counted in both spec and code
*)

{
  open Lexing
  open Format

  let skip_header = ref true
  let tokens = ref false
  let factor = ref false
  let files = Queue.create ()

  (** counters *)

  type counter =
      { mutable spec: int; mutable code: int; mutable comment: int }

  let new_counter () =
    { spec = 0; code = 0; comment = 0 }

  let (+=) c1 c2 =
    c1.spec <- c1.spec + c2.spec;
    c1.code <- c1.code + c2.code;
    c1.comment <- c1.comment + c2.comment

  let reset c =
    c.spec <- 0; c.code <- 0; c.comment <- 0

  let current_line = new_counter ()
  let current_file = new_counter ()
  let grand_total = new_counter ()

  let comment_depth = ref 0

  let reset_counters () =
    reset current_line; reset current_file; comment_depth := 0

  let update_totals () =
    grand_total += current_file

  (** state of the automaton *)

  type state = Nothing | Spec | Code

  let state = ref Nothing

  let add n = if !tokens then n+1 else 1

  let add_token () = match !state with
    | Nothing -> ()
    | Spec -> current_line.spec <- add current_line.spec
    | Code -> current_line.code <- add current_line.code

  let new_line () =
    current_file += current_line; reset current_line

  let add_comment n =
    current_line.comment <- current_line.comment + n + 1;
    if n > 0 then new_line ()

  let add_string n =
    add_token ();
    if n > 0 then new_line ()

}

(** regexps (mostly from src/parser/lexer.mll) *)

let space = [' ' '\t' '\r']
let ident = ['a'-'z' 'A'-'Z' '_' '0'-'9' '\'']+
let spec =
  "type" | "constant" | "function" | "predicate" |
  "inductive" | "coinductive" | "axiom" | "lemma" | "goal" | "meta"
let code =
  "let" | "val" | "exception"
let annotation =
  "requires" | "ensures" | "returns" | "raises" | "reads" | "writes" |
  "variant" | "invariant" | "assert" | "assume" | "check" | "alias"

let digit = ['0'-'9']
let hexadigit = ['0'-'9' 'a'-'f' 'A'-'F']
let exponent = ['e' 'E'] (['-' '+']? digit+)
let pexponent = ['p' 'P'] (['-' '+']? digit+)
let number =
    ['0'-'9'] ['0'-'9' '_']*
  | '0' ['x' 'X'] (['0'-'9' 'A'-'F' 'a'-'f']['0'-'9' 'A'-'F' 'a'-'f' '_']*)
  | '0' ['o' 'O'] (['0'-'7'] ['0'-'7' '_']*)
  | '0' ['b' 'B'] (['0'-'1'] ['0'-'1' '_']*)
  | digit+ exponent
  | digit+ '.' digit* exponent?
  | digit* '.' digit+ exponent?
  | '0' ['x' 'X'] hexadigit+ pexponent
  | '0' ['x' 'X'] hexadigit+ '.' hexadigit*
  | '0' ['x' 'X'] hexadigit* '.' hexadigit+ pexponent?

let op_char_1 = ['=' '<' '>' '~']
let op_char_2 = ['+' '-']
let op_char_3 = ['*' '/' '%']
let op_char_4 = ['!' '$' '&' '?' '@' '^' '.' ':' '|' '#']
let op_char_34 = op_char_3 | op_char_4
let op_char_234 = op_char_2 | op_char_34
let op_char_1234 = op_char_1 | op_char_234
let op_char_pref = ['!' '?']

let token =
    number
  | "->" | "<-" | "<->" | "&&" | "||" | "/\\" | "\\/" | "<>"
  | op_char_pref op_char_4*
  | op_char_1234* op_char_1 op_char_1234*
  | op_char_234*  op_char_2 op_char_234*
  | op_char_34*   op_char_3 op_char_34*
  | op_char_4+

(** lexer entries; the entry point is [scan] *)

rule scan = parse
  | space+
      { scan lexbuf }
  | "(*)"
      { add_token (); scan lexbuf }
  | "(*" space* '\n'?
      { add_comment (comment 0 lexbuf); scan lexbuf }
  | '"'
      { add_string (string 0 lexbuf); scan lexbuf }
  | '\n' space* '\n' (* at least one blank line *)
      { new_line ();
        state := Nothing;
        scan lexbuf }
  | '\n'
      { new_line ();
        scan lexbuf }
  | spec
      { if !state = Nothing then state := Spec;
        add_token (); scan lexbuf }
  | code
      { if !state = Nothing then state := Code;
        add_token (); scan lexbuf }
  | "diverges" (* no curly braces for this annotation *)
      { current_line.spec <- add current_line.spec;
        scan lexbuf }
  | "mutable" (* rather imprecise, but better than nothing *)
      { state := Code; scan lexbuf }
  | annotation
      { let oldst = !state in (* most likely already Code *)
        state := Spec; add_token (); start_annotation lexbuf;
        state := oldst; scan lexbuf }
  | ident
      { add_token (); scan lexbuf }
  | token (* try to be precise wrt Why3 tokens *)
      { add_token (); scan lexbuf }
  | _ (* otherwise, the fallback is to count single characters *)
      { add_token (); scan lexbuf }
  | eof
      { }

(** looks for a left curly brace, then scans the annotation until the
    matching right curly brace *)

and start_annotation = parse
  | space+
      { start_annotation lexbuf }
  | "(*)"
      { add_token (); scan lexbuf }
  | "(*"
      { add_comment (comment 0 lexbuf); start_annotation lexbuf }
  | "{"
      { add_token (); scan_annotation lexbuf }
  | '\n'
      { new_line (); start_annotation lexbuf }
  | _
      { add_token () (* no curly brace, we give up *) }
  | eof
      { }

(** scans an annotation until we find the matching curly brace *)

and scan_annotation = parse
  | space+
      { scan_annotation lexbuf }
  | "{" (* nested curly braces (e.g. records) *)
      { add_token (); scan_annotation lexbuf; scan_annotation lexbuf }
  | "}"
      { add_token () }
  | "(*)"
      { add_token (); scan lexbuf }
  | "(*" space* '\n'?
      { add_comment (comment 0 lexbuf); scan_annotation lexbuf }
  | '"'
      { add_string (string 0 lexbuf); scan_annotation lexbuf }
  | ('\n' | space)* '\n'
      { new_line (); scan_annotation lexbuf }
  | ident
      { add_token (); scan_annotation lexbuf }
  | token
      { add_token (); scan_annotation lexbuf }
  | _
      { add_token (); scan_annotation lexbuf }
  | eof
      { }

(** [string n] reads a string until its end and returns n + the number
    of newlines it contains. *)

and string n = parse
  | '"'  { n }
  | '\\' ('\\' | '"') { string n lexbuf }
  | '\n' { string (n + 1) lexbuf }
  | _    { string n lexbuf }
  | eof  { n }

(** [comment n] reads a comment until its end and returns n + the number
    of non-empty lines it contains (not counting the first one). *)

and comment n = parse
  | ('\n' | space)* "*)"
          { n }
  | "(*)" { comment n lexbuf }
  | "(*"  { comment (comment n lexbuf) lexbuf }
  | '"'   { comment (string n lexbuf) lexbuf }
  | '\n'+ { comment (n + 1) lexbuf }
  | _     { comment n lexbuf }
  | eof   { n }

(** [read_header] is used to skip the possible header at
    the beginning of files (unless option -a is specified).
    It stops whenever it encounters an empty line or any character outside
    a comment. In this last case, it correctly resets the lexer position
    on that character (decreasing [lex_curr_pos] by 1). *)

and read_header = parse
  | "(*"   { skip_header_comment lexbuf; skip_until_nl lexbuf;
             read_header lexbuf }
  | "\n"   { () }
  | space+ { read_header lexbuf }
  | _      { lexbuf.lex_curr_pos <- lexbuf.lex_curr_pos - 1 }
  | eof    { () }

and skip_header_comment = parse
  | "*)" { () }
  | _    { skip_header_comment lexbuf }
  | eof  { () }

and skip_until_nl = parse
  | '\n' { () }
  | _    { skip_until_nl lexbuf }
  | eof  { () }

{

  (** printing results *)

  let legend =
    let todo = ref true in
    fun () -> if !todo then begin
      printf "    spec     code comments@."; todo := false end

  let print_file ?file c =
    legend ();
    printf "%8d" c.spec;
    (* if not !code_only then *) printf " %8d" c.code;
    printf " %8d" c.comment;
    (match file with Some f -> printf " %s" f | _ -> ());
    if !factor && c.code > 0 then begin
      let f = float c.spec /. float c.code in
      printf " (%.2f)" f
    end;
    printf "@."

  let print_totals () =
    print_file ~file:"total" grand_total

  (** processing channels/files *)

  let process_channel ch =
    let lb = Lexing.from_channel ch in
    reset_counters ();
    if !skip_header then read_header lb;
    scan lb

  let process_file f =
    try
      let ch = open_in f in
      process_channel ch;
      close_in ch;
      print_file ~file:f current_file;
      update_totals ()
    with Sys_error s ->
      flush stdout; eprintf "why3wc: %s@." s

  (** Command line parsing and entry point *)

  let spec = Arg.align [
    "-t", Arg.Set tokens,
      " count tokens";
    "--tokens", Arg.Set tokens,
      " same as -t";
    "-l", Arg.Clear tokens,
      " count lines (default)";
    "--lines", Arg.Clear tokens,
      " same as -l";
    "-f", Arg.Set factor,
      " print spec/code ratio";
    "--factor", Arg.Set factor,
      " same as -f";
    "-a", Arg.Clear skip_header,
      " count heading comments as well";
    "--do-not-skip-header", Arg.Clear skip_header,
      " same as -a";
  ]

  let add_file file =
    if not (Sys.file_exists file) then begin
      eprintf "%s: no such file@." file; exit 1
    end;
    Queue.add file files

  let usage = Format.sprintf "Usage: %s [options] files...\n\
  \n\
  Counts tokens/lines in Why3 source files.\n\
  Assumes source files to be lexically well-formed.\n\
  If no source file is given, standard input is analyzed.\n"
    (Filename.basename Sys.argv.(0))

  let () = Arg.parse spec add_file usage

  let () =
    let n = Queue.length files in
    if n = 0 then begin process_channel stdin; print_file current_file end
    else if n = 1 then process_file (Queue.pop files)
    else begin Queue.iter process_file files; print_totals () end

}
