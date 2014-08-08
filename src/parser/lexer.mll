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
  open Parser

  exception IllegalCharacter of char

  let () = Exn_printer.register (fun fmt e -> match e with
    | IllegalCharacter c -> fprintf fmt "illegal character %c" c
    | _ -> raise e)

  let keywords = Hashtbl.create 97
  let () =
    List.iter
      (fun (x,y) -> Hashtbl.add keywords x y)
      [
        "as", AS;
        "axiom", AXIOM;
        "clone", CLONE;
        "coinductive", COINDUCTIVE;
        "constant", CONSTANT;
        "else", ELSE;
        "end", END;
        "epsilon", EPSILON;
        "exists", EXISTS;
        "export", EXPORT;
        "false", FALSE;
        "forall", FORALL;
        "function", FUNCTION;
        "goal", GOAL;
        "if", IF;
        "import", IMPORT;
        "in", IN;
        "inductive", INDUCTIVE;
        "lemma", LEMMA;
        "let", LET;
        "match", MATCH;
        "meta", META;
        "namespace", NAMESPACE;
        "not", NOT;
        "predicate", PREDICATE;
        "prop", PROP;
        "then", THEN;
        "theory", THEORY;
        "true", TRUE;
        "type", TYPE;
        "use", USE;
        "with", WITH;
        (* programs *)
        "abstract", ABSTRACT;
        "absurd", ABSURD;
        "any", ANY;
        "assert", ASSERT;
        "assume", ASSUME;
        "begin", BEGIN;
        "check", CHECK;
        "diverges", DIVERGES;
        "do", DO;
        "done", DONE;
        "downto", DOWNTO;
        "ensures", ENSURES;
        "exception", EXCEPTION;
        "for", FOR;
        "fun", FUN;
        "ghost", GHOST;
        "invariant", INVARIANT;
        "loop", LOOP;
        "model", MODEL;
        "module", MODULE;
        "mutable", MUTABLE;
        "private", PRIVATE;
        "raise", RAISE;
        "raises", RAISES;
        "reads", READS;
        "rec", REC;
        "requires", REQUIRES;
        "returns", RETURNS;
        "to", TO;
        "try", TRY;
        "val", VAL;
        "variant", VARIANT;
        "while", WHILE;
        "writes", WRITES;
      ]
}

let space = [' ' '\t' '\r']
let lalpha = ['a'-'z' '_']
let ualpha = ['A'-'Z']
let alpha = lalpha | ualpha
let digit = ['0'-'9']
let lident = lalpha (alpha | digit | '\'')*
let uident = ualpha (alpha | digit | '\'')*
let hexadigit = ['0'-'9' 'a'-'f' 'A'-'F']

let op_char_1 = ['=' '<' '>' '~']
let op_char_2 = ['+' '-']
let op_char_3 = ['*' '/' '%']
let op_char_4 = ['!' '$' '&' '?' '@' '^' '.' ':' '|' '#']
let op_char_34 = op_char_3 | op_char_4
let op_char_234 = op_char_2 | op_char_34
let op_char_1234 = op_char_1 | op_char_234

let op_char_pref = ['!' '?']

rule token = parse
  | "##" space* ("\"" ([^ '\010' '\013' '"' ]* as file) "\"")?
    space* (digit+ as line) space* (digit+ as char) space* "##"
      { Lexlib.update_loc lexbuf file (int_of_string line) (int_of_string char);
        token lexbuf }
  | "#" space* "\"" ([^ '\010' '\013' '"' ]* as file) "\""
    space* (digit+ as line) space* (digit+ as bchar) space*
    (digit+ as echar) space* "#"
      { POSITION (Loc.user_position file (int_of_string line)
                 (int_of_string bchar) (int_of_string echar)) }
  | '\n'
      { Lexlib.newline lexbuf; token lexbuf }
  | space+
      { token lexbuf }
  | '_'
      { UNDERSCORE }
  | lident as id
      { try Hashtbl.find keywords id with Not_found -> LIDENT id }
  | uident as id
      { UIDENT id }
  | ['0'-'9'] ['0'-'9' '_']* as s
      { INTEGER (Number.int_const_dec (Lexlib.remove_underscores s)) }
  | '0' ['x' 'X'] (['0'-'9' 'A'-'F' 'a'-'f']['0'-'9' 'A'-'F' 'a'-'f' '_']* as s)
      { INTEGER (Number.int_const_hex (Lexlib.remove_underscores s)) }
  | '0' ['o' 'O'] (['0'-'7'] ['0'-'7' '_']* as s)
      { INTEGER (Number.int_const_oct (Lexlib.remove_underscores s)) }
  | '0' ['b' 'B'] (['0'-'1'] ['0'-'1' '_']* as s)
      { INTEGER (Number.int_const_bin (Lexlib.remove_underscores s)) }
  | (digit+ as i) ("" as f) ['e' 'E'] (['-' '+']? digit+ as e)
  | (digit+ as i) '.' (digit* as f) (['e' 'E'] (['-' '+']? digit+ as e))?
  | (digit* as i) '.' (digit+ as f) (['e' 'E'] (['-' '+']? digit+ as e))?
      { FLOAT (Number.real_const_dec i f
          (Opt.map Lexlib.remove_leading_plus e)) }
  | '0' ['x' 'X'] (hexadigit+ as i) ("" as f) ['p' 'P'] (['-' '+']? digit+ as e)
  | '0' ['x' 'X'] (hexadigit+ as i) '.' (hexadigit* as f)
        (['p' 'P'] (['-' '+']? digit+ as e))?
  | '0' ['x' 'X'] (hexadigit* as i) '.' (hexadigit+ as f)
        (['p' 'P'] (['-' '+']? digit+ as e))?
      { FLOAT (Number.real_const_hex i f
          (Opt.map Lexlib.remove_leading_plus e)) }
  | "(*)"
      { LEFTPAR_STAR_RIGHTPAR }
  | "(*"
      { Lexlib.comment lexbuf; token lexbuf }
  | "~'" (lident as id)
      { OPAQUE_QUOTE_LIDENT id }
  | "'" (lident as id)
      { QUOTE_LIDENT id }
  | "'" (uident as id)
      { QUOTE_UIDENT id }
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
      { STRING (Lexlib.string lexbuf) }
  | eof
      { EOF }
  | _ as c
      { raise (IllegalCharacter c) }

{
  let parse_logic_file env path lb =
    open_file token (Lexing.from_string "") (Typing.open_file env path);
    Loc.with_location (logic_file token) lb;
    Typing.close_file ()

  let parse_program_file inc lb =
    open_file token (Lexing.from_string "") inc;
    Loc.with_location (program_file token) lb

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
    (), parse_logic_file env path lb

  let library_of_env = Env.register_format "why" ["why"] read_channel
    ~desc:"Why@ logical@ language"

  let parse_logic_file env = parse_logic_file (library_of_env env)
}

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. test"
End:
*)

