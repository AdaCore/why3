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
  open Parse_smtv2_model_parser
  open Model_parser
  exception SyntaxError

  let char_for_backslash = function
    | 'a'  -> '\x07'
    | 'b'  -> '\b'
    | 'e'  -> '\x1B'
    | 'f'  -> '\x0C'
    | 'n'  -> '\n'
    | 'r'  -> '\r'
    | 't'  -> '\t'
    | 'v'  -> '\x0B'
    | _ as c -> c

  let bv_of_string s =
    let v, l =
      try BigInt.of_string ("0b"^Strings.remove_prefix "#b" s), String.length s-2 with Not_found ->
      try BigInt.of_string ("0x"^Strings.remove_prefix "#x" s), (String.length s-2) * 4 with Not_found ->
        failwith "bv_of_string" in
    {bv_value= v; bv_length= l; bv_verbatim= s}

let float_of_binary sign exp mant =
    let sign = bv_of_string sign in
    let exp = bv_of_string exp in
    let mant = bv_of_string mant in
    float_of_binary {sign; exp; mant}
}

let atom = [^'('')'' ''\t''\n''"']
let space = [' ''\t''\n''\r']
let num = ['0'-'9']+
let opt_num = ['0'-'9']*
let hex     = ['0'-'9' 'a'-'f' 'A'-'F']
let hexa_num = hex+
let binary_num = ['0' '1']+
let dec_num = num"."num
let name = (['a'-'z']*'_'*['0'-'9']*)*
let dummy = ('_''_''_')?
let float_num = '#'('b' | 'x') hexa_num
let bv_num = '#'('b' | 'x') hexa_num
let variable = [^'|']* (* cvc4 variables can now be arbitrary strings *)

rule token = parse
  | '\n'
    { token lexbuf }
  | space+
      { token lexbuf }
  | "\""
      { STRING (read_string (Buffer.create 17) lexbuf) }
  | "store" { STORE }
  | "const" { CONST }
  | "model" {MODEL}
  | "as" { AS }
  | '('
      { LPAREN }
  | ')'
      { RPAREN }
  | ';' { read_comment (Buffer.create 17) lexbuf }
  | ";;" { read_comment (Buffer.create 17) lexbuf }
  | '=' { EQUAL }
  | '_' { UNDERSCORE }
  | '/' { DIV }
  | "as-array" { AS_ARRAY }
  | "ite" { ITE }
  | "define-fun" { DEFINE_FUN }
  | "declare-fun" { DECLARE_FUN }
  | "declare-sort" { DECLARE_SORT } (* z3 declare functions *)
  | "forall" { FORALL } (* z3 cardinality *)
  | "not" { NOT } (* Z3 specific *)
  | "and" { AND } (* z3 specific in ite  *)
  | "<=" { LE } (* z3 specific *)
  | ">=" { GE } (* z3 specific *)
  | "declare-datatypes" { DECLARE_DATATYPES }
  | "let" { LET }
  | "true" { TRUE }
  | "false" { FALSE }
  | "LAMBDA" { LAMBDA }
  | "lambda" { LAMBDA }
  | "ARRAY_LAMBDA" { ARRAY_LAMBDA }
  | "(_" space+ "bv"(num as v) space+ (num as l)")" as s { BV_VALUE {bv_value= BigInt.of_string v; bv_length= int_of_string l; bv_verbatim= s} }
  | "(_" space+ "BitVec" space+ num")" { BV_TYPE }
  | "(_" space+ "extract" space+ num space+ num ")" as s { BV_EXTRACT s }
  | "(_" space+ "int2bv" space+ num ")" as s { INT_TO_BV s}
  | "(_" space+ "FloatingPoint" space+ (num as exp) space+ (num as mantissa)")" { FLOAT_TYPE (exp, mantissa) }
  | "(_" space+ "+zero" space+ num space+ num ")" { FLOAT_VALUE Plus_zero }
  | "(_" space+ "-zero" space+ num space+ num ")" { FLOAT_VALUE Minus_zero }
  | "(_"  space+ "+oo" space+ num space+ num ")" { FLOAT_VALUE Plus_infinity }
  | "(_" space+ "-oo" space+ num space+ num ")" { FLOAT_VALUE Minus_infinity }
  | "(_" space+ "NaN" space+ num space+ num ")" { FLOAT_VALUE Not_a_number }
  | "(fp" space+ (float_num as b) space+ (float_num as eb) space+ (float_num as sb) ")"
      { FLOAT_VALUE (float_of_binary b eb sb) }
  | "#x" (hexa_num as v) as s { BV_VALUE_HEX {bv_value= BigInt.of_string ("0x"^v); bv_length= String.length v/4; bv_verbatim= s} }
  | "#b" (binary_num as v) as s {BV_VALUE_BIN {bv_value= BigInt.of_string ("0b"^v); bv_length= String.length v/4; bv_verbatim= s} }

  | num as i                                         { INT {int_value= BigInt.of_string i; int_verbatim= i} }
  | '(' space* '-' space* (num as i) space* ')' as s
      { INT {int_value= BigInt.minus (BigInt.of_string i); int_verbatim= "-"^i} }
  | (num as i)"."(num as f) as s                     { DEC {dec_int= BigInt.of_string i; dec_frac= BigInt.of_string f; dec_verbatim= s} }
  | '(' space* '-' space* (num as i) '.' (num as f) space* ')' as s
    { DEC { dec_int= BigInt.minus (BigInt.of_string i); dec_frac= BigInt.of_string f; dec_verbatim= "-"^i^"."^f } }
  | '|' (variable as at) '|'                         { ATOM (at) }
  | atom+ as at                                      { ATOM (at) }
  | eof
      { EOF }
  | _
      { raise SyntaxError }

and read_comment buf =
  parse
  | '\n'      { COMMENT (Buffer.contents buf) }
  | '\r'      { COMMENT (Buffer.contents buf) }
  | eof       { COMMENT (Buffer.contents buf) }
  | _ as a    { Buffer.add_char buf a; read_comment buf lexbuf }

and read_string buf = parse
  | "\""
    { Buffer.contents buf }
  | "\"\""
    { Buffer.add_char buf '"';
      read_string buf lexbuf }
  | "\\x" (hex hex as c)
    { let c = Scanf.sscanf c "%2x" Char.chr in
      Buffer.add_char buf c;
      read_string buf lexbuf }
  | "\\" (_ as c)
    { Buffer.add_char buf (char_for_backslash c);
      read_string buf lexbuf }
  | _ as c
    { Buffer.add_char buf c;
      read_string buf lexbuf }
