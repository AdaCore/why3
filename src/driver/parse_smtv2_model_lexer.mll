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
  open Parse_smtv2_model_parser
  exception SyntaxError

}

let atom = [^'('')'' ''\t''\n']
let space = [' ''\t''\n''\r']
let num = ['0'-'9']+
let opt_num = ['0'-'9']*
let hexa_num = ( num | ['a' - 'f'] | ['A' - 'F'])+
let dec_num = num"."num
let name = (['a'-'z']*'_'*['0'-'9']*)*
let dummy = ('_''_''_')?
let float_num = '#'('b' | 'x') hexa_num
let bv_num = '#'('b' | 'x') hexa_num

rule token = parse
  | '\n'
    { token lexbuf }
  | space+
      { token lexbuf }
  | "store" { STORE }
  | "const" { CONST }
  | "model" {MODEL}
  | "as" { AS }
  | '('
      { LPAREN }
  | ')'
      { RPAREN }
  | ';' { read_string (Buffer.create 17) lexbuf }
  | ";;" { read_string (Buffer.create 17) lexbuf }
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
  | "(_" space+ "bv"(num as bv_value) space+ num")" { BITVECTOR_VALUE bv_value }
  | "(_" space+ "BitVec" space+ num")" { BITVECTOR_TYPE }
  | "(_" space+ "extract" space+ num space+ num ")" as s { BITVECTOR_EXTRACT s }
  | "(_" space+ "int2bv" space+ num ")" as s { INT_TO_BV s}
  | "(_" space+ "FloatingPoint" space+ (num as exp) space+ (num as mantissa)")" { FLOAT_TYPE (exp, mantissa) }
  | "(_" space+ "+zero" space+ num space+ num ")" { FLOAT_VALUE Model_parser.Plus_zero }
  | "(_" space+ "-zero" space+ num space+ num ")" { FLOAT_VALUE Model_parser.Minus_zero }
  | "(_"  space+ "+oo" space+ num space+ num ")" { FLOAT_VALUE Model_parser.Plus_infinity }
  | "(_" space+ "-oo" space+ num space+ num ")" { FLOAT_VALUE Model_parser.Minus_infinity }
  | "(_" space+ "NaN" space+ num space+ num ")" { FLOAT_VALUE Model_parser.Not_a_number }
  | "(fp" space+ (float_num as b) space+ (float_num as eb) space+ (float_num as sb) ")"
      { FLOAT_VALUE (Model_parser.interp_float ~interp:false b eb sb) }
  | bv_num as bv_value { BITVECTOR_VALUE bv_value }

  | num as integer
      { INT_STR (integer) }
  | '-'space*(num as integer) { MINUS_INT_STR ("-"^integer) }
  | (num as int_part)"."(num as fract_part)
      { DEC_STR (int_part, fract_part)  }
  | '-'space*(num as int_part)"."(num as fract_part)
      {MINUS_DEC_STR (("-"^int_part), fract_part)}
  | atom+ as at { ATOM (at) }
  | eof
      { EOF }
  | _
      { raise SyntaxError }

and read_string buf =
  parse
  | '\n'      { COMMENT (Buffer.contents buf) }
  | '\r'      { COMMENT (Buffer.contents buf) }
  | eof       { COMMENT (Buffer.contents buf) }
  | _ as a    { Buffer.add_char buf a; read_string buf lexbuf }
