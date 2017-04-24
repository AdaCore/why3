(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
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
let dec_num = num"."num
let name = (['a'-'z']*'_'*['0'-'9']*)*

rule token = parse
  | '\n'
    { token lexbuf }
  | space+ as space_str
      { SPACE (space_str) }
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
  | "as-array" { AS_ARRAY }
  | "ite" { ITE }
  | "define-fun" { DEFINE_FUN }
  | "declare-fun" { DECLARE_FUN }
  | "declare-sort" { DECLARE_SORT } (* z3 declare functions *)
  | "forall" { FORALL } (* z3 cardinality *)
  | "declare-datatypes" { DECLARE_DATATYPES }
  | "let" { LET }
  | "true" { TRUE }
  | "false" { FALSE }
  | "LAMBDA" { LAMBDA }
  | "ARRAY_LAMBDA" { ARRAY_LAMBDA }
  | "mk___split_fields"(opt_num as n) opt_num "___" {
    match n with
    | "" -> MK_SPLIT_FIELD ("mk___split_fields",0)
    | n -> MK_SPLIT_FIELD ("mk____split_fields"^n, int_of_string n) }
  | "mk___rep"(opt_num as n) opt_num "___" {
    match n with
    | "" -> MK_REP ("mk___rep", 0)
    | n -> MK_REP ("mk___rep"^n, int_of_string n) }
  | "mk___t"(opt_num as n) opt_num "___" {
    match n with
    | "" -> MK_T ("mk___t", 0)
    | n -> MK_T ("mk___t"^n, int_of_string n) }
  | "mk___split_discrs"(opt_num as n) opt_num "___" {
    match n with
    | "" -> MK_SPLIT_DISCRS ("mk___split_discrs",0)
    | n -> MK_SPLIT_DISCRS ("mk____split_discrs"^n, int_of_string n) }
  | "mk" name "___" { MK_ANYTHING } (* encapsulate mk_int_ref etc (other refs) *)
  | "(_ bv"(num as bv_value)" "num")" { BITVECTOR_VALUE bv_value }
  | "(_ BitVec "num")" { BITVECTOR_TYPE }
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
