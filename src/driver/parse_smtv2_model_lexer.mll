(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2016   --   INRIA - CNRS - Paris-Sud University  *)
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
let space = [' ''\t''\n']
let num = ['0'-'9']+
let dec_num = num"."num

rule token = parse
  | '\n'
    { token lexbuf }
  | space+ as space_str
      { SPACE (space_str) }
  | "mk_t__ref"(num*) { MK_T_REF }
  | "store" { STORE }
  | "const" { CONST }
  | "model" {MODEL}
  | "as" { AS }
  | '('
      { LPAREN }
  | ')'
      { RPAREN }
  | "(_ bv"(num as bv_value)" "num")" { BITVECTOR_VALUE bv_value }
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
    (* | space { SPACE } *)
  | _
	{ raise SyntaxError }
