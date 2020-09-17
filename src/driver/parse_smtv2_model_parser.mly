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

%{
open Model_parser
open Smt2_model_defs
%}

%start <Smt2_model_defs.definition Wstdlib.Mstr.t> output
%type <Smt2_model_defs.term> smt_term
%token <string> ATOM
%token MODEL
%token STORE
%token CONST
%token AS
%token DEFINE_FUN
%token DECLARE_FUN
%token DECLARE_SORT
%token DECLARE_DATATYPES
%token FORALL
%token UNDERSCORE
%token AS_ARRAY
%token EQUAL
%token ITE
%token LAMBDA
%token ARRAY_LAMBDA
%token TRUE FALSE
%token LET
%token AND LE GE NOT
%token DIV
%token <Model_parser.model_float> FLOAT_VALUE
%token <string> COMMENT
%token <string> STRING
%token <Model_parser.model_bv> BV_VALUE_BIN
%token <Model_parser.model_bv> BV_VALUE_HEX
%token <Model_parser.model_bv> BV_VALUE
%token <string> BV_EXTRACT
%token <string> INT_TO_BV
%token BV_TYPE
%token <string * string> FLOAT_TYPE
%token <Model_parser.model_int> INT
%token <Model_parser.model_dec> DEC
%token LPAREN RPAREN
%token EOF
%%

output:
| EOF { Wstdlib.Mstr.empty }
| LPAREN MODEL RPAREN { Wstdlib.Mstr.empty }
| LPAREN MODEL list_decls RPAREN { $3 }

list_decls:
| LPAREN decl RPAREN { add_element $2 Wstdlib.Mstr.empty}
| LPAREN decl RPAREN list_decls { add_element $2 $4 }
| COMMENT list_decls  { $2 } (* Lines beginning with ';' are ignored *)

(* Examples:
"(define-fun to_rep ((_ufmt_1 enum_t)) Int 0)"
"(declare-sort enum_t 0)"
"(declare-datatypes () ((tuple0 (Tuple0))
))"
*)
decl:
| DEFINE_FUN name LPAREN args_lists RPAREN
    ireturn_type smt_term
    { let t = make_local $4 $7 in
        Some ($2, (Function ($4, t))) }
| DECLARE_SORT isort_def { None }
| DECLARE_DATATYPES idata_def { None }
(* z3 declare function *)
| DECLARE_FUN name LPAREN args_lists RPAREN ireturn_type { None }
| FORALL LPAREN args_lists RPAREN smt_term { None } (* z3 cardinality *)

smt_term:
| name      { Variable $1         }
| STRING    { Sval (String $1)    }
| INT       { Sval (Integer $1)   }
| DEC       { Sval (Decimal $1)   }
| fraction  { Sval (Fraction $1)  }
| array     { Array $1            }
| bitvector { Sval (Bitvector $1) }
| boolean   { Sval (Boolean $1)   }
(* z3 sometimes answer with boolean expressions for some reason ? *)
| boolean_expression { Sval (Other "") }
| FLOAT_VALUE { Sval (Float $1) }
(* ite (= ?a ?b) ?c ?d *)
| LPAREN ITE pair_equal smt_term smt_term RPAREN
    {  match $3 with
    | None -> Sval (Other "")
    | Some (t1, t2) -> Ite (t1, t2, $4, $5) }
(* No parsable value are applications. *)
| application { $1 }

(* Particular case for functions that are defined as an equality:
   define-fun f ((a int) (b int)) (= a b) *)
| LPAREN EQUAL list_smt_term RPAREN { Sval (Other "") }
| LPAREN LET LPAREN list_let RPAREN smt_term RPAREN
    { substitute $4 $6 }
(* z3 specific constructor *)
| LPAREN UNDERSCORE AS_ARRAY name RPAREN
    { To_array (Variable $4) }


(* value of let are not used *)
list_let:
| { [] }
| LPAREN name smt_term RPAREN list_let { ($2, $3) :: $5 }
(* TODO not efficient *)

(* Condition of an if-then-else. We are only interested in equality case *)
pair_equal:
| LPAREN AND list_pair_equal RPAREN { None }
| LPAREN EQUAL smt_term smt_term RPAREN { Some ($3, $4) }
| application { None }
| name { None }
(* ITE containing boolean expressions cannot be dealt with for counterex *)
| LPAREN NOT smt_term RPAREN { None }

list_pair_equal:
| { }
| pair_equal list_pair_equal { }

list_smt_term:
| smt_term { [$1] }
| list_smt_term smt_term { $2 :: $1}

application:
| LPAREN name list_smt_term RPAREN { Apply ($2, List.rev $3) }
| LPAREN binop smt_term smt_term RPAREN { Apply ($2, [$3; $4]) }
(* This should not happen in relevant part of the model *)
| LPAREN INT_TO_BV smt_term RPAREN {
  Apply ($2, [$3]) }


binop:
| LE { "<=" }
| GE { ">=" }

array:
| LPAREN LPAREN AS CONST ireturn_type RPAREN smt_term RPAREN
    { Const $7 }
| LPAREN STORE array smt_term smt_term RPAREN
    { Store ($3, $4, $5) }
| LPAREN STORE name smt_term smt_term RPAREN
    { Store (Array_var $3, $4, $5) }
(* When array is of type int -> bool, Cvc4 returns something that looks like:
   (ARRAY_LAMBDA (LAMBDA ((BOUND_VARIABLE_1162 Int)) false)) *)
| LPAREN ARRAY_LAMBDA LPAREN LAMBDA LPAREN args_lists RPAREN smt_term RPAREN RPAREN
    { Const $8 }

args_lists:
| { [] }
| LPAREN args RPAREN args_lists { $2 :: $4 }
(* TODO This is inefficient and should be done in a left recursive way *)

args:
| name ireturn_type { $1, $2 }

name:
| ATOM { $1 }
(* Should not happen in relevant part of the model (ad hoc) *)
| BV_TYPE { "" }
| BV_EXTRACT { $1 }
| FLOAT_TYPE { "" }

(* Z3 specific boolean expression. This should maybe be used in the future as
   it may give some information on the counterexample. *)
boolean_expression:
| LPAREN FORALL LPAREN args_lists RPAREN smt_term RPAREN {  }
| LPAREN NOT smt_term RPAREN { }
| LPAREN AND list_smt_term RPAREN { }

fraction:
| LPAREN; DIV; nom=INT; den=INT; RPAREN
    { {frac_nom= nom.int_value; frac_den= den.int_value; frac_verbatim= Format.sprintf "(/ %s %s)" nom.int_verbatim den.int_verbatim} }
(* Integer from z3 can be written 1.0 *)
| LPAREN; DIV; d1=DEC; d2=DEC; RPAREN
    { if BigInt.(eq d1.dec_frac zero && eq d2.dec_frac zero) then
        {frac_nom= d1.dec_int; frac_den= d2.dec_int; frac_verbatim= Format.sprintf "(/ %s %s)" d1.dec_verbatim d2.dec_verbatim}
      else
        (* Should not happen. If it does, change the parsing *)
        assert (false) }

(* Example:
   (_ bv2048 16) *)
bitvector:
| BV_VALUE { $1 }
| BV_VALUE_BIN { $1 }
| BV_VALUE_HEX { $1 }

boolean:
| TRUE  { true  }
| FALSE { false }

(* BEGIN IGNORED TYPES *)
(* Types are badly parsed (for future use) but never saved *)
ireturn_type:
| name { Some $1 }
| LPAREN idata_type RPAREN { None }

isort_def:
| name INT { }

idata_def:
(* cvc4,1.5 with smtlib2.5 compat *)
| LPAREN RPAREN LPAREN LPAREN idata_type RPAREN RPAREN { }
| LPAREN RPAREN LPAREN LPAREN RPAREN RPAREN { }
(* cvc4,1.6 with smtlib2.6 compat *)
| LPAREN LPAREN ilist_app RPAREN RPAREN LPAREN LPAREN idata_type RPAREN RPAREN { }

ilist_app:
| name { }
| INT { }
| name ilist_app { }
| LPAREN idata_type RPAREN { }
| LPAREN idata_type RPAREN ilist_app { }

idata_type:
| name { }
| name idata_type { }
(* Z3 return bv can be "(_ bv 129)" which is not interpreted as a value *)
| UNDERSCORE name INT { }
| LPAREN idata_type RPAREN option(idata_type) { }
(* END IGNORED TYPES *)
