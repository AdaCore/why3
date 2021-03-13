(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* The type of tokens. *)

open Why3

type token =
  | SWITCH
  | VAR
  | CFG
  | GOTO
  | WRITES
  | WITH
  | WHILE
  | VARIANT
  | VAL
  | USE
  | UNDERSCORE
  | UIDENT of (string)
  | TYPE
  | TRY
  | TRUE
  | TO
  | THEORY
  | THEN
  | STRING of (string)
  | SO
  | SEMICOLON
  | SCOPE
  | RIGHTSQ_QUOTE of (string)
  | RIGHTSQ
  | RIGHTPAR_USCORE of (string)
  | RIGHTPAR_QUOTE of (string)
  | RIGHTPAR
  | RIGHTBRC
  | RETURNS
  | RETURN
  | REQUIRES
  | REF
  | REC
  | REAL of (Number.real_constant)
  | READS
  | RANGE
  | RAISES
  | RAISE
  | QUOTE_LIDENT of (string)
  | PURE
  | PRIVATE
  | PREDICATE
  | POSITION of (Loc.position)
  | PARTIAL
  | OR
  | OPPREF of (string)
  | OP4 of (string)
  | OP3 of (string)
  | OP2 of (string)
  | OP1 of (string)
  | OLD
  | NOT
  | MUTABLE
  | MODULE
  | MINUS
  | META
  | MATCH
  | LTGT
  | LT
  | LRARROW
  | LIDENT of (string)
  | LET
  | LEMMA
  | LEFTSQ
  | LEFTSQBAR
  | LEFTPAR
  | LEFTBRC
  | LARROW
  | LABEL
  | INVARIANT
  | INTEGER of (Number.int_constant)
  | INDUCTIVE
  | IN
  | IMPORT
  | IF
  | GT
  | GOAL
  | GHOST
  | FUNCTION
  | FUN
  | FORALL
  | FOR
  | FLOAT
  | FALSE
  | EXPORT
  | EXISTS
  | EXCEPTION
  | EQUALARROW
  | EQUAL
  | EPSILON
  | EOF
  | ENSURES
  | END
  | ELSE
  | DOWNTO
  | DOTDOT
  | DOT
  | DONE
  | DO
  | DIVERGES
  | CORE_UIDENT of (string)
  | CORE_LIDENT of (string)
  | CONTINUE
  | CONSTANT
  | COMMA
  | COLON
  | COINDUCTIVE
  | CLONE
  | CHECK
  | BY
  | BREAK
  | BEGIN
  | BARBAR
  | BARRIGHTSQ
  | BAR
  | AXIOM
  | ATTRIBUTE of (string)
  | AT
  | ASSUME
  | ASSERT
  | AS
  | ARROW
  | ANY
  | AND
  | AMPAMP
  | AMP
  | ALIAS
  | ABSURD
  | ABSTRACT
