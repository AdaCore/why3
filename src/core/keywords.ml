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

open Parser_tokens

(* keep the following files synchronized:

  doc/ext/why3.py
  plugins/cfg/cfg_lexer.mll
  share/emacs/why3.el
  share/vim/syntax/why3.vim
  src/trywhy3/mode-why3.js
*)

let plain = [
    "abstract", ABSTRACT;
    "absurd", ABSURD;
    "alias", ALIAS;
    "any", ANY;
    "as", AS;
    "assert", ASSERT;
    "assume", ASSUME;
    "at", AT;
    "axiom", AXIOM;
    "begin", BEGIN;
    "break", BREAK;
    "by", BY;
    "check", CHECK;
    "clone", CLONE;
    "coinductive", COINDUCTIVE;
    "constant", CONSTANT;
    "continue", CONTINUE;
    "diverges", DIVERGES;
    "do", DO;
    "done", DONE;
    "downto", DOWNTO;
    "else", ELSE;
    "end", END;
    "ensures", ENSURES;
    "epsilon", EPSILON;
    "exception", EXCEPTION;
    "exists", EXISTS;
    "export", EXPORT;
    "false", FALSE;
    "for", FOR;
    "forall", FORALL;
    "fun", FUN;
    "function", FUNCTION;
    "ghost", GHOST;
    "goal", GOAL;
    "if", IF;
    "import", IMPORT;
    "in", IN;
    "inductive", INDUCTIVE;
    "invariant", INVARIANT;
    "label", LABEL;
    "lemma", LEMMA;
    "let", LET;
    "match", MATCH;
    "meta", META;
    "module", MODULE;
    "mutable", MUTABLE;
    "not", NOT;
    "old", OLD;
    "partial", PARTIAL;
    "predicate", PREDICATE;
    "private", PRIVATE;
    "pure", PURE;
    "raise", RAISE;
    "raises", RAISES;
    "reads", READS;
    "rec", REC;
    "requires", REQUIRES;
    "return", RETURN;
    "returns", RETURNS;
    "scope", SCOPE;
    "so", SO;
    "then", THEN;
    "theory", THEORY;
    "to", TO;
    "true", TRUE;
    "try", TRY;
    "type", TYPE;
    "use", USE;
    "val", VAL;
    "variant", VARIANT;
    "while", WHILE;
    "with", WITH;
    "writes", WRITES;
  ]

let contextual = [
    "float", FLOAT;
    "range", RANGE;
    "ref", REF;
  ]

let keyword_tokens =
  plain @ contextual

let keywords =
  List.map fst plain
