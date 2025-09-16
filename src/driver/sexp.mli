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

(** {1 S-expressions and their parser}

     Double quotes and pipes in atoms are retained for strings and quoted symbols, to
    allow for distinguishing between "0" 0 and |0|. Two quotes in a string are read as one
    quote. For example:

      S-expression | OCaml
      0            | Atom "0"
      "0"          | Atom "\"0\""
      |0|          | Atom "|0|"
      |x x|        | Atom "|x x|"
      "x\"\"x"     | Atom "\"x\"x\""
*)

type sexp =
  | Atom of string
  | List of sexp list

val exists : (sexp -> bool) -> sexp -> bool
(** Check if the node or any of its sub-nodes satisfies the predicate. *)

exception Error

val read : Lexing.lexbuf -> sexp
(** Read an S-expression from a lexbuf. Raises [Error] if the lexbuf doesn't
    contain an S-expression.  *)

val read_list : Lexing.lexbuf -> sexp list
