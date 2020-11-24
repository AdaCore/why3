
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

exception Error

val read : Lexing.lexbuf -> sexp
(** Read an S-expression from a lexbuf. Raises [Error] if the lexbuf doesn't
    contain an S-expression.  *)

val read_list : Lexing.lexbuf -> sexp list
