Other Input Formats
===================

Why3 can be used to verify programs written in languages other than
WhyML. Currently, Why3 supports tiny subsets of C and Python,
respectively coined micro-C and micro-Python below. These were
designed for teaching purposes. They come with their own specification
languages, written in special comments.
These input formats are described below.

Any Why3 tool (`why3 prove`, `why3 ide`, etc.) can be passed a file
with a suffix `.c` or `.py`, which triggers the corresponding input format.
These input formats can also be used in on-line versions of Why3, at
http://why3.lri.fr/micro-C/ and http://why3.lri.fr/python/, respectively.

.. _format.micro-C:

micro-C
-------

Micro-C is a valid subset of ANSI C. Hence, micro-C files can be
passed to a C compiler.

Syntax of micro-C
~~~~~~~~~~~~~~~~~

Notation: The grammar of micro-C is given below in extended
Backus-Naur Form, using `|` for alternation, `()` for grouping,
`[]` for option, and `{}` for repetition.

Logical annotations are inserted in special comments starting
with `//@` or `/*@`. In the following grammar, we
only use the former kind, for simplicity, but both kinds are allowed.

.. productionlist:: micro-C
    file: `decl`*
    decl: `c_include` | `c_function` | `logic_declaration`
    c_include: "#include" "<" file-name ">"

Directives `#include` are ignored during the translation to
Why3. They are allowed anyway, such that a C source code using
functions such as `printf` (see below) is accepted by a C compiler.

.. rubric:: Function definition

.. productionlist:: micro-C
     c_function: `return_type` identifier "(" [ `params` ] ")" { spec } block
    return_type: "void" | "int"
         params: `param` { "," `param` }
          param: "int" identifier | "int" identifier "[]"

.. rubric:: Function specification

.. productionlist:: micro-C
    spec: "requires" `term` ";"
       : | "ensures"  `term` ";"
       : | "variant"  `term` { "," `term` } ";"

.. rubric:: C expression

.. productionlist:: micro-C
    expr: integer-literal | string-literal
       : | identifier | identifier ( "++" | "--" ) | ( "++" | "--" ) identifier
       : | identifier "[" `expr` "]"
       : | identifier "[" `expr` "]" ( "++" | "--")
       : | ( "++" | "--") identifier "[" `expr` "]"
       : | "-" `expr` | "!" `expr`
       : | `expr` ( "+" | "-" | "*" | "/" | "%" | "==" | "!=" | "<" | "<=" | ">" | ">=" | "&&" | "||" ) `expr`
       : | identifier "(" [ `expr` { "," `expr` } ] ")"
       : | "scanf" "(" "\"%d\"" "," "&" identifier ")"
       : | "(" `expr` ")"

.. rubric:: C statement

.. productionlist:: micro-C
       stmt: ";"
            : | "return" `expr` ";"
            : | "int" identifier ";"
            : | "int" identifier "[" `expr` "]" ";"
            : | "break" ";"
            : | "if" "(" `expr` ")" `stmt`
            : | "if" "(" `expr` ")" `stmt` "else" `stmt`
            : | "while" "(" `expr` ")" `loop_body`
            : | "for" "(" `expr_stmt` ";" `expr` ";" `expr_stmt` ")" `loop_body`
            : | `expr_stmt` ";"
            : | `block`
            : | "//@" "label" identifier ";"
            : | "//@" ( "assert" | "assume" | "check" ) `term` ";"
      block: "{" { `stmt` } "}"
  expr_stmt: "int" identifier "=" `expr`
            : | identifier `assignop` `expr`
            : | identifier "[" `expr` "]" `assignop` `expr`
            : | `expr`
   assignop: "=" | "+=" | "-=" | "*=" | "/="
  loop_body: { `loop_annot` } `stmt`
            : | "{" { `loop_annot` } { `stmt` } "}"
 loop_annot: "//@" "invariant" `term` ";"
            : | "//@" "variant" `term` { "," `term` } ";"

Note that the syntax for loop bodies allows the loop annotations to be
placed either before the block or right at the beginning of the block.

.. rubric:: Logic declarations

.. productionlist:: micro-C
    logic_declaration: "//@" "function" "int" identifier "(" `params` ")" ";"
                    : | "//@" "function" "int" identifier "(" `params` ")" "=" `term` ";"
                    : | "//@" "predicate" identifier "(" `params` ")" ";"
                    : | "//@" "predicate" identifier "(" `params` ")" "=" `term` ";"
                    : | "//@" "axiom" identifier ":" `term` ";"
                    : | "//@" "lemma" identifier ":" `term` ";"
                    : | "//@" "goal"  identifier ":" `term` ";"

.. rubric:: Logical term

.. productionlist:: micro-C
    term: identifier
       : | integer-literal
       : | "true"
       : | "false"
       : | "(" `term` ")"
       : | `term` "[" `term` "]"
       : | `term` "[" `term` "<-" `term` "]"
       : | "!" `term`
       : | "old" "(" `term` ")"
       : | "at" "(" `term` "," identifier ")"
       : | "-" `term`
       : | `term` ( "->" | "<->" | "||" | "&&" ) `term`
       : | `term` ( "==" | "!=" | "<" | "<=" | ">" | ">=" ) `term`
       : | `term` ( "+" | "-" | "*" | "/" | "% ) `term`
       : | "if" `term` "then" `term` "else `term`
       : | "let" identifier "=" `term` "in" `term`
       : | ( "forall" | "exists" ) `binder` { "," `binder` } "." `term`
       : | identifier "(" [ `term` { "," `term` } ] ")"
    binder: identifier
       : | identifier "[]"

Built-in functions and predicates
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. rubric:: C code

* `scanf`, with a syntax limited to `scanf("%d", &x)`
* `printf`, limited to `printf(string-literal,
  expr1, ..., exprn)` and assuming that the string literal
  contains exactly n occurrences of `%d` (not checked by Why3).
* `rand()`, returns a pseudo-random integer in the range 0 to
  `RAND_MAX` inclusive.

.. rubric:: Logic

* `int length(int[] a)`, the length of array `a`
* `int occurrence(int v, int[] a)`, the number of occurrences of the
  value `v` in array `a`

Verifying a program
~~~~~~~~~~~~~~~~~~~

Click on the gears button to launch the verification.
Verification conditions (VCs) then appear in the right panel, in
the Task List tab, and
Alt-Ergo is run on each of them with a default time limit (that
can be set in the Settings menu).

When a VC is not proved, there are several options:

* use the contextual menu to rerun Alt-Ergo with a larger time limit
  (e.g. 1000 or 5000 steps instead of 100);
* use the contextual menu to split the VC and rerun Alt-Ergo on each
  sub-VC (split and prove);
* use the Task View tab to investigate the problematic VC,
  for wrong or missing elements of specification (precondition,
  postcondition, invariant);
* add intermediate assertions in the code, using `//@ assert ...;`.



.. _format.micro-Python:

micro-Python
------------

Micro-Python is a valid subset of Python 3. Hence, micro-Python files can be
passed to a Python interpreter.


