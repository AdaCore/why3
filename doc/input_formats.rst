Other Input Formats
===================

Why3 can be used to verify programs written in languages other than
WhyML. Currently, Why3 supports tiny subsets of C and Python,
respectively coined micro-C and micro-Python below. These were
designed for teaching purposes. They come with their own specification
languages, written in special comments.
These input formats are described below.

Any Why3 tool (:why3:tool:`why3 prove`, :why3:tool:`why3 ide`, etc.) can be passed a file
with a suffix `.c` or `.py`, which triggers the corresponding input format.
These input formats can also be used in on-line versions of Why3, at
http://why3.lri.fr/micro-C/ and http://why3.lri.fr/python/, respectively.

.. index:: micro-C
.. _format.micro-C:

micro-C
-------

Micro-C is a valid subset of ANSI C. Hence, micro-C files can be
passed to a C compiler.

Syntax of micro-C
~~~~~~~~~~~~~~~~~

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
     c_function: `return_type` identifier "(" `params`? ")" `spec`* `block`
    return_type: "void" | "int"
         params: `param` ("," `param`)*
          param: "int" identifier | "int" identifier "[]"

.. rubric:: Function specification

.. productionlist:: micro-C
    spec: "//@" "requires" `term` ";"
       : | "//@" "ensures"  `term` ";"
       : | "//@" "variant"  `term` ("," `term`)* ";"

.. rubric:: C expression

.. productionlist:: micro-C
    expr: integer-literal | string-literal
       : | identifier | identifier ( "++" | "--" ) | ( "++" | "--" ) identifier
       : | identifier "[" `expr` "]"
       : | identifier "[" `expr` "]" ( "++" | "--")
       : | ( "++" | "--") identifier "[" `expr` "]"
       : | "-" `expr` | "!" `expr`
       : | `expr` ( "+" | "-" | "*" | "/" | "%" | "==" | "!=" | "<" | "<=" | ">" | ">=" | "&&" | "||" ) `expr`
       : | identifier "(" (`expr` ("," `expr`)*)? ")"
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
      block: "{" `stmt`* "}"
  expr_stmt: "int" identifier "=" `expr`
            : | identifier `assignop` `expr`
            : | identifier "[" `expr` "]" `assignop` `expr`
            : | `expr`
   assignop: "=" | "+=" | "-=" | "*=" | "/="
  loop_body: `loop_annot`* `stmt`
            : | "{" `loop_annot`* `stmt`* "}"
 loop_annot: "//@" "invariant" `term` ";"
            : | "//@" "variant" `term` ("," `term`)* ";"

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

Logic functions are limited to a return type ``int``.

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
       : | ( "forall" | "exists" ) `binder` ("," `binder`)* "." `term`
       : | identifier "(" (`term` ("," `term`)*)? ")"
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


.. index:: Python
.. _format.micro-Python:

micro-Python
------------

Micro-Python is a valid subset of Python 3. Hence, micro-Python files can be
passed to a Python interpreter.

Syntax of micro-Python
~~~~~~~~~~~~~~~~~~~~~~

Notation: In the grammar of micro-Python given below,
special symbols `NEWLINE`, `INDENT`,
and `DEDENT` mark an end of line, the beginning of a new
indentation block, and its end, respectively.

Logical annotations are inserted in special comments starting with `#@`.

.. productionlist:: microPython
      file: `decl`*
      decl: `py_import` | `py_function` | `stmt` | `logic_declaration`
 py_import: "from" identifier "import" identifier ("," identifier)* NEWLINE

Directives `import` are ignored during the translation to
Why3. They are allowed anyway, such that a Python source code using
functions such as `randint` is accepted by a Python
interpreter (see below).

..  rubric:: Function definition

.. productionlist:: microPython
    py_function: "def" identifier "(" [ `params` ] ")" ":" NEWLINE INDENT `spec`* `stmt`* DEDENT
    params: identifier ("," identifier)*

.. rubric:: Function specification

.. productionlist:: microPython
   spec: "#@" "requires" `term` NEWLINE
        : | "#@" "ensures"  `term` NEWLINE
        : | "#@" "variant"  `term` ("," `term`)* NEWLINE

.. rubric:: Python expression

.. productionlist:: microPython
  expr: "None" | "True" | "False" | integer-literal | string-literal
       : | identifier
       : | identifier "[" `expr` "]"
       : | "-" `expr` | "not" `expr`
       : | `expr` ( "+" | "-" | "*" | "//" | "%" | "==" | "!=" | "<" | "<=" | ">" | ">=" | "and" | "or" ) `expr`
       : | identifier "(" (`expr` ("," `expr`)*)? ")"
       : | "[" (`expr` ("," `expr`)*)? "]"
       : | "(" `expr` ")"

.. rubric:: Python statement

.. productionlist:: microPython
       stmt: `simple_stmt` NEWLINE
            : | "if" `expr` ":" `suite` `else_branch`
            : | "while" `expr` ":" `loop_body`
            : | "for" identifier "in" `expr` ":" `loop_body`
    else_branch: /* nothing */
            : | "else:" `suite`
            : | "elif" `expr` ":" `suite` `else_branch`
      suite: `simple_stmt` NEWLINE
            : | NEWLINE INDENT `stmt` `stmt`* DEDENT
  simple_stmt: `expr`
            : | "return" `expr`
            : | identifier "=" `expr`
            : | identifier "[" `expr` "]" "=" `expr`
            : | "break"
            : | "#@" "label" identifier
            : | "#@" ( "assert" | "assume" | "check" ) `term`
  loop_body: `simple_stmt` NEWLINE
            : | NEWLINE INDENT `loop_annot`* `stmt` `stmt`* DEDENT
 loop_annot: "#@" "invariant" `term` NEWLINE
            : | "#@" "variant" `term` ("," `term`)* NEWLINE

.. rubric:: Logic declaration

.. productionlist:: microPython
  logic-declaration: "#@" "function" identifier "(" `params` ")" NEWLINE
                 : | "#@" "predicate" identifier "(" `params` ")" NEWLINE

Note that logic functions and predicates cannot be given definitions.
Yet, they can be axiomatized, using toplevel `assume` statements.


.. rubric:: Logical term

.. productionlist:: microPython
  term: identifier
       : | integer-literal
       : | "None"
       : | "True"
       : | "False"
       : | "(" `term` ")"
       : | `term` "[" `term` "]"
       : | `term` "[" `term` "<-" `term` "]"
       : | "not" `term`
       : | "old" "(" `term` ")"
       : | "at" "(" `term` "," identifier ")"
       : | "-" `term`
       : | `term` ( "->" | "<->" | "or" | "and" ) `term`
       : | `term` ( "==" | "!=" | "<" | "<=" | ">" | ">=" ) `term`
       : | `term` ( "+" | "-" | "*" | "//" | "% ) `term`
       : | "if" `term` "then" `term` "else `term`
       : | "let" identifier "=" `term` "in" `term`
       : | ( "forall" | "exists" ) identifier ("," identifier)* "." `term`
       : | identifier "(" (`term` ("," `term`)*)? ")"

Built-in functions and predicates
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. rubric:: Python code

* `len(l)`, the length of list `l`
* `int(input())`, reads an integer from standard input
* `range(l, u)`, returns the list of integers
  from `l` inclusive to `u` exclusive <br>
  (in particular, `for x in range(l, u):` is supported)
* `randint(l, u)`, returns a pseudo-random integer
  in the range `l` to `u` inclusive

.. rubric:: Logic

* `len(l)`, the length of list `l`
* `occurrence(v, l)`, the number of occurrences of the value `v` in list `l`

Limitations
~~~~~~~~~~~

Python lists are modeled as arrays, whose size cannot be modified.


.. index:: CFG
.. _format.CFG:

CFG: Control-Flow-Graph style function bodies
---------------------------------------------

CFG is an experimental extension of the regular WhyML language, in
which the body of program functions can optionally be coded using
labelled blocks and `goto` statements. CFG can be used to encoded
algorithms which are presented in an unstructured fashion. It can be
also used as a target for encoding unstructured programming languages
in Why3, for example assembly code.

Syntax of CFG
~~~~~~~~~~~~~

The syntax is an extension of the regular WhyML syntax. The additional rules are as follows

.. productionlist:: CFG
    file: `module`*
    module: "module" `ident` `decl`* "end"
    decl: "let" "cfg" `cfg_fundef` ("with" `cfg_fundef`)*
    cfg_fundef: `ident` `binders` : `type` `spec` "=" `vardecl`* `block` `labelblock`*
