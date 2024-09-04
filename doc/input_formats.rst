Other Input Formats
===================

Why3 can be used to verify programs written in languages other than
WhyML. Currently, Why3 supports tiny subsets of C and Python,
respectively coined micro-C and micro-Python below. These were
designed for teaching purposes. They come with their own specification
languages, written in special comments.
These input formats are described below.

Why3 also supports the format MLCFG, which is an extension of WhyML
allowing to define function bodies in an unstructured style, with goto
statements.

Why3 also supports the format Coma (which stands for Continuation Machine).
Coma is an Intermediate Verification Language implemented as a plugin in the
Why3 platform.

Any Why3 tool (:why3:tool:`why3 prove`, :why3:tool:`why3 ide`, etc.)
can be passed a file with a suffix :file:`.c`, :file:`.py`, :file:`.coma` or
:file:`.mlcfg`, which triggers the corresponding input format.

.. index:: micro-C
.. _format.micro-C:

micro-C
-------

Micro-C is a valid subset of ANSI C. Hence, micro-C files can be
passed to a C compiler.

Syntax of micro-C
~~~~~~~~~~~~~~~~~

Logical annotations are inserted in special comments starting
with ``//@`` or ``/*@``. In the following grammar, we
only use the former kind, for simplicity, but both kinds are allowed.

.. productionlist:: micro-C
    file: `decl`*
    decl: `c_include` | `c_function` | `logic_declaration`
    c_include: "#include" "<" file-name ">"

Directives ``#include`` are ignored during the translation to
Why3. They are allowed anyway, such that a C source code using
functions such as ``printf`` (see below) is accepted by a C compiler.

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
       : | "scanf" "(" '"%d"' "," "&" identifier ")"
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

* ``scanf`` is limited to the syntax ``scanf("%d", &x)``.
* ``printf`` is limited to ``printf(string-literal,
  expr1, ..., exprn)``. The string literal should
  contain exactly ``n`` occurrences of ``%d`` (not checked by Why3).
* ``rand()`` returns a pseudo-random integer in the range ``0`` to
  ``RAND_MAX`` inclusive.

.. rubric:: Logic

* ``int length(int a[])`` returns the length of array ``a``.
* ``int occurrence(int v, int a[])`` returns the number of occurrences of the
  value ``v`` in array ``a``.


.. index:: Python
.. _format.micro-Python:

micro-Python
------------

Micro-Python is a valid subset of Python 3. Hence, micro-Python files can be
passed to a Python interpreter.

Syntax of micro-Python
~~~~~~~~~~~~~~~~~~~~~~

Notation: In the grammar of micro-Python given below,
special symbols ``NEWLINE``, ``INDENT``,
and ``DEDENT`` mark an end of line, the beginning of a new
indentation block, and its end, respectively.

Logical annotations are inserted in special comments starting with ``#@``.

.. productionlist:: microPython
   file: `decl`*
   decl: `py_import` | `py_constant` | `py_function` | `stmt` | `logic_declaration`
   py_import: "from" identifier "import" identifier ("," identifier)* NEWLINE

Directives ``import`` are ignored during the translation to
Why3. They are allowed anyway, such that a Python source code using
functions such as ``randint`` is accepted by a Python
interpreter (see below).

..  rubric:: Constant definition

.. productionlist:: microPython
    py_constant: "#@" "constant" NEWLINE identifier "=" `expr` NEWLINE

..  rubric:: Function definition

.. productionlist:: microPython
    py_function: `logic_def`? "def" identifier "(" `params`? ")" `return_type`? ":" NEWLINE INDENT `spec`* `stmt`* DEDENT
    params: `param` ("," `param`)*
    param: identifier (":" `py_type`)?
    return_type: "->" `py_type`
    py_type: identifier ("[" `py_type` ("," `py_type`)* "]")?
          : | "'" identifier

.. rubric:: Function specification

.. productionlist:: microPython
   logic_def: "#@" "function" NEWLINE
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
       : | `expr` ("," `expr`)+
       : | "[" (`expr` ("," `expr`)*)? "]"
       : | `expr` "if" `expr` "else" `expr`
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
   logic_declaration: "#@" "function" identifier "(" `params` ")" `return_type`? ("variant" "{" `term` "}")? ("=" `term`)? NEWLINE
                 : | "#@" "predicate" identifier "(" `params` ")" ("=" `term`)? NEWLINE
                 : | "#@" "axiom" identifier ":" `term` NEWLINE
                 : | "#@" "lemma" identifier ":" `term` NEWLINE

Note that logic functions and predicates cannot be given definitions.
Yet, they can be axiomatized, using toplevel ``assume`` statements.


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
       : | `term` ( "->" | "<->" | "or" | "and" | "by" | "so" ) `term`
       : | `term` ( "==" | "!=" | "<" | "<=" | ">" | ">=" ) `term`
       : | `term` ( "+" | "-" | "*" | "//" | "%" ) `term`
       : | "if" `term` "then" `term` "else `term`
       : | "let" identifier "=" `term` "in" `term`
       : | ( "forall" | "exists" ) param ("," param)* "." `term`
       : | identifier "(" (`term` ("," `term`)*)? ")"

Built-in functions and predicates
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. rubric:: Python code

* built-in function ``pow`` over integers
* ``len(l)`` returns the length of list ``l``.
* ``int(input())`` reads an integer from standard input.
* ``range(l, u)`` returns the list of integers
  from ``l`` inclusive to ``u`` exclusive.
  In particular, ``for x in range(l, u):`` is supported.
* ``randint(l, u)`` returns a pseudo-random integer
  in the range ``l`` to ``u`` inclusive.

.. rubric:: Logic

* ``len(l)`` returns the length of list ``l``.
* ``occurrence(v, l)`` returns the number of occurrences of the value ``v`` in list ``l``.

Limitations
~~~~~~~~~~~

Python lists are modeled as arrays, whose size cannot be modified.



.. index:: CFG
.. _format.CFG:

MLCFG
-----

The MLCFG language is an experimental extension of the regular WhyML
language, in which the body of program functions can be
coded using labelled blocks and goto statements. MLCFG can be used to
encode algorithms which are presented in an unstructured fashion. It
can also be used as a target for encoding unstructured programming
languages in Why3, for example assembly code.


Syntax of the MLCFG language
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The MLCFG syntax is an extension of the regular WhyML syntax. Every
WhyML declaration is allowed, plus an additional declaration of
program function of the following form, introduced by keywords ``let cfg``:

.. parsed-literal::

   let cfg *f* (*x*:sub:`1`: *t*:sub:`1`) ... (*x*:sub:`n`: *t*:sub:`n`): *t*
     requires { *Pre* }
     ensures  { *Post* }
   =
    var *y*:sub:`1`: *u*:sub:`1`;
    ...
    var *y*:sub:`k`: *u*:sub:`k`;
    { *instructions*; *terminator* }
    *L*:sub:`1` { *instructions*:sub:`1`; *terminator*:sub:`1` }
    ...
    *L*:sub:`j` { *instructions*:sub:`j`; *terminator*:sub:`j` }


It defines a program function *f*, with the usual syntax for
its contract. The difference is the body, which is made of a sequence
of declarations of mutable variables with their types, an initial block,
composed of a zero or more instructions followed by a terminator, and a
sequence of other blocks, each denoted by a label (:math:`L_1 \ldots L_j` above).
The instructions are semi-colon separated sequences of regular
WhyML expressions of type ``unit``, excluding ``return`` or ``absurd``
expressions, or code invariants:

- a code invariant: :samp:`invariant {I} \\{ {t} }` where *I* is a
  name and *t* a predicate. It is similar to an assert expression,
  meaning that *t* must hold when execution reaches this statement.
  Additionally, it acts as a cut in the generation of VC, similarly
  to a loop invariant. See example below.

Each block is ended by one of the following terminators:

- a ``goto`` statement: :samp:`goto {L}` where *L* is one of the labels of the
  other blocks. It instructs to continue execution at the
  given block.

- a ``switch`` statement, of the form

  .. parsed-literal::

     switch (*e*)
     | *pat*:sub:`1` -> *terminator*:sub:`1`
     ...
     | *pat*:sub:`k` -> *terminator*:sub:`k`
     end

- a ``return`` statement: :samp:`return {expr}`
- an ``absurd`` statement: indicating that this block should be unreachable.

The extension of syntax is described by the following rules.

.. productionlist:: CFG
    file: `module`*
    module: "module" `:ident` `decl`* "end"
    decl: "let" "cfg" `cfg_fundef`
    : | "let" "rec" "cfg" `cfg_fundef` ("with" `cfg_fundef`)*
    : | "scope" `:ident` `decl`* "end"
    cfg_fundef: `:ident` `:binder`+ : `:type` `:spec` "=" `vardecl`* "{" `block` "}" `labelblock`*
    vardecl: "var" `:ident`* ":" `:type` ";" | "ghost" "var" `:ident`* ":" `:type` ";"
    block: (`instruction` ";")* `terminator`
    labelblock: `:ident` "{" `block` "}"
    instruction: `:expr`
    : | "invariant" `:ident` "{" `:term` "}"
    terminator:
    : | "return" `:expr`
    : | "absurd"
    : | "goto" `:ident`
    : | "switch" "(" `:expr` ")" `switch_case`* "end"
    switch_case: "|" `:pattern` "->" `terminator`



An example
~~~~~~~~~~

The following example is directly inspired from the documentation of
the ANSI C Specification Language (See :cite:`baudin18acsl`, Section
2.4.2 Loop invariants, Example 2.27). It is itself inspired from the
first example of Knuth's MIX language, for which formal proofs were
first investigated by J.-C. Filliâtre in 2007
(:cite:`filliatre07mix`), and also revisited by T.-M.-T. Nguyen in her
PhD thesis in 2012 (:cite:`nguyen12phd`, Section 9.5 Translation from
a CFG to Why, page 115).

This example aims at computing the maximum value of
an array of integers. Its code in C is given below.

.. code-block:: C

   /*@ requires n >= 0 && \valid(a,0,n);
     @ ensures \forall integer j ; 0 <= j < n ==> \result >= a[j]);
     @*/
   int max_array(int a[], int n) {
     int m, i = 0;
     goto L;
     do {
       if (a[i] > m) { L: m = a[i]; }
       /*@ invariant
         @   0 <= i < n && \forall integer j ; 0 <= j <= i ==> m >= a[j]);
         @*/
       i++;
     }
     while (i < n);
     return m;
   }

The code can be viewed as a control-flow graph as shown in :numref:`fig.cfg.max_array`.

.. graphviz:: images/max_array.dot
   :caption: Control-flow graph of the ``max_array`` function.
   :name: fig.cfg.max_array

Below is a version of this code in the MLCFG language, where label
``L`` corresponds to node ``L``, label ``L1`` to node ``invariant``,
label ``L2`` to node ``do``.

.. code-block:: whyml

  let cfg max_array (a:array int) : (max: int, ghost ind:int)
    requires { length a > 0 }
    ensures  { 0 <= ind < length a }
    ensures  { forall j. 0 <= j < length a -> a[ind] >= a[j] }
  =
  var i m: int;
  ghost var ind: int;
  {
    i <- 0;
    goto L
  }
  L {
    m <- a[i];
    ind <- i;
    goto L1
  }
  L1 {
    invariant i_bounds   { 0 <= i < length a };
    invariant ind_bounds { 0 <= ind < length a };
    invariant m_and_ind  { m = a[ind] };
    invariant m_is_max   { forall j. 0 <= j <= i -> m >= a[j] };
                           (* yes, j <= i, not j < i ! *)
    i <- i + 1;
    switch (i < length a)
    | True  -> goto L2
    | False -> return (m, ind)
    end
  }
  L2 {
    switch (a[i] > m)
    | True  -> goto L
    | False -> goto L1
    end
  }

The consecutive invariants act as a single cut in the generation of VCs.


Error messages
~~~~~~~~~~~~~~

The translation from the MLCFG language to regular WhyML code may raise
the following errors.

- “cycle without invariant”: in order to perform the translation, any
  cycle on the control-flow graph must contain at least one
  ``invariant`` clause. It corresponds to the idea that any loop must
  contain a loop invariant.

- “cycle without invariant (starting from `I`)”: same error as
  above, except that the cycle was not reachable from the start of the
  function body, but from the other ``invariant`` clause named
  :math:`I`.

- “label `L` not found for goto”: there is a ``goto`` instruction
  to a non-existent label.

- “unreachable code after goto”: any code occurring after a ``goto``
  statement is unreachable and is not allowed.

- “unsupported: trailing code after switch”: see limitations below.


Current limitations
~~~~~~~~~~~~~~~~~~~

- There is no way to prove termination.

- New keywords ``cfg``, ``goto``, ``switch``, and ``var`` cannot be used as
  regular identifiers anymore.

- Trailing code after ``switch`` is not supported. In principle, it
  should be possible to have a ``switch`` with type ``unit`` and to transfer
  the execution to the instructions after the ``switch`` for branches
  not containing ``goto``. This is not
  yet supported. A workaround is to place the trailing instructions in
  another block and pose an extra ``goto`` to this block in all the
  branches that do not end with a ``goto``.

- Conditional statements ``if e then i1 else i2`` are not yet
  supported, but can be simulated with ``switch (e) | True -> i1 |
  False -> i2 end``.

Alternative translation scheme: Stackify
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

An alternative translation scheme from MLCFG to regular WhyML
can be triggered by putting the attribute :why3:attribute:`[@cfg:stackify]` on
a function. This method attempts to recover a more
structured program body, reconstructing loops when possible.


Subregion analysis
~~~~~~~~~~~~~~~~~~

Additional invariants on the generated WhyML code can be inferred by
putting the attribute :why3:attribute:`[@cfg:subregion_analysis]` on a
function. These invariants are derived by a static analysis of the
subregions that are never modified in a loop.


.. index:: S-expressions
.. _format.S-expressions:

S-expressions
-------------

This format is intended to be used only as an intermediate language
format. Why3 accepts input files in the format of a big S-expression,
mirroring the internal structure of parse trees, as they are defined
in the module ``Ptree`` of the OCaml API. The S-expression in question
is supposed to be generated by the API itself, that is the function
``Ptree.sexp_of_mlw_file``. It is in fact exactly the format that is
also printed using :option:`why3 pp --output` with ``--output=sexp``.

Notice that this input format is available only when Why3 is compiled
with S-expressions support provided by the ``ppx_sexp_conv`` OCaml
library.

Concerning the use of Why3 as an intermediate language, via the
``Ptree`` API, the use of S-expressions instead of the regular WhyML
syntax is recommended since the printing and re-parsing of parse trees
is automatically generated, hence the result is guaranteed to
faithfully mirror the internal Ptree representation.

.. index:: Coma
.. _format.Coma:

Coma
-----

The Coma documentation is described in https://coma-ivl.codeberg.page/.
