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

MLCFG: Function Bodies on the Style of Control-Flow Graphs
----------------------------------------------------------

The MLCFG language is an experimental extension of the regular WhyML
language, in which the body of program functions can be
coded using labelled blocks and goto statements. MLCFG can be used to
encode algorithms which are presented in an unstructured fashion. It
can also be used as a target for encoding unstructured programming
languages in Why3, for example assembly code.


Syntax of the MLCFG language
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The MLCFG syntax is an extension of the regular WhyML syntax: every
WhyML declaration is allowed, plus an additional declaration of
program function of the following form, introduced by keywords ``let cfg``:

| ``let cfg`` :math:`f (x_1:t_1) ... (x_n:t_n) : t`
|   ``requires`` { :math:`Pre` }
|   ``ensures``  { :math:`Post` }
|   ``=``
|   ``var`` :math:`y_1 : u_1`;
|   :math:`\vdots`
|   ``var`` :math:`y_k : u_k`;
|   {
|     :math:`instructions`
|   }
|   :math:`L_1`
|   {
|     :math:`instructions`
|   }
|   :math:`\vdots`
|   :math:`L_j`
|   {
|     :math:`instructions`
|   }

It defines a program function `f`, with the usual syntax for
its contract. The difference is the body, which is made of a sequence
of declarations of mutable variables with their types, an initial block
of instructions, and a sequence of other blocks of instructions, each
block being denoted by a label (:math:`L_1 \ldots L_j` above). The
instructions are semi-colon separated sequences of either regular
WhyML expressions of type ``unit`` (apart from the last one in the
sequence, when returning a value), or CFG-specific instructions below:

- a ``goto`` statement: ``goto L`` where ``L`` is one of the label of the
  other blocks. It instructs to continue execution at the
  given block.

- a code invariant: ``invariant`` `I` ``{`` `t` ``}`` where `I` is a
  name and `t`
  a predicate. It is similar to an assert expression, meaning that `t`
  must hold when execution reaches this statement. Additionally, it
  acts as a cut in the generation of VC, similarly to a loop
  invariant. See example below.

- a ``switch`` statement, of the form

  | ``switch`` ``(`` :math:`e` ``)``
  | ``|`` :math:`pat_1` ``->`` :math:`instructions_1`
  | :math:`\vdots`
  | ``|`` :math:`pat_k` ``->`` :math:`instructions_k`
  | ``end``

  It is similar to a ``match ... with ... end`` expression, except that
  the branches may recursively contain CFG instructions.

The extension of syntax is described by the following rules.

.. productionlist:: CFG
    file: `module`*
    module: "module" `ident` `decl`* "end"
    decl: "let" "cfg" `cfg_fundef` ("with" `cfg_fundef`)*
    cfg_fundef: `ident` `binder`+ : `type` `spec` "=" `vardecl`* "{" `block` "}" `labelblock`*
    vardecl: "var" `ident`* ":" `type` ";" | "ghost" "var" `ident`* ":" `type` ";"
    block: `instruction` (";" `instruction`)*
    labelblock: `ident` "{" `block` "}"
    instruction: `expr`
    : | "goto" `ident`
    : | "invariant" `ident` "{" `term` "}"
    : | "switch" "(" `expr` ")" `switch_case`* "end"
    switch_case: "|" `pattern` "->" `block`



An example
~~~~~~~~~~

The following example is inspired from the documentation of the ANSI C
Specification Language (See :cite:`baudin18acsl`, section 2.4.2 Loop
invariants, Example 2.27). It aims at computing the maximum value of
an array of integers.

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
   :caption: Control-flow graph of "max_array" example.
   :name: fig.cfg.max_array

Below is a version of this code in the Why3-CFG language, where label
"L" corresponds
to node "L", label "L1" to node "invariant", label "L2" to node "do".

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
    | False -> (m, ind)
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

The translation from the CFG language to regular WhyML code may raise
the following errors.

- "cycle without invariant": in order to perform the translation, any
  cycle on the control-flow graph must contain at least one
  "invariant" clause. It corresponds to the idea that any loop must
  contain a loop invariant.

- "cycle without invariant (starting from :math:`I`)": same error as
  above, except that the cycle was not reachable from the start of the
  function body, but from the other "invariant" clause named
  :math:`I`.

- "label :math:`L` not found for goto": there is a goto instruction
  to a non-existent label.

- "unreachable code after goto": any code occuring after a goto
  statement is unreachable and is not allowed.

- "unsupported: trailing code after switch": see limitations below.


Current Limitations
~~~~~~~~~~~~~~~~~~~

- There is no way to prove termination.

- New keywords "cfg", "goto", "switch" and "var" cannot be used as
  regular identifiers anymore.

- Trailing code after "switch" is not supported: in principle, it
  should be possible to have a ``switch`` with type ``unit`` and to transfer
  the execution to the instructions after the ``switch`` for branches
  not containing ``goto``. This is not
  yet supported. A workaround is to place the trailing instructions in
  another block and pose an extra ``goto`` to this block in all the
  branches that do not end with a ``goto``.

- Conditional statements ``if e then i1 else i2`` are not yet
  supported, but can be simulated with ``switch (e) | True -> i1 |
  False -> i2 end``.
