The WhyML Language Reference
============================

In this chapter, we describe the syntax and semantics of WhyML.

Lexical Conventions
-------------------

Blank characters are space, horizontal tab, carriage return, and line
feed. Blanks separate lexemes but are otherwise ignored. Comments are
enclosed by ``(*`` and ``*)`` and can be nested. Note that ``(*)`` does
not start a comment.

Strings are enclosed in double quotes (``"``). The backslash character
``\``, is used for escaping purposes. The following
escape sequences are allowed:

- ``\`` followed by a *new line* allows for
  multi-line strings. The leading spaces immediately after the new
  line are ignored.
- ``\\`` and ``\"`` for the backslash and double quote respectively.
- ``\n``, ``\r``, and
  ``\t`` for the new line feed, carriage return,
  and horizontal tab character.
- ``\DDD``, ``\oOOO``, and
  ``\xXX``, where ``DDD`` is a decimal value
  in the interval 0-255, ``OOO`` an octal value in the
  interval 0-377, and ``XX`` an hexadecimal value.
  Sequences of this form can be used to encode Unicode characters, in
  particular non printable ASCII characters.
- any other escape sequence results in a parsing error.

The syntax for numerical constants is given by the following rules:

.. productionlist::
    digit: "0" - "9"
    hex_digit: "0" - "9" | "a" - "f" | "A" - "F"
    oct_digit: "0" - "7"
    bin_digit: "0" | "1"
    integer: `digit` (`digit` | "_")*
      : | ("0x" | "0X") `hex_digit` (`hex_digit` | "_")*
      : | ("0o" | "0O") `oct_digit` (`oct_digit` | "_")*
      : | ("0b" | "0B") `bin_digit` (`bin_digit` | "_")*
    real: `digit`+ `exponent`
      : | `digit`+ "." `digit`* `exponent`?
      : | `digit`* "." `digit`+ `exponent`?
      : | ("0x" | "0X") `hex_digit`+ `h_exponent`
      : | ("0x" | "0X") `hex_digit`+ "." `hex_digit`* `h_exponent`?
      : | ("0x" | "0X") `hex_digit`* "." `hex_digit`+ `h_exponent`?
    exponent: ("e" | "E") ("-" | "+")? `digit`+
    h_exponent: ("p" | "P") ("-" | "+")? `digit`+
    char: "a" - "z" | "A" - "Z" | "0" - "9"
      : | " " | "!" | "#" | "$" | "%" | "&" | "'" | "("
      : | ")" | "*" | "+" | "," | "-" | "." | "/" | ":"
      : | ";" | "<" | "=" | ">" | "?" | "@" | "[" | "]"
      : | "^" | "_" | "`" | "\\" | "\n" | "\r" | "\t" | '\"'
      : | "\" ("0" | "1") `digit` `digit`
      : | "\" "2" ("0" - "4") `digit`
      : | "\" "2" "5" ("0" - "5")
      : | "\x" `hex_digit` `hex_digit`
      : | "\o" ("0" - "3" ) `oct_digit` `oct_digit`
    string: '"' `char`* '"'


Integer and real constants have arbitrary precision. Integer constants
can be given in base 10, 16, 8 or 2. Real constants can be given in
base 10 or 16. Notice that the exponent in hexadecimal real constants
is written in base 10.

Identifiers are composed of letters, digits, underscores, and primes.
The syntax distinguishes identifiers that start with a lowercase letter
or an underscore (:token:`lident_nq`), identifiers that start with an
uppercase letter (:token:`uident_nq`), and identifiers that start with
a prime (:token:`qident`, used exclusively for type variables):

.. productionlist::
    alpha: "a" - "z" | "A" - "Z"
    suffix: (`alpha` | "'"* ("0" - "9" | "_")*)* "'"*
    lident_nq: ("a" - "z") `suffix`* | "_" `suffix`+
    uident_nq: ("A" - "Z") `suffix`*
    ident_nq: `lident_nq` | `uident_nq`
    qident: "'" ("a" - "z") `suffix`*


Identifiers that contain a prime followed by a letter, such as
``int32'max``, are reserved for symbols introduced by Why3 and cannot be
used for user-defined symbols.

.. productionlist::
    lident: `lident_nq` ("'" `alpha` `suffix`)*
    uident: `lident_nq` ("'" `alpha` `suffix`)*
    ident: `lident` | `uident`

In order to refer to symbols introduced in different namespaces
(*scopes*), we can put a dot-separated “qualifier prefix” in front of an
identifier (e.g., ``Map.S.get``). This allows us to use the symbol
``get`` from the scope ``Map.S`` without importing it in the current
namespace:

.. productionlist::
    qualifier: (`uident` ".")+
    lqualid: `qualifier`? `lident`
    uqualid: `qualifier`? `uident`


All parenthesised expressions in WhyML (types, patterns, logical terms,
program expressions) admit a qualifier before the opening parenthesis,
e.g., ``Map.S.(get m i)``. This imports the indicated scope into the
current namespace during the parsing of the expression under the
qualifier. For the sake of convenience, the parentheses can be omitted
when the expression itself is enclosed in parentheses, square brackets
or curly braces.

Prefix and infix operators are built from characters organized in four
precedence groups (:token:`op_char_1` to :token:`op_char_4`), with optional primes at
the end:

.. productionlist::
    op_char_1: "=" | "<" | ">" | "~"
    op_char_2: "+" | "-"
    op_char_3: "*" | "/" | "\" | "%"
    op_char_4: "!" | "$" | "&" | "?" | "@" | "^" | "." | ":" | "|" | "#"
    op_char_1234: `op_char_1` | `op_char_2` | `op_char_3` | `op_char_4`
    op_char_234: `op_char_2` | `op_char_3` | `op_char_4`
    op_char_34: `op_char_3` | `op_char_4`
    infix_op_1: `op_char_1234`* `op_char_1` `op_char_1234`* "'"*
    infix_op_2: `op_char_234`* `op_char_2` `op_char_234`* "'"*
    infix_op_3: `op_char_34`* `op_char_3` `op_char_34`* "'"*
    infix_op_4: `op_char_4`+ "'"*
    prefix_op: `op_char_1234`+ "'"*
    tight_op: ("!" | "?") `op_char_4`* "'"*


Infix operators from a high-numbered group bind stronger than the infix
operators from a low-numbered group. For example, infix operator ``.*.``
from group 3 would have a higher precedence than infix operator ``->-``
from group 1. Prefix operators always bind stronger than infix
operators. The so-called “tight operators” are prefix operators that
have even higher precedence than the juxtaposition (application)
operator, allowing us to write expressions like ``inv !x`` without
parentheses.

Finally, any identifier, term, formula, or expression in a
WhyML source can be tagged either with a string :token:`attribute` or a
location:

.. productionlist::
    attribute: "[@" ... "]"
             : | "[#" `string` `digit`+ `digit`+ `digit`+ "]"


An attribute cannot contain newlines or closing square brackets; leading
and trailing spaces are ignored. A location consists of a file name in
double quotes, a line number, and starting and ending character
positions.

Type expressions
----------------

WhyML features an ML-style type system with polymorphic types, variants
(sum types), and records that can have mutable fields. The syntax for
type expressions is the following:

.. productionlist::
    type: `lqualid` `type_arg`+   ; polymorphic type symbol
        : | `type` "->" `type`   ; mapping type (right-associative)
        : | `type_arg`
    type_arg: `lqualid`   ; monomorphic type symbol (sort)
            : | `qident`   ; type variable
            : | "()"   ; unit type
            : | "(" `type` ("," `type`)+ ")"   ; tuple type
            : | "{" `type` "}"   ; snapshot type
            : | `qualifier`? "(" `type` ")"   ; type in a scope

.. index:: mapping type

Built-in types are ``int`` (arbitrary precision integers), ``real``
(real numbers), ``bool``, the arrow type (also called the *mapping
type*), and the tuple types. The empty tuple type is also called the
*unit type* and can be written as ``unit``.

Note that the syntax for type expressions notably differs from the usual
ML syntax. In particular, the type of polymorphic lists is written
``list 'a``, and not ``'a list``.

.. index:: snapshot type

*Snapshot types* are specific to WhyML, they denote the types of ghost
values produced by pure logical functions in WhyML programs. A snapshot
of an immutable type is the type itself; thus, ``{int}`` is the same as
``int`` and ``{list 'a}`` is the same as ``list 'a``. A snapshot of a
mutable type, however, represents a snapshot value which cannot be
modified anymore. Thus, a snapshot array ``a`` of type ``{array int}``
can be read from (``a[42]`` is accepted) but not written into
(``a[42] <- 0`` is rejected). Generally speaking, a program function
that expects an argument of a mutable type will accept an argument of
the corresponding snapshot type as long as it is not modified by the
function.

Logical expressions
-------------------

A significant part of a typical WhyML source file is occupied by
non-executable logical content intended for specification and proof:
function contracts, assertions, definitions of logical functions and
predicates, axioms, lemmas, etc.


Terms and Formulas
^^^^^^^^^^^^^^^^^^

Logical expressions are called *terms*. Boolean terms are called
*formulas*. Internally, Why3 distinguishes the proper formulas (produced
by predicate symbols, propositional connectives and quantifiers) and the
terms of type ``bool`` (produced by Boolean variables and logical
functions that return ``bool``). However, this distinction is not
enforced on the syntactical level, and Why3 will perform the necessary
conversions behind the scenes.

The syntax of WhyML terms is given in :token:`term`.


.. productionlist::
    term0: `integer`   ; integer constant
        : | `real`   ; real constant
        : | "true" | "false"   ; Boolean constant
        : | "()"   ; empty tuple
        : | `string` ; string constant
        : | `qualid`   ; qualified identifier
        : | `qualifier`? "(" `term` ")"   ; term in a scope
        : | `qualifier`? "begin" `term` "end"   ; idem
        : | `tight_op` `term`   ; tight operator
        : | "{" `term_field`+ "}"   ; record
        : | "{" `term` "with" `term_field`+ "}"   ; record update
        : | `term` "." `lqualid`   ; record field access
        : | `term` "[" `term` "]" "'"*   ; collection access
        : | `term` "[" `term` "<-" `term` "]" "'"*   ; collection update
        : | `term` "[" `term` ".." `term` "]" "'"*   ; collection slice
        : | `term` "[" `term` ".." "]" "'"*   ; right-open slice
        : | `term` "[" ".." `term` "]" "'"*   ; left-open slice
        : | "[|" (`term` "=>" `term` ";")* ("_" "=>" `term`)? "|]" ; function literal
        : | "[|" (`term` ";")+ "|]" ; function literal (domain over nat)
        : | `term` `term`+   ; application
        : | `prefix_op` `term`   ; prefix operator
        : | `term` `infix_op_4` `term`   ; infix operator 4
        : | `term` `infix_op_3` `term`   ; infix operator 3
        : | `term` `infix_op_2` `term`   ; infix operator 2
        : | `term` "at" `uident`   ; past value
        : | "old" `term`   ; initial value
        : | `term` `infix_op_1` `term`   ; infix operator 1
        : | "not" `term`   ; negation
        : | `term` "/\" `term`   ; conjunction
        : | `term` "&&" `term`   ; asymmetric conjunction
        : | `term` "\/" `term`   ; disjunction
        : | `term` "||" `term`   ; asymmetric disjunction
        : | `term` "by" `term`   ; proof indication
        : | `term` "so" `term`   ; consequence indication
        : | `term` "->" `term`   ; implication
        : | `term` "<->" `term`   ; equivalence
        : | `term` ":" `type`   ; type cast
        : | `attribute`+ `term`   ; attributes
        : | `term` ("," `term`)+   ; tuple
        : | `quantifier` `quant_vars` `triggers`? "." `term`   ; quantifier
        : | ...   ; (to be continued in `term`)
    formula: `term`   ; no distinction as far as syntax is concerned
    term_field: `lqualid` "=" `term` ";"   ; field = value
    qualid: `qualifier`? (`lident_ext` | `uident`)   ; qualified identifier
    lident_ext: `lident`   ; lowercase identifier
              : | "(" `ident_op` ")"   ; operator identifier
              : | "(" `ident_op` ")" ("_" | "'") alpha suffix*   ; associated identifier
    ident_op:  `infix_op_1`   ; infix operator 1
            : | `infix_op_2`   ; infix operator 2
            : | `infix_op_3`   ; infix operator 3
            : | `infix_op_4`   ; infix operator 4
            : | `prefix_op` "_"   ; prefix operator
            : | `tight_op` "_"?   ; tight operator
            : | "[" "]" "'" *   ; collection access
            : | "[" "<-" "]" "'"*   ; collection update
            : | "[" "]" "'"* "<-"   ; in-place update
            : | "[" ".." "]" "'"*   ; collection slice
            : | "[" "_" ".." "]" "'"*   ; right-open slice
            : | "[" ".." "_" "]" "'"*   ; left-open slice
    quantifier: "forall" | "exists"
    quant_vars: `quant_cast` ("," `quant_cast`)*
    quant_cast: `binder`+ (":" `type`)?
    binder: "_" | `bound_var`
    bound_var: `lident` `attribute`*
    triggers: "[" `trigger` ("|" `trigger`)* "]"
    trigger: `term` ("," `term`)*


The various
constructs have the following priorities and associativities, from
lowest to greatest priority:

+------------------------------------+-----------------+
| construct                          | associativity   |
+====================================+=================+
| ``if then else`` / ``let in``      | –               |
+------------------------------------+-----------------+
| attribute                          | –               |
+------------------------------------+-----------------+
| cast                               | –               |
+------------------------------------+-----------------+
| ``->`` / ``<->`` / ``by`` / ``so`` | right           |
+------------------------------------+-----------------+
| ``\/`` / ``||``                    | right           |
+------------------------------------+-----------------+
| ``/\`` / ``&&``                    | right           |
+------------------------------------+-----------------+
| ``not``                            | –               |
+------------------------------------+-----------------+
| infix-op level 1                   | right           |
+------------------------------------+-----------------+
| ``at`` / ``old``                   | –               |
+------------------------------------+-----------------+
| infix-op level 2                   | left            |
+------------------------------------+-----------------+
| infix-op level 3                   | left            |
+------------------------------------+-----------------+
| infix-op level 4                   | left            |
+------------------------------------+-----------------+
| prefix-op                          | –               |
+------------------------------------+-----------------+
| function application               | left            |
+------------------------------------+-----------------+
| brackets / ternary brackets        | –               |
+------------------------------------+-----------------+
| bang-op                            | –               |
+------------------------------------+-----------------+

For example, as was mentioned above,
tight operators have the highest precedence of all operators, so that
``-p.x`` denotes the negation of the record field ``p.x``, whereas
``!p.x`` denotes the field ``x`` of a record stored in the reference
``p``.

Infix operators from groups 2-4 are left-associative. Infix operators
from group 1 are right-associative and can be chained. For example, the
term ``0 <= i < j < length a`` is parsed as the conjunction of three
inequalities ``0 <= i``, ``i < j``, and ``j < length a``.
Note that infix symbols of level 1 include equality (``=``) and
disequality (``<>``).

An operator in parentheses acts as an identifier referring to that
operator, for example, in a definition. To distinguish between prefix
and infix operators, an underscore symbol is appended at the end: for
example, ``(-)`` refers to the binary subtraction and ``(-_)`` to the
unary negation. Tight operators cannot be used as infix operators, and
thus do not require disambiguation.

As with normal identifiers, we can put a qualifier over a parenthesised
operator, e.g., ``Map.S.([]) m i``. Also, as noted above, a qualifier
can be put over a parenthesised term, and the parentheses can be omitted
if the term is a record or a record update.

Note the curryfied syntax for function application, though partial
application is not allowed (rejected at typing).

.. _rubric.collections_syntax:

.. index:: bracket; syntax
.. index:: collections; syntax; function literals

Specific syntax for collections
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In addition to prefix and infix operators, WhyML supports several mixfix
bracket operators to manipulate various collection types: dictionaries,
arrays, sequences, etc.

Bracket operators do not have any predefined
meaning and may be used to denote access and update operations for
various user-defined collection types. We can introduce multiple bracket
operations in the same scope by disambiguating them with primes after
the closing bracket: for example, ``a[i]`` may denote array access and
``s[i]'`` sequence access. Notice that the in-place update operator
``a[i] <- v`` cannot be used inside logical terms: all effectful
operations are restricted to program expressions. To represent the
result of a collection update, we should use a pure logical update
operator ``a[i <- v]`` instead. WhyML supports “associated” names for
operators, obtained by adding a suffix after the parenthesised operator
name. For example, an axiom that represents the specification of the
infix operator ``(+)`` may be called ``(+)'spec`` or ``(+)_spec``. As
with normal identifiers, names with a letter after a prime, such as
``(+)'spec``, can only be introduced by Why3, and not by the user in a
WhyML source.

WhyML provides a special syntax for `function literals`. The term
``[|t1 => u1; ...; tn => un; _ => default|]``, where ``t1, ..., tn``
have some type ``t`` and ``u1, ..., un, default`` some type ``u``,
represents a total function of the form ``fun x -> if x = t1 then u1
else if ... else if x = tn then un else default``. The default value
can be omitted in which case the last value will be taken as the
default value. For instance, the function literal ``[|t1 => u1|]``
represents the term ``fun x -> if x = t1 then u1 else u1``. When the
domain of the function ranges over an initial sequence of the natural
numbers it is possible to write ``[|t1;t2;t3|]`` as a shortcut for
``[|0 => t1; 1 => t2; 2 => t3|]``.  Function literals cannot be empty.

.. index:: at; syntax
.. index:: old; syntax

The "at" and "old" operators
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The ``at`` and ``old`` operators are used inside postconditions and
assertions to refer to the value of a mutable program variable at some
past moment of execution (see the next section for details). These
operators have higher precedence than the infix operators from group 1
(:token:`infix_op_1`): ``old i > j`` is parsed as ``(old i) > j`` and not as
``old (i > j)``.

.. index:: &&, ||, by, so

Non-standard connectives
^^^^^^^^^^^^^^^^^^^^^^^^

The propositional connectives in WhyML formulas are listed in
:token:`term`. The non-standard connectives — asymmetric
conjunction (``&&``), asymmetric disjunction (``||``), proof indication
(``by``), and consequence indication (``so``) — are used to control the
goal-splitting transformations of Why3 and provide integrated proofs for
WhyML assertions, postconditions, lemmas, etc. The semantics of these
connectives follows the rules below:

-  A proof task for ``A && B`` is split into separate tasks for ``A``
   and ``A -> B``. If ``A && B`` occurs as a premise, it behaves as a
   normal conjunction.

-  A case analysis over ``A || B`` is split into disjoint cases ``A``
   and ``not A /\ B``. If ``A || B`` occurs as a goal, it behaves as a
   normal disjunction.

-  An occurrence of ``A by B`` generates a side condition ``B -> A``
   (the proof justifies the affirmation). When ``A by B`` occurs as a
   premise, it is reduced to ``A`` (the proof is discarded). When
   ``A by B`` occurs as a goal, it is reduced to ``B`` (the proof is
   verified).

-  An occurrence of ``A so B`` generates a side condition ``A -> B``
   (the premise justifies the conclusion). When ``A so B`` occurs as a
   premise, it is reduced to the conjunction (we use both the premise
   and the conclusion). When ``A so B`` occurs as a goal, it is reduced
   to ``A`` (the premise is verified).

For example, full splitting of the goal
``(A by (exists x. B so C)) && D`` produces four subgoals:
``exists x. B`` (the premise is verified), ``forall x. B -> C`` (the
premise justifies the conclusion), ``(exists x. B /\ C) -> A`` (the
proof justifies the affirmation), and finally, ``A -> D`` (the proof of
``A`` is discarded and ``A`` is used to prove ``D``).

The behavior of the splitting transformations is further controlled by
attributes :why3:attribute:`[@stop_split]` and :why3:attribute:`[@case_split]`.
Consult the documentation
of transformation :why3:transform:`split_goal` in
:numref:`sec.transformations` for details.

Among the propositional connectives, ``not`` has the highest precedence,
``&&`` has the same precedence as ``/\`` (weaker than negation), ``||``
has the same precedence as ``\/`` (weaker than conjunction), ``by``,
``so``, ``->``, and ``<->`` all have the same precedence (weaker than
disjunction). All binary connectives except equivalence are
right-associative. Equivalence is non-associative and is chained
instead: ``A <-> B <-> C`` is transformed into a conjunction of
``A <-> B`` and ``B <-> C``. To reduce ambiguity, WhyML forbids to place
a non-parenthesised implication at the right-hand side of an
equivalence: ``A <-> B -> C`` is rejected.

.. index:: conditionals; syntax
.. index:: let; syntax
.. index:: pattern-matching; syntax

Conditionals, "let" bindings and pattern-matching
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. productionlist::
  term: `term0`
      : | "if" `term` "then" `term` "else" `term`   ; conditional
      : | "match" `term` "with" `term_case`+ "end"   ; pattern matching
      : | "let" `pattern` "=" `term` "in" `term`   ; let-binding
      : | "let" `symbol` `param`+ "=" `term` "in" `term`   ; mapping definition
      : | "fun" `param`+ "->" `term`   ; unnamed mapping
  term_case: "|" `pattern` "->" `term`
  pattern: `binder`   ; variable or "_"
         : | "()"   ; empty tuple
         : | "{" (`lqualid` "=" `pattern` ";")+ "}"   ; record pattern
         : | `uqualid` `pattern`*   ; constructor
         : | "ghost" `pattern`   ; ghost sub-pattern
         : | `pattern` "as" "ghost"? `bound_var`   ; named sub-pattern
         : | `pattern` "," `pattern`   ; tuple pattern
         : | `pattern` "|" `pattern`   ; "or" pattern
         : | `qualifier`? "(" `pattern` ")"   ; pattern in a scope
  symbol: `lident_ext` `attribute`*   ; user-defined symbol
  param: `type_arg`   ; unnamed typed
       : | `binder`   ; (un)named untyped
       : | "(" "ghost"? `type` ")"   ; unnamed typed
       : | "(" "ghost"? `binder` ")"   ; (un)named untyped
       : | "(" "ghost"? `binder`+ ":" `type` ")"   ; multi-variable typed

Above, we find the more advanced term constructions:
conditionals, let-bindings, pattern matching, and local function
definitions, either via the ``let-in`` construction or the ``fun``
keyword. The pure logical functions defined in this way are called
*mappings*; they are first-class values of “arrow” type
``t -> u``.

The patterns are similar to those of OCaml, though the ``when`` clauses
and numerical constants are not supported. Unlike in OCaml, ``as`` binds
stronger than the comma: in the pattern ``(p,q as x)``, variable
``x`` is bound to the value matched by pattern ``q``. Also notice
the closing ``end`` after the ``match with`` term. A ``let in``
construction with a non-trivial pattern is translated as a
``match with`` term with a single branch.

Inside logical terms, pattern matching must be exhaustive: WhyML rejects
a term like ``let Some x = o in e``, where ``o`` is a variable of an
option type. In program expressions, non-exhaustive pattern matching is
accepted and a proof obligation is generated to show that the values not
covered cannot occur in execution.

The syntax of parameters in user-defined operations—first-class
mappings, top-level logical functions and predicates, and program
functions—is rather flexible in WhyML. Like in OCaml, the user can
specify the name of a parameter without its type and let the type be
inferred from the definition. Unlike in OCaml, the user can also specify
the type of the parameter without giving its name. This is convenient
when the symbol declaration does not provide the actual definition or
specification of the symbol, and thus only the type signature is of
relevance. For example, one can declare an abstract binary function that
adds an element to a set simply by writing
``function add 'a (set 'a): set 'a``. A standalone non-qualified
lowercase identifier without attributes is treated as a type name when
the definition is not provided, and as a parameter name otherwise.

Ghost patterns, ghost variables after ``as``, and ghost parameters in
function definitions are only used in program code, and not allowed in
logical terms.

Program expressions
-------------------

The syntax of program expressions is given below. As before, the constructions
are listed in the order of decreasing precedence. The rules for tight,
prefix, infix, and bracket operators are the same as for logical terms.
In particular, the infix operators from group 1 (:token:`infix_op_1`) can be chained. Notice
that binary operators ``&&`` and ``||`` denote here the usual lazy
conjunction and disjunction, respectively.

.. productionlist::
    expr: `integer`   ; integer constant
        : | `real`   ; real constant
        : | "true" | "false"   ; Boolean constant
        : | "()"   ; empty tuple
        : | `string` ; string constant
        : | `qualid`   ; identifier in a scope
        : | `qualifier`? "(" `expr` ")"   ; expression in a scope
        : | `qualifier`? "begin" `expr` "end"   ; idem
        : | `tight_op` `expr`   ; tight operator
        : | "{" (`lqualid` "=" `expr` ";")+ "}"   ; record
        : | "{" `expr` "with" (`lqualid` "=" `expr` ";")+ "}"   ; record update
        : | `expr` "." `lqualid`   ; record field access
        : | `expr` "[" `expr` "]" "'"*   ; collection access
        : | `expr` "[" `expr` "<-" `expr` "]" "'"*   ; collection update
        : | `expr` "[" `expr` ".." `expr` "]" "'"*   ; collection slice
        : | `expr` "[" `expr` ".." "]" "'"*   ; right-open slice
        : | `expr` "[" ".." `expr` "]" "'"*   ; left-open slice
        : | "[|" (`expr` "=>" `expr` ";")* ("_" "=>" `expr`)? "|]" ; function literal
        : | "[|" (`expr` ";")+ "|]" ; function literal (domain over nat)
        : | `expr` `expr`+   ; application
        : | `prefix_op` `expr`   ; prefix operator
        : | `expr` `infix_op_4` `expr`   ; infix operator 4
        : | `expr` `infix_op_3` `expr`   ; infix operator 3
        : | `expr` `infix_op_2` `expr`   ; infix operator 2
        : | `expr` `infix_op_1` `expr`   ; infix operator 1
        : | "not" `expr`   ; negation
        : | `expr` "&&" `expr`   ; lazy conjunction
        : | `expr` "||" `expr`   ; lazy disjunction
        : | `expr` ":" `type`   ; type cast
        : | `attribute`+ `expr`   ; attributes
        : | "ghost" `expr`   ; ghost expression
        : | `expr` ("," `expr`)+   ; tuple
        : | `expr` "<-" `expr`   ; assignment
        : | `expr` `spec`+   ; added specification
        : | "if" `expr` "then" `expr` ("else" `expr`)?   ; conditional
        : | "match" `expr` "with" ("|" `pattern` "->" `expr`)+ "end"   ; pattern matching
        : | `qualifier`? "begin" `spec`+ `expr` "end"   ; abstract block
        : | `expr` ";" `expr`   ; sequence
        : | "let" `pattern` "=" `expr` "in" `expr`   ; let-binding
        : | "let" `fun_defn` "in" `expr`   ; local function
        : | "let" "rec" `fun_defn` ("with" `fun_defn`)* "in" `expr`   ; recursive function
        : | "fun" `param`+ `spec`* "->" `spec`* `expr`   ; unnamed function
        : | "any" `result` `spec`*   ; arbitrary value
        : | "while" `expr` "do" `invariant`* `variant`? `expr` "done"   ; while loop
        : | "for" `lident` "=" `expr` ("to" | "downto") `expr` "do" `invariant`* `expr` "done"   ; for loop
        : | "for" `pattern` "in" `expr` "with" `uident` ("as" `lident_nq`)? "do"  `invariant`* `variant`? `expr` "done" ; for each loop
        : | "break" `lident`?   ; loop break
        : | "continue" `lident`?   ; loop continue
        : | ("assert" | "assume" | "check") "{" `term` "}"   ; assertion
        : | "raise" `uqualid` `expr`?   ; exception raising
        : | "raise" "(" `uqualid` `expr`? ")"
        : | "try" `expr` "with" ("|" `handler`)+ "end"   ; exception catching
        : | "(" `expr` ")"   ; parentheses
        : | "label" `uident` "in" `expr`   ; label
    handler: `uqualid` `pattern`? "->" `expr`   ; exception handler
    fun_defn: `fun_head` `spec`* "=" `spec`* `expr`   ; function definition
    fun_head: "ghost"? `kind`? `symbol` `param`+ (":" `result`)?   ; function header
    kind: "function" | "predicate" | "lemma"   ; function kind
    result: `ret_type`
      : | "(" `ret_type` ("," `ret_type`)* ")"
      : | "(" `ret_name` ("," `ret_name`)* ")"
    ret_type: "ghost"? `type`   ; unnamed result
    ret_name: "ghost"? `binder` ":" `type`   ; named result
    spec: "requires" "{" `term` "}"   ; pre-condition
      : | "ensures" "{" `term` "}"   ; post-condition
      : | "returns" "{" ("|" `pattern` "->" `term`)+ "}"   ; post-condition
      : | "raises" "{" ("|" `pattern` "->" `term`)+ "}"   ; exceptional post-c.
      : | "raises" "{" `uqualid` ("," `uqualid`)* "}"   ; raised exceptions
      : | "reads" "{" `lqualid` ("," `lqualid`)* "}"   ; external reads
      : | "writes" "{" `path` ("," `path`)* "}"   ; memory writes
      : | "alias" "{" `alias` ("," `alias`)* "}"   ; memory aliases
      : | `variant`
      : | "diverges"   ; may not terminate
      : | ("reads" | "writes" | "alias") "{" "}"   ; empty effect
    path: `lqualid` ("." `lqualid`)*   ; v.field1.field2
    alias: `path` "with" `path`   ; arg1 with result
    invariant: "invariant" "{" `term` "}"   ; loop and type invariant
    variant: "variant" "{" `variant_term` ("," `variant_term`)* "}"   ; termination variant
    variant_term: `term` ("with" `lqualid`)?   ; variant term + WF-order

.. index:: ghost expressions

Ghost expressions
^^^^^^^^^^^^^^^^^

Keyword ``ghost`` marks the expression as ghost code added for
verification purposes. Ghost code is removed from the final code
intended for execution, and thus cannot affect the computation of the
program results nor the content of the observable memory.

.. index:: assignment expressions

Assignment expressions
^^^^^^^^^^^^^^^^^^^^^^

Assignment updates in place a mutable record field or an element of a
collection. The former can be done simultaneously on a tuple of values:
``x.f, y.g <- a, b``. The latter form, ``a[i] <- v``, amounts to a call
of the ternary bracket operator ``([]<-)`` and cannot be used in a
multiple assignment.

.. index:: auto-dereference
.. index:: reference

Auto-dereference: simplified usage of mutable variables
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Some syntactic sugar is provided to ease the use of mutable variables
(aka references), in such a way that the bang character is no more
needed to access the value of a reference, in both logic and programs.
This syntactic sugar summarized in the following table.

+-------------------------+-------------------------------+
| auto-dereference syntax | desugared to                  |
+=========================+===============================+
| ``let &x = ... in``     | ``let (x: ref ...) = ... in`` |
+-------------------------+-------------------------------+
| ``f x``                 | ``f x.contents``              |
+-------------------------+-------------------------------+
| ``x <- ...``            | ``x.contents <- ...``         |
+-------------------------+-------------------------------+
| ``let ref x = ...``     | ``let &x = ref ...``          |
+-------------------------+-------------------------------+

Notice that

- the ``&`` marker adds the typing constraint ``(x: ref ...)``;
- top-level ``let/val ref`` and ``let/val &`` are allowed;
- auto-dereferencing works in logic, but such variables
  cannot be introduced inside logical terms.

Here is an example:

.. code-block:: whyml

    let ref x = 0 in while x < 100 do invariant { 0 <= x <= 100 } x <- x + 1 done

That syntactic sugar is further extended to pattern matching, function
parameters, and reference passing, as follows.

+----------------------------------+-----------------------------------------------------+
| auto-dereference syntax          | desugared to                                        |
+==================================+=====================================================+
| ``match e with (x,&y) -> y end`` | ``match e with (x,(y: ref ...)) -> y.contents end`` |
+----------------------------------+-----------------------------------------------------+
| .. code-block:: whyml            | .. code-block:: whyml                               |
|                                  |                                                     |
|    let incr (&x: ref int) =      |    let incr (x: ref int) =                          |
|      x <- x + 1                  |      x.contents <- x.contents + 1                   |
|                                  |                                                     |
|    let f () =                    |    let f () =                                       |
|      let ref x = 0 in            |      let x = ref 0 in                               |
|      incr x;                     |      incr x;                                        |
|      x                           |      x.contents                                     |
+----------------------------------+-----------------------------------------------------+
| ``let incr (ref x: int) ...``    | ``let incr (&x: ref int) ...``                      |
+----------------------------------+-----------------------------------------------------+

The type annotation is not required. Let-functions with such formal
parameters also prevent the actual argument from auto-dereferencing when
used in logic. Pure logical symbols cannot be declared with such
parameters.

Auto-dereference suppression does not work in the middle of a relation
chain: in ``0 < x :< 17``, ``x`` will be dereferenced even if ``(:<)``
expects a ref-parameter on the left.

Finally, that syntactic sugar applies to the caller side:

+-------------------------+-----------------------+
| auto-dereference syntax | desugared to          |
+=========================+=======================+
| .. code-block:: whyml   | .. code-block:: whyml |
|                         |                       |
|    let f () =           |    let f () =         |
|      let ref x = 0 in   |      let x = ref 0 in |
|      g &x               |      g x              |
+-------------------------+-----------------------+

The ``&`` marker can only be attached to a variable. Works in logic.

Ref-binders and ``&``-binders in variable declarations, patterns, and
function parameters do not require importing ``ref.Ref``. Any example
that does not use references inside data structures can be rewritten by
using ref-binders, without importing ``ref.Ref``.

Explicit use of type symbol ``ref``, program function ``ref``, or field
``contents`` requires importing ``ref.Ref`` or ``why3.Ref.Ref``.
Operations ``(:=)`` and ``(!)`` require importing ``ref.Ref``.
Note that operation ``(:=)`` is fully subsumed by direct assignment ``(<-)``.

.. index:: evaluation order

Evaluation order
^^^^^^^^^^^^^^^^

In applications, arguments are evaluated from right to left. This
includes applications of infix operators, with the only exception of
lazy operators ``&&`` and ``||`` which evaluate from left to right,
lazily.

.. index:: past program states
.. index:: at
.. index:: old
.. index:: label

Referring to past program states using "at" and "old" operators
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Within specifications, terms are extended with
constructs ``old`` and ``at``.  Within a postcondition, ``old t`` refers to
the value of term ``t`` in the pre-state. Within the scope of a code label
``L``, introduced with ``label L in ...``, the term ``t at L`` refers to the
value of term ``t`` at the program point corresponding to ``L``.

Note that ``old`` can be used in annotations contained in the function
body as well (assertions, loop invariants), with the exact same meaning: it
refers to the pre-state of the function. In particular, ``old t`` in
a loop invariant does not refer to the program point right before the
loop but to the function entry.

Whenever ``old t`` or ``t at L`` refers to a program point at which
none of the variables in ``t`` is defined, Why3 emits a warning ``this
`at'/`old' operator is never used`` and the operator ``old``/``at`` is
ignored. For instance, the following code

.. code-block:: whyml

    let x = ref 0 in assert { old !x = !x }

emits a warning and is provable, as it amounts to proving `0=0`.
Similarly, if ``old t`` or ``t at L`` refers to a term ``t`` that is
immutable, Why3 emits the same warning and ignores the operator.

Caveat: Whenever the term ``t`` contains several variables, some of
them being meaningful at the corresponding program point but others
not being in scope or being immutable, there is *no warning* and the
operator ``old``/``at`` is applied where it is defined and ignored
elsewhere. This is convenient when writing terms such as ``old a[i]``
where ``a`` makes sense in the pre-state but ``i`` does not.

.. index:: for loop, invariant; for loop

The “for” loop
^^^^^^^^^^^^^^

The “for” loop of Why3 has the following general form:

.. code-block:: whyml

    for v=e1 to e2 do invariant { i } e3 done

Here, ``v`` is a variable identifier, that is bound by the loop
statement and of type ``int`` ; ``e1`` and ``e2`` are program
expressions of type ``int``, and ``e3`` is an expression of type
``unit``. The variable ``v`` may occur both in ``i`` and ``e3``, and
is not mutable. The execution of such a loop amounts to first evaluate
``e1`` and ``e2`` to values ``n1`` and ``n2``. If ``n1 >= n2`` then
the loop is not executed at all, otherwise it is executed iteratively
for ``v`` taking all the values between ``n1`` and ``n2`` included.

Regarding verification conditions, one must prove that ``i[v <- n1]``
holds (invariant initialization) ; and that ``forall n. n1 <= n <= n2
/\ i[v <- n] -> i[v <- n+1]`` (invariant preservation). At loop exit,
the property which is known is ``i[v <- n2+1]`` (notice the index
``n2+1``). A special case occurs when the initial value ``n1`` is
larger than ``n2+1``: in that case the VC generator does not produce
any VC to prove, the loop just acts as a no-op instruction. Yet in the
case when ``n1 = n2+1``, the formula ``i[v <- n2+1]`` is asserted and
thus need to be proved as a VC.

The variant with keyword ``downto`` instead of ``to`` iterates
backwards.

It is also possible for ``v`` to be an integer range type (see
:numref:`sec.range_types`) instead of an integer.

.. index:: for each loop, invariant; for each loop

The “for each” loop
^^^^^^^^^^^^^^^^^^^

The “for each” loop of Why3 has the following syntax:

.. code-block:: whyml

    for p in e1 with S do invariant/variant... e2 done

Here, ``p`` is a pattern, ``S`` is a namespace, and ``e1`` and ``e2``
are program expressions. Such a for each loop is syntactic sugar for
the following:

.. code-block:: whyml

    let it = S.create e1 in
    try
      while true do
        invariant/variant...
        let p = S.next it in
        e2
      done
    with S.Done -> ()

That is, namespace ``S`` is assumed to declare at least a function
``create`` and a function ``next``, and an exception ``Done``. The
latter is used to signal the end of the iteration.
As shown above, the iterator is named ``it``. It can be referred to
within annotations. A different name can be specified, using syntax
``with S as x do``.

.. index:: while loop, for loop, break, continue

Break & Continue
^^^^^^^^^^^^^^^^


The ``break`` and ``continue`` statements can be used in ``while``,
``for`` and ``for-each`` loops, with the expected semantics. The
statements take an optional identifier which can be used to break
out of nested loops. This identifier can be defined using ``label``
like in the following example:

.. code-block:: whyml

    label A in
    while true do
      variant...
      while true do
        variant..
        break A (* abort the outer loop *)
      done
    done

.. index:: collections; syntax; function literals

Function literals
^^^^^^^^^^^^^^^^^

Function literals can be written in expressions the same way as they
are in terms but there are a few subtleties that one must bear in
mind. First of all, if the domain of the literal is of type ``t`` then
an equality infix operator ``=`` should exist. For instance, the
literal ``[|t1 => u1|]`` with ``t1`` of type ``t``, is only considered
well typed if the infix operator ``=`` of type ``t -> t -> bool`` is
visible in the current scope. This problem does not exist in terms
because the equality in terms is polymorphic.

Second, the function literal expression ``[|t1 => u1; t2 => u2; _ =>
u3|]`` will be translated into the following expression:

.. code-block:: whyml

    let def'e = u3 in
    let d'i1 = t2 in
    let r'i1 = u2 in
    let d'i0 = t1 in
    let r'i0 = u1 in
    fun x'x -> if x'x = d'i0 then r'i0 else
               if x'x = d'i1 then r'i1 else
               def'e

.. index:: any expression

The ``any`` expression
^^^^^^^^^^^^^^^^^^^^^^

The general form of the ``any`` expression is the following.

.. code-block:: whyml

  any <type> <contract>

This expression non-deterministically evaluates to a value of the
given type that satisfies the contract. For example, the code

.. code-block:: whyml

  let x = any int ensures { 0 <= result < 100 } in
  ...

will give to ``x`` any non-negative integer value smaller than 100.

As for contracts on functions, it is allowed to name the result or
even give a pattern for it. For example the following expression
returns a pair of integers which first component is smaller than the
second.

.. code-block:: whyml

  any (int,int) returns { (a,b) -> a <= b }

Notice that an ``any`` expression is not supposed to have side effects
nor raise exceptions, hence its contract cannot include any
``writes`` or ``raises`` clauses.

To ensure that this construction is safe, it is mandatory to show that
there is always at least one possible value to return. It means that
the VC generator produces a proof obligation of form

.. code-block:: whyml

   exists result:<type>. <post-condition>

In that respect, notice the difference with the construct

.. code-block:: whyml

  val x:<type> <contract> in x

which will not generate any proof obligation, meaning that the
existence of the value ``x`` is taken for granted.



Modules
-------

A WhyML input file is a (possibly empty) list of modules

.. productionlist::
    file: `module`*
    module: "module" `uident_nq` `attribute`* `decl`* "end"
    decl: "type" `type_decl` ("with" `type_decl`)*
      : | "constant" `constant_decl`
      : | "function" `function_decl` ("with" `logic_decl`)*
      : | "predicate" `predicate_decl` ("with" `logic_decl`)*
      : | "inductive" `inductive_decl` ("with" `inductive_decl`)*
      : | "coinductive" `inductive_decl` ("with" `inductive_decl`)*
      : | "axiom" `ident_nq` ":" `formula`
      : | "lemma" `ident_nq` ":" `formula`
      : | "goal"  `ident_nq` ":" `formula`
      : | "use" `imp_exp` `tqualid` ("as" `uident`)?
      : | "clone" `imp_exp` `tqualid` ("as" `uident`)? `subst`?
      : | "scope" "import"? `uident_nq` `decl`* "end"
      : | "import" `uident`
      : | "let" "ghost"? `lident_nq` `attribute`* `fun_defn`
      : | "let" "rec" `fun_defn`
      : | "val" "ghost"? `lident_nq` `attribute`* `pgm_decl`
      : | "exception" `lident_nq` `attribute`* `type`?
    type_decl: `lident_nq` `attribute`* ("'" `lident_nq` `attribute`*)* `type_defn`
    type_defn:   ; abstract type
      : | "=" `type`   ; alias type
      : | "=" "|"? `type_case` ("|" `type_case`)*   ; algebraic type
      : | "=" `vis_mut` "{" `record_field` (";" `record_field`)* "}" `invariant`* `type_witness`  ; record type
      : | "<" "range" `integer` `integer` ">"   ; range type
      : | "<" "float" `integer` `integer` ">"   ; float type
    type_case: `uident` `attribute`* `type_param`*
    record_field: "ghost"? "mutable"? `lident_nq` `attribute`* ":" `type`
    type_witness: "by" "{" `lident_nq` "=" `expr` (";" `lident_nq` "=" `expr`)* "}"
    vis_mut: ("abstract" | "private")? "mutable"?
    pgm_decl: ":" `type`   ; global variable
      : | `param` (`spec`* `param`)+ ":" `type` `spec`*   ; abstract function
    logic_decl: `function_decl`
      : | `predicate_decl`
    constant_decl: `lident_nq` `attribute`* ":" `type`
      : | `lident_nq` `attribute`* ":" `type` "=" `term`
    function_decl: `lident_nq` `attribute`* `type_param`* ":" `type`
      : | `lident_nq` `attribute`* `type_param`* ":" `type` "=" `term`
    predicate_decl: `lident_nq` `attribute`* `type_param`*
      : | `lident_nq` `attribute`* `type_param`* "=" `formula`
    inductive_decl: `lident_nq` `attribute`* `type_param`* "=" "|"? `ind_case` ("|" `ind_case`)*
    ind_case: `ident_nq` `attribute`* ":" `formula`
    imp_exp: ("import" | "export")?
    subst: "with" ("," `subst_elt`)+
    subst_elt: "type" `lqualid` "=" `lqualid`
      : | "function" `lqualid` "=" `lqualid`
      : | "predicate" `lqualid` "=" `lqualid`
      : | "scope" (`uqualid` | ".") "=" (`uqualid` | ".")
      : | "lemma" `qualid`
      : | "goal"  `qualid`
    tqualid: `uident` | `ident` ("." `ident`)* "." `uident`
    type_param: "'" `lident`
     : | `lqualid`
     : | "(" `lident`+ ":" `type` ")"
     : | "(" `type` ("," `type`)* ")"
     : | "()"


.. index:: record type
.. _Record Types:

Record types
^^^^^^^^^^^^

A record type declaration introduces a new type, with named and typed
fields, as follows:

.. code-block:: whyml

    type t = { a: int; b: bool }

Such a type can be used both in logic and programs.
A new record is built using curly braces and a value for each field,
such as ``{ a = 42; b = true }``. If ``x`` is a value of type ``t``,
its fields are accessed using the dot notation, such as ``x.a``.
Each field happens to be a projection function, so that we can also
write ``a x``.
A field can be declared ``mutable``, as follows:

.. code-block:: whyml

    type t = { mutable a: int; b: bool }

A mutable field can be modified using notation ``x.a <- 42``.
The ``writes`` clause of a function contract can list mutable fields,
e.g., ``writes { x.a }``.

.. index:: type invariant, invariant; type
.. rubric:: Type invariants

Invariants can be attached to record types, as follows:

.. code-block:: whyml

    type t = { mutable a: int; b: bool }
      invariant { b = true -> a >= 0 }

The semantics of type invariants is as follows. In the logic, a type
invariant always holds.
Consequently, it is no more possible
to build a value using the curly braces (in the logic).
To prevent the introduction of a logical
inconsistency, Why3 generates a VC to show the existence of at least
one record instance satisfying the invariant. It is named ``t'vc``
and has the form ``exists a:int, b:bool. b = true -> a >= 0``. To ease the
verification of this VC, one can provide an explicit witness using the
keyword ``by``, as follows:

.. code-block:: whyml

    type t = { mutable a: int; b: bool }
      invariant { b = true -> a >= 0 }
      by { a = 42; b = true }

It generates a simpler VC, where fields are instantiated accordingly.

In programs, a type invariant is assumed to
hold at function entry and must be restored at function exit.
In the middle, the invariant can be temporarily broken. For instance,
the following function can be verified:

.. code-block:: whyml

    let f (x: t) = x.a <- x.a - 1; x.a <- 0

After the first assignment, the invariant does not necessarily hold
anymore. But it is restored before function exit with the second
assignment.

If the record is passed to another function, then the invariant
must be reestablished (so as to honor the contract of the callee).
For instance, the following function cannot be verified:

.. code-block:: whyml

    let f1 (x: t) = x.a <- x.a - 1; f x; x.a <- 0

Indeed, passing ``x`` to function ``f`` requires checking the
invariant first, which does not hold in this example. Similarly, the
invariant must be reestablished if the record is passed to a logical
function or predicate. For instance, the following function cannot be
verified:

.. code-block:: whyml

    predicate p (x: t) = x.b

    let f2 (x: t) = x.a <- x.a - 1; assert { p x }; x.a <- 0

Accessing the record fields, however, does not require restoring the
invariant, both in logic and programs.
For instance, the following function can be verified:

.. code-block:: whyml

    let f2 (x: t) = x.a <- x.a - 1; assert { x.a < old x.a }; x.a <- 0

Indeed, the invariant may not hold after the first assignment, but the
assertion is only making use of field access, so there is no need to
reestablish the invariant.

.. index:: private type
.. rubric:: Private types

A record type can be declared ``private``, as follows:

.. code-block:: whyml

    type t = private { mutable a: int; b: bool }

The meaning of such a declaration is that one cannot build a record
instance, neither in the logic, nor in programs.
For instance, the following function cannot be defined:

.. code-block:: whyml

    let create () = { a = 42; b = true }

One cannot modify mutable fields of private types either.
One may wonder what is the purpose of private types, if one cannot
build values in those types. The purpose is to build
interfaces, to be later refined with actual implementations (see
section :ref:`Module cloning` below). Indeed, if we cannot build
record instances, we can still *declare* operations that
return such records. For instance, we can declare the following two
functions:

.. code-block:: whyml

    val create (n: int) : t
      ensures { result.a = n }

    val incr (x: t) : unit
      writes  { x.a }
      ensures { x.a = old x.a + 1 }

Later, we can *refine* type ``t`` with a type that is not private
anymore, and then implement operations ``create`` and ``incr``.

Private types are often used in conjunction with ghost fields, that
are used to model the contents of data structures. For instance, we
can conveniently model a queue containing integers as follows:

.. code-block:: whyml

    type queue = private { mutable ghost s: seq int }

If needed, we could even add invariants (e.g., the sequence ``s`` is
sorted in a priority queue).

.. index:: abstract type

When a private record type only has ghost fields, one can use
``abstract`` as a convenient shortcut:

.. code-block:: whyml

    type queue = abstract { mutable s: seq int }

This is equivalent to the previous declaration.

.. rubric:: Recursive record types

Record types can be recursive, e.g,

.. code-block:: whyml

    type t = { a: int; next: option t }

Recursive record types cannot have invariants, cannot have mutable
fields, and cannot be private.

.. index:: algebraic data type

Algebraic data types
^^^^^^^^^^^^^^^^^^^^

Algebraic data types combine sum and product types.
A simple example of a sum type is that of an option type:

.. code-block:: whyml

    type maybe = No | Yes int

Such a declaration introduces a new type ``maybe``, with two
constructors ``No`` and ``Yes``. Constructor ``No`` has no argument
and thus can be used as a constant value. Constructor ``Yes`` has an
argument of type ``int`` and thus can be used to build values such as
``Yes 42``. Algebraic data types can be polymorphic, e.g.,

.. code-block:: whyml

    type option 'a = None | Some 'a

(This type is already part of Why3 standard library, in module
`option.Option <http://why3.lri.fr/stdlib/option.html>`_.)

A data type can be recursive. The archetypal example is the type of
polymorphic lists:

.. code-block:: whyml

    type list 'a = Nil | Cons 'a (list 'a)

(This type is already part of Why3 standard library, in module
`list.List <http://why3.lri.fr/stdlib/list.html>`_.)

When a field is common to all constructors, with the same type, it can
be named:

.. code-block:: whyml

    type t =
      | MayBe (size: int) (option int)
      | Many  (size: int) (list int)

Such a named field introduces a projection function. Here, we get a
function ``size`` of type ``t -> int``.

Constructor arguments can be ghost, e.g.,

.. code-block:: whyml

    type answer =
      | Yes (ghost int)
      | No

Non-uniform data types are allowed, such as the following type for
`random access lists <http://toccata.lri.fr/gallery/random_access_list.fr.html>`_:

.. code-block:: whyml

    type ral 'a =
      | Empty
      | Zero    (ral ('a, 'a))
      | One  'a (ral ('a, 'a))

Why3 supports polymorphic recursion, both in logic and programs, so
that we can define and verify operations on such types.

.. index:: tuples
.. rubric:: Tuples

A tuple type is a particular case of algebraic data types, with a
single constructor. A tuple type need not be declared by the user; it
is generated on the fly. The syntax for a tuple type is ``(type1,
type2, ...)``.

Note: Record types, introduced in the previous section, also
constitute a particular case of algebraic data types with a single
constructor. There are differences, though. Record types may have
mutable fields, invariants, or private status, while algebraic data
types cannot.


.. index:: range type
.. _sec.range_types:

Range types
^^^^^^^^^^^

A declaration of the form ``type r = <range a b>`` defines a type that
projects into the integer range ``[a,b]``. Note that in order to make
such a declaration the theory ``int.Int`` must be imported.

Why3 let you cast an integer literal in a range type (e.g., ``(42:r)``)
and will check at typing that the literal is in range. Defining such a
range type :math:`r` automatically introduces the following:

.. code-block:: whyml

    function r'int r : int
    constant r'maxInt : int
    constant r'minInt : int

The function ``r'int`` projects a term of type ``r`` to its integer
value. The two constants represent the high bound and low bound of the
range respectively.

Unless specified otherwise with the meta :why3:meta:`keep:literal` on ``r``, the
transformation :why3:transform:`eliminate_literal` introduces an axiom

.. code-block:: whyml

    axiom r'axiom : forall i:r. r'minInt <= r'int i <= r'maxInt

and replaces all casts of the form ``(42:r)`` with a constant and an
axiom as in:

.. code-block:: whyml

    constant rliteral7 : r
    axiom rliteral7_axiom : r'int rliteral7 = 42

This type is used in the standard library in the theories ``bv.BV8``,
``bv.BV16``, ``bv.BV32``, ``bv.BV64``.

Floating-point types
^^^^^^^^^^^^^^^^^^^^

A declaration of the form ``type f = <float eb sb>`` defines a type of
floating-point numbers as specified by the IEEE-754
standard :cite:`ieee754-2008`. Here the literal ``eb``
represents the number of bits in the exponent and the literal ``sb`` the
number of bits in the significand (including the hidden bit). Note that
in order to make such a declaration the theory ``real.Real`` must be
imported.

Why3 let you cast a real literal in a float type (e.g., ``(0.5:f)``) and
will check at typing that the literal is representable in the format.
Note that Why3 do not implicitly round a real literal when casting to a
float type, it refuses the cast if the literal is not representable.

Defining such a type ``f`` automatically introduces the following:

.. code-block:: whyml

    predicate f'isFinite f
    function  f'real f : real
    constant  f'eb : int
    constant  f'sb : int

As specified by the IEEE standard, float formats includes infinite
values and also a special NaN value (Not-a-Number) to represent results
of undefined operations such as :math:`0/0`. The predicate
``f'isFinite`` indicates whether its argument is neither infinite nor
NaN. The function ``f'real`` projects a finite term of type ``f`` to its
real value, its result is not specified for non finite terms.

Unless specified otherwise with the meta :why3:meta:`keep:literal` on ``f``, the
transformation :why3:transform:`eliminate_literal` will introduce an axiom

.. code-block:: whyml

    axiom f'axiom :
      forall x:f. f'isFinite x -> -. max_real <=. f'real x <=. max_real

where ``max_real`` is the value of the biggest finite float in the
specified format. The transformation also replaces all casts of the form
``(0.5:f)`` with a constant and an axiom as in:

.. code-block:: whyml

    constant fliteral42 : f
    axiom fliteral42_axiom : f'real fliteral42 = 0.5 /\ f'isFinite fliteral42

This type is used in the standard library in the theories
``ieee_float.Float32`` and ``ieee_float.Float64``.





Function declarations
^^^^^^^^^^^^^^^^^^^^^

``let``
   Definition of a program function, with prototype, contract, and body

``val``
   Declaration of a program function, with prototype and contract only

``let function``
   Definition of a pure (that is, side-effect free) program function
   which can also be used in specifications as a logical function
   symbol

``let predicate``
   Definition of a pure Boolean program function which can also be
   used in specifications as a logical predicate symbol

``val function``
   Declaration of a pure program function which can also be used in
   specifications as a logical function symbol

``val predicate``
   Declaration of a pure Boolean program function which can also be
   used in specifications as a logical predicate symbol

``function``
   Definition or declaration of a logical function symbol which can
   also be used as a program function in ghost code

``predicate``
   Definition or declaration of a logical predicate symbol which can
   also be used as a Boolean program function in ghost code

``let lemma``
   definition of a special pure program function which serves not as
   an actual code to execute but to prove the function's contract as a
   lemma: “for all values of parameters, the precondition implies the
   postcondition”. This lemma is then added to the logical context and
   is made available to provers. If this “lemma-function” produces a
   result, the lemma is “for all values of parameters, the
   precondition implies the existence of a result that satisfies the
   postcondition”. Lemma-functions are mostly used to prove some
   property by induction directly in Why3, without resorting to an
   external higher-order proof assistant.

Program functions (defined with ``let`` or declared with ``val``) can
additionally be marked ``ghost``, meaning that they can only be used
in the ghost code and never translated into executable code ; or
``partial``, meaning that their execution can produce observable
effects unaccounted by their specification, and thus they cannot be
used in the ghost code.

.. index:: clone
.. index:: module cloning
.. _Module cloning:

Module cloning
^^^^^^^^^^^^^^

Why3 features a mechanism to make an instance of a module, by
substituting some of its declarations with other symbols. It is called
*module cloning*.

Let us consider the example of a module implementing
`exponentiation by squaring
<https://en.wikipedia.org/wiki/Exponentiation_by_squaring>`_.
We want to make it as general as possible, so that we can implement it
and verify it only once and then reuse it in various different
contexts, e.g., with integers, floating-point numbers, matrices, etc.
We start our module with the introduction of a monoid:

.. code-block:: whyml

   module Exp
     use int.Int
     use int.ComputerDivision

     type t

     val constant one : t

     val function mul t t : t

     axiom one_neutral: forall x. mul one x = x = mul x one

     axiom mul_assoc: forall x y z. mul x (mul y z) = mul (mul x y) z

Then we define a simple exponentiation function, mostly for the
purpose of specification:

.. code-block:: whyml
   :dedent: 0

     let rec function exp (x: t) (n: int) : t
       requires { n >= 0 }
       variant  { n }
     = if n = 0 then one else mul x (exp x (n - 1))

In anticipation of the forthcoming verification of exponentiation by
squaring, we prove two lemmas. As they require induction, we use lemma
functions:

.. code-block:: whyml
   :dedent: 0

     let rec lemma exp_add (x: t) (n m: int)
       requires { 0 <= n /\ 0 <= m }
       variant  { n }
       ensures  { exp x (n + m) = mul (exp x n) (exp x m) }
     = if n > 0 then exp_add x (n - 1) m

     let rec lemma exp_mul (x: t) (n m: int)
       requires { 0 <= n /\ 0 <= m }
       variant  { m }
       ensures  { exp x (n * m) = exp (exp x n) m }
     = if m > 0 then exp_mul x n (m - 1)

Finally, we implement and verify exponentiation by squaring, which
completes our module.

.. code-block:: whyml
   :dedent: 0

     let fast_exp (x: t) (n: int) : t
       requires { n >= 0 }
       ensures  { result = exp x n }
     = let ref p = x in
       let ref q = n in
       let ref r = one in
       while q > 0 do
         invariant { 0 <= q }
         invariant { mul r (exp p q) = exp x n }
         variant   { q }
         if mod q 2 = 1 then r <- mul r p;
         p <- mul p p;
         q <- div q 2
       done;
       r

   end

Note that module ``Exp`` mixes declared symbols (type ``t``, constant
``one``, function ``mul``) and defined symbols (function ``exp``,
program function ``fast_exp``).

We can now make an instance of module ``Exp``, by substituting some of
its declared symbols (not necessarily all of them) with some other
symbols. For instance, we get exponentiation by squaring on integers
by substituting ``int`` for type ``t``, integer ``1`` for constant
``one``, and integer multiplication for function ``mul``.

.. code-block:: whyml

    module ExponentiationBySquaring
      use int.Int
      clone Exp with type t = int, val one = one, val mul = (*)
    end

In a substitution such as ``val one = one``,
the left-hand side refers to the namespace of
the module being cloned, while the right-hand side refers to the
current namespace (which here contains a constant ``one`` of type
``int``).

When a module is cloned, any axiom is automatically turned into a
lemma. Thus, the ``clone`` command above generates two VCs, one for
lemma ``one_neutral`` and another for lemma ``mul_assoc``.  If an
axiom should instead remain an axiom, it should be explicitly
indicated in the substitution (using ``axiom mul_assoc`` for
instance). Why3 cannot figure out by itself whether an axiom should be
turned into a lemma, so it goes for the safe path (all axioms are to
be proved) by default.

Lemmas that were proved in the module being cloned (such as
``exp_add`` and ``exp_mul`` here) are not reproved. They are part
of the resulting namespace, the substitution being applied to
their statements.
Similarly, functions that were defined in the module being cloned
(such as ``exp`` and ``fast_exp`` here) are not reproved and are part
of the resulting module, the substitution being applied to their
argument types, return type, and definition. For instance, we get a
fresh function ``fast_exp`` of type ``int->int->int``.

We can make plenty other instances of our module ``Exp``.
For instance, we get
`Russian multiplication
<https://en.wikipedia.org/wiki/Ancient_Egyptian_multiplication>`_ for free
by instantiating ``Exp`` with zero and addition instead.

.. code-block:: whyml

    module Multiplication
      use int.Int
      clone Exp with type t = int, val one = zero, val mul = (+)
      goal G: exp 2 3 = 6
    end

.. index:: standard library

The Why3 Standard Library
-------------------------

The Why3 standard library provides general-purpose modules, to be used
in logic and/or programs. It can be browsed on-line at
http://why3.lri.fr/stdlib/. Each file contains one or several modules.
To ``use`` or ``clone`` a module ``M`` from file :file:`file.mlw`, use the
syntax ``file.M``, since :file:`file.mlw` is available in Why3’s default load
path. For instance, the module of integers and the module of arrays
indexed by integers are imported as follows:

.. code-block:: whyml

      use int.Int
      use array.Array

A sub-directory :file:`mach/` provides various modules to model machine
arithmetic. For instance, the module of 63-bit integers and the module
of arrays indexed by 63-bit integers are imported as follows:

.. code-block:: whyml

      use mach.int.Int63
      use mach.array.Array63

In particular, the types and operations from these modules are mapped to
native OCaml’s types and operations when Why3 code is extracted to OCaml
(see :numref:`sec.extract`).

Library ``int``: mathematical integers
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The ``int`` library contains several modules whose dependencies are
displayed on Figure :numref:`fig.lib.int`.

.. graphviz:: generated/library-int.dot
   :caption: Module dependencies in library ``int``.
   :name: fig.lib.int

The main module is ``Int`` which provides basic operations like addition
and multiplication, and comparisons.

The division of modulo operations are defined in other modules. They
indeed come into two flavors: the module ``EuclideanDivision`` proposes
a version where the result of the modulo is always non-negative, whereas
the module ``ComputerDivision`` provides a version which matches the
standard definition available in programming languages like C, Java or
OCaml. Note that these modules do not provide any divsion or modulo
operations to be used in programs. For those, you must use the module
``mach.int.Int`` instead, which provides these operations, including
proper pre-conditions, and with the usual infix syntax ``x / y`` and ``x
% y``.

The detailed documentation of the library is available on-line at
http://why3.lri.fr/stdlib/int.html


Library ``array``: array data structure
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The ``array`` library contains several modules whose dependencies are
displayed on Figure :numref:`fig.lib.array`.

.. graphviz:: generated/library-array.dot
   :caption: Module dependencies in library ``array``.
   :name: fig.lib.array

The main module is ``Array``, providing the operations for accessing and
updating an array element, with respective syntax ``a[i]`` and ``a[i] <-
e``, and proper pre-conditions for the indexes. The length of an array is
denoted as ``a.length``. A fresh array can be created using ``make l v``
where ``l`` is the desired length and ``v`` is the initial value of each
cell.

The detailed documentation of the library is available on-line at
http://why3.lri.fr/stdlib/array.html
