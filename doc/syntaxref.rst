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


Built-in types are ``int`` (arbitrary precision integers), ``real``
(real numbers), ``bool``, the arrow type (also called the *mapping
type*), and the tuple types. The empty tuple type is also called the
*unit type* and can be written as ``unit``.

Note that the syntax for type expressions notably differs from the usual
ML syntax. In particular, the type of polymorphic lists is written
``list 'a``, and not ``'a list``.

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

Logical expressions: terms and formulas
---------------------------------------

.. productionlist::
    term: `integer`   ; integer constant
        : | `real`   ; real constant
        : | "true" | "false"   ; Boolean constant
        : | "()"   ; empty tuple
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
        : | ...   ; (to be continued)
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


A significant part of a typical WhyML source file is occupied by
non-executable logical content intended for specification and proof:
function contracts, assertions, definitions of logical functions and
predicates, axioms, lemmas, etc.

Logical expressions are called *terms*. Boolean terms are called
*formulas*. Internally, Why3 distinguishes the proper formulas (produced
by predicate symbols, propositional connectives and quantifiers) and the
terms of type ``bool`` (produced by Boolean variables and logical
functions that return ``bool``). However, this distinction is not
enforced on the syntactical level, and Why3 will perform the necessary
conversions behind the scenes.

The syntax of WhyML terms is given in :token:`term`.  The various
constructs have the following priorities and associativities, from
lowest to greatest priority:

+---------------------------------+-----------------+
| construct                       | associativity   |
+=================================+=================+
| ``if then else`` / ``let in``   | –               |
+---------------------------------+-----------------+
| attribute                       | –               |
+---------------------------------+-----------------+
| cast                            | –               |
+---------------------------------+-----------------+
| ``->`` / ``<->``                | right           |
+---------------------------------+-----------------+
| ``by`` / ``so``                 | right           |
+---------------------------------+-----------------+
| ``\/`` / ``||``                 | right           |
+---------------------------------+-----------------+
| ``/\`` / ``&&``                 | right           |
+---------------------------------+-----------------+
| ``not``                         | –               |
+---------------------------------+-----------------+
| infix-op level 1                | left            |
+---------------------------------+-----------------+
| infix-op level 2                | left            |
+---------------------------------+-----------------+
| infix-op level 3                | left            |
+---------------------------------+-----------------+
| infix-op level 4                | left            |
+---------------------------------+-----------------+
| prefix-op                       | –               |
+---------------------------------+-----------------+
| function application            | left            |
+---------------------------------+-----------------+
| brackets / ternary brackets     | –               |
+---------------------------------+-----------------+
| bang-op                         | –               |
+---------------------------------+-----------------+

For example, as was mentioned above,
tight operators have the highest precedence of all operators, so that
``-p.x`` denotes the negation of the record field ``p.x``, whereas
``!p.x`` denotes the field ``x`` of a record stored in the reference
``p``.

Note that infix symbols of level 1 include equality (``=``) and
disequality (``<>``).

Note the curryfied syntax for function application, though partial
application is not allowed (rejected at typing).

An operator in parentheses acts as an identifier referring to that
operator, for example, in a definition. To distinguish between prefix
and infix operators, an underscore symbol is appended at the end: for
example, ``(-)`` refers to the binary subtraction and ``(-_)`` to the
unary negation. Tight operators cannot be used as infix operators, and
thus do not require disambiguation.

In addition to prefix and infix operators, WhyML supports several mixfix
bracket operators to manipulate various collection types: dictionaries,
arrays, sequences, etc. Bracket operators do not have any predefined
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

.. index:: at
.. index:: old

The ``at`` and ``old`` operators are used inside postconditions and
assertions to refer to the value of a mutable program variable at some
past moment of execution (see the next section for details). These
operators have higher precedence than the infix operators from group 1
(:token:`infix_op_1`): ``old i > j`` is parsed as ``(old i) > j`` and not as
``old (i > j)``.

Infix operators from groups 2-4 are left-associative. Infix operators
from group 1 are non-associative and can be chained. For example, the
term ``0 <= i < j < length a`` is parsed as the conjunction of three
inequalities ``0 <= i``, ``i < j``, and ``j < length a``.

As with normal identifiers, we can put a qualifier over a parenthesised
operator, e.g., ``Map.S.([]) m i``. Also, as noted above, a qualifier
can be put over a parenthesised term, and the parentheses can be omitted
if the term is a record or a record update.

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
attributes ``[@stop_split]`` and ``[@case_split]``. Consult the documentation
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

.. productionlist::
  term: ...
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
`t -> u`.

The patterns are similar to those of OCaml, though the `when` clauses
and numerical constants are not supported. Unlike in OCaml, `as` binds
stronger than the comma: in the pattern `(p,q as x)`, variable
`x` is bound to the value matched by pattern `q`. Also notice
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
.. rubric:: Ghost expressions

Keyword ``ghost`` marks the expression as ghost code added for
verification purposes. Ghost code is removed from the final code
intended for execution, and thus cannot affect the computation of the
program results nor the content of the observable memory.

.. index:: assignment expressions
.. rubric:: Assignment expressions

Assignment updates in place a mutable record field or an element of a
collection. The former can be done simultaneously on a tuple of values:
``x.f, y.g <- a, b``. The latter form, ``a[i] <- v``, amounts to a call
of the ternary bracket operator ``([]<-)`` and cannot be used in a
multiple assignment.

.. index:: evaluation order
.. rubric:: Evaluation order

In applications, arguments are evaluated from right to left. This
includes applications of infix operators, with the only exception of
lazy operators ``&&`` and ``||`` which evaluate from left to right,
lazily.

.. index:: specification clauses
.. rubric:: Specification clauses
.. index:: at
.. index:: old

The syntax for specification clauses in programs is given in
:token:`spec`.  Within specifications, terms are extended with
constructs `old` and `at`.  Within a postcondition, `old t` refers to
the value of term `t` in the prestate. Within the scope of a code mark
`L`, the term `at t L` refers to the value of term `t` at the program
point corresponding to `L`.

.. index:: for each loop
.. rubric:: The “For each” loop

The “for each” loop of Why3 has the following syntax:

::

    for p in e1 with S do invariants/variant... e2 done

Here, ``p`` is a pattern, ``S`` is a namespace, and ``e1`` and ``e2``
are program expressions. Such a for each loop is syntactic sugar for
the following:

::

    let it = S.create e1 in
    try while true do
      invariants/variant...
      let p = S.next it in
      e2
    with S.Done -> ()

That is, namespace ``S`` is assumed to declare at least a function
``create`` and a function ``next``, and an exception ``Done``. The
latter is used to signal the end of the iteration.
As shown above, the iterator is named ``it``. It can be referred to
within annotations. A different name can be specified, using syntax
``with S as x do``.

Constructions ``break`` and ``continue`` can be used in for each
loops, with the expected semantics.

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


Algebraic types
^^^^^^^^^^^^^^^

.. index:: algebraic type

TO BE COMPLETED



Record types
^^^^^^^^^^^^
.. index:: record type

A record type declaration introduces a new type, with named and types
fields, as follows:

::

   type t = { a: int; b: bool; }

Such a type can be used in both logic and programs.
A new record is built using curly braces and a value for each field,
such as ``{ a = 42; b = true }``. If ``x`` is a value of type ``t``,
its fields are accessed using the dot notation, such as ``x.a``.
Each field happens to be a projection function, so that we can also
``a x``.
A field can be declared ``mutable``, as follows:

::

   type t = { mutable a: int; b: bool; }

A mutable field can be mutated using notation ``x.a <- 42``.
The ``writes`` clause of a function contract can list mutable fields,
e.g., ``writes { x.a }``.

.. index:: type invariant
.. rubric:: Type invariants

Invariants can be attached to record types, as follows:

::

   type t = { mutable a: int; b: bool; } invariant { b -> a >= 0 }

The semantics of type invariants is as follows. In the logic, a type
invariant always holds. To prevent the introduction of a logical
inconsistency, Why3 generates a VC to show the existence of at least
one record instance satisfying the invariant. It is named ``t'vc``
and has the form ``exists a:int, b:bool. ...``. To ease the
verification of this VC, one can provide an explicit witness using the
keyword ``by``, as follows:

::

   type t = { mutable a: int; b: bool; } invariant { b -> a >= 0 }
      by { a = 42; b = true }

It generates a simpler VC, where fields are instantiated accordingly.

In programs, a type invariant is assumed to
hold at function entry and must be restored at function exit.
In the middle, the invariant can be temporarily broken. For instance,
the following function can be verified:

::

    let f (x: t) = x.a <- x.a - 1; x.a <- 0

After the first assignment, the invariant does not necessarily hold
anymore. But it is restored before function exit with the second
assignment.

If ever the record is passed to another function, then the invariant
must be reestablished (so as to honor the contract of the callee).
For instance, the following function cannot be verified:

::

    let f1 (x: t) = x.a <- x.a - 1; f x; x.a <- 0

Indeed, passing ``x`` to function ``f`` imposes to check for the
invariant first, which does not hold on this example. Similarly, the
invariant must be reestablished if the record is passed to a logical
function or predicate. For instance, the following function cannot be
verified:

::

    predicate p (x: t) = x.b
    let f2 (x: t) = x.a <- x.a - 1; assert { p x }; x.a <- 0

Accessing the record fields, however, does not imply to restore the
invariant, in both logic and programs.
For instance, the following function can be verified:

::

    let f2 (x: t) = x.a <- x.a - 1; assert { x.a < old x.a }; x.a <- 0

Indeed, the invariant may not hold after the first assignment, but the
assertion is only making use of field access, so there is no need to
reestablished the invariant.

.. index:: private type
.. rubric:: Private types

A record type can be declared ``private``, as follows:

::

    type t = private { mutable a: int; b: bool; }

The meaning of such a declaration is that one cannot build a record
instance anymore, neither in the logic, nor in programs.
For instance, the following function cannot be defined anymore:

::

    let create () = { a = 42; b = true }

One cannot modify mutable fields of private types either.
One may wonder what is the purpose of private types, if one cannot
build values in those types anymore. The purpose is to build
interfaces, to be later refined with actual implementations (see
section :ref:`Module Cloning` below). Indeed, if we cannot build
record instances anymore, we can still *declare* operations that
return such records. For instance, we can declare the following two
functions:

::

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

::

    type queue = private { mutable ghost s: seq int }

If needed, we could even add invariants (e.g., the sequence ``s`` is
sorted for a priority queue).

.. index:: abstract type

When a private record type only has ghost fields, one can use
``abstract`` as a convenient shortcut:

::

    type queue = abstract { mutable s: seq int }

This is equivalent to the previous declaration.

.. rubric:: Recursive record types

Record types can be recursive, e.g,

::

    type t = { a: int; next: option t; }

Recursive record types cannot have invariants, cannot have mutable
fields, and cannot be private.

Range types
^^^^^^^^^^^

.. index:: range type

A declaration of the form ``type r = < range a b >`` defines a type that
projects into the integer range ``[a,b]``. Note that in order to make
such a declaration the theory ``int.Int`` must be imported.

Why3 let you cast an integer literal in a range type (e.g. ``(42:r)``)
and will check at typing that the literal is in range. Defining such a
range type :math:`r` automatically introduces the following:

::

      function  r'int r : int
      constant  r'maxInt : int
      constant  r'minInt : int

The function ``r'int`` projects a term of type ``r`` to its integer
value. The two constants represent the high bound and low bound of the
range respectively.

Unless specified otherwise with the meta ``keep:literal`` on ``r``, the
transformation :why3:transform:`eliminate_literal` introduces an axiom

::

    axiom r'axiom : forall i:r. r'minInt <= r'int i <= r'maxInt

and replaces all casts of the form ``(42:r)`` with a constant and an
axiom as in:

::

    constant rliteral7 : r
    axiom rliteral7_axiom : r'int rliteral7 = 42

This type is used in the standard library in the theories ``bv.BV8``,
``bv.BV16``, ``bv.BV32``, ``bv.BV64``.

Floating-point types
^^^^^^^^^^^^^^^^^^^^

A declaration of the form ``type f = < float eb sb >`` defines a type of
floating-point numbers as specified by the IEEE-754
standard :cite:`ieee754-2008`. Here the literal ``eb``
represents the number of bits in the exponent and the literal ``sb`` the
number of bits in the significand (including the hidden bit). Note that
in order to make such a declaration the theory ``real.Real`` must be
imported.

Why3 let you cast a real literal in a float type (e.g. ``(0.5:f)``) and
will check at typing that the literal is representable in the format.
Note that Why3 do not implicitly round a real literal when casting to a
float type, it refuses the cast if the literal is not representable.

Defining such a type ``f`` automatically introduces the following:

::

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

Unless specified otherwise with the meta ``keep:literal`` on ``f``, the
transformation :why3:transform:`eliminate_literal` will introduce an axiom

::

    axiom f'axiom :
      forall x:f. f'isFinite x -> -. max_real <=. f'real x <=. max_real

where ``max_real`` is the value of the biggest finite float in the
specified format. The transformation also replaces all casts of the form
``(0.5:f)`` with a constant and an axiom as in:

::

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

.. _Module Cloning:

Module Cloning
^^^^^^^^^^^^^^

TO BE COMPLETED


The Why3 Standard Library
-------------------------

The Why3 standard library provides general-purpose modules, to be used
in logic and/or programs. It can be browsed on-line at
http://why3.lri.fr/stdlib/. Each file contains one or several modules.
To ``use`` or ``clone`` a module ``M`` from file ``file``, use the
syntax ``file.M``, since ``file`` is available in Why3’s default load
path. For instance, the module of integers and the module of arrays
indexed by integers are imported as follows:

::

      use int.Int
      use array.Array

A sub-directory ``mach/`` provides various modules to model machine
arithmetic. For instance, the module of 63-bit integers and the module
of arrays indexed by 63-bit integers are imported as follows:

::

      use mach.int.Int63
      use mach.array.Array63

In particular, the types and operations from these modules are mapped to
native OCaml’s types and operations when Why3 code is extracted to OCaml
(see :numref:`sec.extract`).

Library `int`: mathematical integers
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The library `int` contains several modules whose dependencies are
displayed on Figure :numref:`fig.lib.int`.

.. %EXECUTE bin/why3pp --output=dep stdlib/int.mlw | tred > doc/stdlib-dot/library-int.dot

.. graphviz:: stdlib-dot/library-int.dot
   :caption: Module dependencies in library `int`
   :name: fig.lib.int

The main module is `Int` which provides basic operations like addition
and multiplication, and comparisons.

The division of modulo operations are defined in other modules. They
indeed come into two flavours: the module `EuclideanDivision` proposes
a version where the result of the modulo is always non-negative,
whereas the module `ComputerDivision` provides a version which matches
the standard definition available in programming languages like C,
Java or OCaml. Note that these modules do not provide any divsion or
modulo operations to be used in programs. For those, you must use the
module `mach.int.Int` instead, which provides these operations,
including proper pre-conditions, and with the usual infix syntax `x /
y` and `x % y`.

The detailed documentation of the library is available on-line at
http://why3.lri.fr/stdlib/int.html


Library `array`: array data structure
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The library `array` contains several modules whose dependencies are
displayed on Figure :numref:`fig.lib.array`.

.. %EXECUTE bin/why3pp --output=dep stdlib/array.mlw | tred > doc/stdlib-dot/library-array.dot

.. graphviz:: stdlib-dot/library-array.dot
   :caption: Module dependencies in library `array`
   :name: fig.lib.array

The main module is `Array`, providing the operations for accessing and
updating an array element, with respective syntax `a[i]` and `a[i] <-
e`, and proper pre-conditions for the indexes. The length of an array
is denoted as `a.length`. A fresh array can be created using `make l
v` where `l` is the desired length and `v` is the initial values of
all cells.

The detailed documentation of the library is available on-line at
http://why3.lri.fr/stdlib/array.html
