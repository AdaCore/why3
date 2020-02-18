Language Reference
==================

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
or an underscore (:token:`lident`), identifiers that start with an
uppercase letter (:token:`uident`), and identifiers that start with
a prime (:token:`qident`, used exclusively for type variables):

.. productionlist::
    alpha: "a" - "z" | "A" - "Z"
    suffix: `alpha` | `digit` | "'" | "_"
    lident: ("a" - "z") `suffix`* | "_" `suffix`+
    uident: ("A" - "Z") `suffix`*
    qident: "'" ("a" - "z") `suffix`*


Identifiers that contain a prime followed by a letter, such as
``int32'max``, are reserved for symbols introduced by Why3 and cannot be
used for user-defined symbols.

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
    infix_op_1: ``op_char_1234`* `op_char_1` `op_char_1234`* "'"*
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
             : | "[#" string digit+ digit+ digit+ "]"


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
    type: `lqualid` `type_arg`+            ; polymorphic type symbol
        : | `type` "->" `type`            ; mapping type (right-associative)
        : | `type_arg`
    type_arg: `lqualid`                  ; monomorphic type symbol (sort)
            : | `qident`                    ; type variable
            : | "()"		             ; unit type
            : | "(" `type` ("," `type`)+ ")"  ; tuple type
            : | "{" `type` "}"              ; snapshot type
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
    term: `integer`            ; integer constant
        : | `real`                    ; real constant
        : | "true" | "false"        ; Boolean constant
        : | "()"                    ; empty tuple
        : | `qualid`                  ; qualified identifier
        : | `qualifier`? "(" `term` ")"        ; term in a scope
        : | `qualifier`? "begin" `term` "end"  ; idem
        : | `tight_op` `term`           ; tight operator
        : | "{" `term_field`+ "}"     ; record
        : | "{" `term` "with" `term_field`+ "}" ; record update
        : | `term` "." `lqualid`        ; record field access
        : | `term` "[" `term` "]" "'"*  ; collection access
        : | `term` "[" `term` "<-" `term` "]" "'"*  ; collection update
        : | `term` "[" `term` ".." `term` "]" "'"*  ; collection slice
        : | `term` "[" `term` ".." "]" "'"*  ; right-open slice
        : | `term` "[" ".." `term` "]" "'"*  ; left-open slice
        : | `term` `term`+              ; application
        : | `prefix_op` `term`          ; prefix operator
        : | `term` `infix_op_4` `term`    ; infix operator 4
        : | `term` `infix_op_3` `term`    ; infix operator 3
        : | `term` `infix_op_2` `term`    ; infix operator 2
        : | `term` "at" `uident`        ; past value
        : | "old" `term`              ; initial value
        : | `term` `infix_op_1` `term`    ; infix operator 1
        : | "not" `term`              ; negation
        : | `term` "/\" `term`          ; conjunction
        : | `term` "&&" `term`          ; asymmetric conjunction
        : | `term` "\/" `term`          ; disjunction
        : | `term` "||" `term`          ; asymmetric disjunction
        : | `term` "by" `term`          ; proof indication
        : | `term` "so" `term`          ; consequence indication
        : | `term` "->" `term`          ; implication
        : | `term` "<->" `term`         ; equivalence
        : | `term` ":" `type`           ; type cast
        : | `attribute`+ `term`         ; attributes
        : | `term` ("," `term`)+        ; tuple
        : | `quantifier` `quant_vars` `triggers`? "." `term` ; quantifier
        : | ...                     ; (to be continued)
    term_field: `lqualid` "=" `term` ";" ; field = value
    qualid: `qualifier`? (`lident_ext` | `uident`)  ; qualified identifier
    lident_ext: `lident`                   ; lowercase identifier
              : | "(" `ident_op` ")"         ; operator identifier
              : | "(" `ident_op` ")" ("_" | "'") alpha suffix* ; associated identifier
    ident_op:  `infix_op_1`              ;   infix operator 1
            : | `infix_op_2`              ;   infix operator 2
            : | `infix_op_3`              ;   infix operator 3
            : | `infix_op_4`              ;   infix operator 4
            : | `prefix_op` "_"           ;   prefix operator
            : | `tight_op` "_"?           ;   tight operator
            : | "[" "]" "'" *           ;   collection access
            : | "[" "<-" "]" "'"*       ;   collection update
            : | "[" "]" "'"* "<-"       ;   in-place update
            : | "[" ".." "]" "'"*       ;   collection slice
            : | "[" "_" ".." "]" "'"*   ;   right-open slice
            : | "[" ".." "_" "]" "'"*   ;   left-open slice
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

The syntax of WhyML terms is given in
Figures [fig:bnf:term1]-[fig:bnf:term3]. The constructions are listed in
the order of decreasing precedence. For example, as was mentioned above,
tight operators have the highest precedence of all operators, so that
``-p.x`` denotes the negation of the record field ``p.x``, whereas
``!p.x`` denotes the field ``x`` of a record stored in the reference
``p``.

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
   and ``not A /92 B``. If ``A || B`` occurs as a goal, it behaves as a
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
attributes ``[@stop_split]`` and ``[@case_split]``. Consult
:numref:`tech.trans:split` for details.

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
      : | "if" `term` "then" `term` "else" `term`     ; conditional
      : | "match" `term` "with" `term_case`+ "end"  ; pattern matching
      : | "let" `pattern` "=" `term` "in" `term`      ; let-binding
      : | "let" `symbol` `param`+ "=" `term` "in" `term`  ; mapping definition
      : | "fun" `param`+ "->" `term`                ; unnamed mapping
  term_case: "|" `pattern` "->" `term`
  pattern: `binder`                            ; variable or "_"
         : | "()"                              ; empty tuple
         : | "{" (`lqualid` "=" `pattern` ";")+ "}"  ; record pattern
         : | `uqualid` `pattern`*                  ; constructor
         : | "ghost" `pattern`                   ; ghost sub-pattern
         : | `pattern` "as" "ghost"? `bound_var`   ; named sub-pattern
         : | `pattern` "," `pattern`              ; tuple pattern
         : | `pattern` "|" `pattern`               ; "or" pattern
         : | `qualifier`? "(" `pattern` ")"        ; pattern in a scope
  symbol: `lident_ext` `attribute`*      ; user-defined symbol
  param: `type-arg`                          ; unnamed typed
       : | `binder`                            ; (un)named untyped
       : | "(" "ghost"? `type` ")"             ; unnamed typed
       : | "(" "ghost"? `binder` ")"           ; (un)named untyped
       : | "(" "ghost"? `binder`+ ":" `type` ")" ; multi-variable typed %

Above, we find the more advanced term constructions:
conditionals, let-bindings, pattern matching, and local function
definitions, either via the ``let-in`` construction or the ``fun``
keyword. The pure logical functions defined in this way are called
*mappings*; they are first-class values of “arrow” type
:samp:`{t} -> {u}`.

The patterns are similar to those of OCaml, though the ``when`` clauses
and numerical constants are not supported. Unlike in OCaml, ``as`` binds
stronger than the comma: in the pattern :samp:`({p},{q} as {x})`, variable
*x* is bound to the value matched by pattern *q*. Also notice
the closing ``end`` after the ``match-with`` term. A ``let-in``
construction with a non-trivial pattern is translated as a
``match-with`` term with a single branch.

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

The syntax of program expressions is given in
Figures [fig:bnf:expr1]-[fig:bnf:expr2]. As before, the constructions
are listed in the order of decreasing precedence. The rules for tight,
prefix, infix, and bracket operators are the same as for logical terms.
In particular, the infix operators from group 1 can be chained. Notice
that binary operators ``&&`` and ``||`` denote here the usual lazy
conjunction and disjunction, respectively.

.. productionlist::
    expr: `integer`            ; integer constant
        : | `real`                    ; real constant
        : | "true" | "false"        ; Boolean constant
        : | "()"                    ; empty tuple
        : | `qualid`                  ; identifier in a scope
        : | `qualifier`? "(" `expr` ")"        ; expression in a scope
        : | `qualifier`? "begin" `expr` "end"  ; idem
        : | `tight_op` `expr`           ; tight operator
        : | "{" (`lqualid` "=" `expr` ";")+ "}"     ; record
        : | "{" `expr` "with" (`lqualid` "=" `expr` ";")+ "}" ; record update
        : | `expr` "." `lqualid`        ; record field access
        : | `expr` "[" `expr` "]" "'"*  ; collection access
        : | `expr` "[" `expr` "<-" `expr` "]" "'"*  ; collection update
        : | `expr` "[" `expr` ".." `expr` "]" "'"*  ; collection slice
        : | `expr` "[" `expr` ".." "]" "'"*  ; right-open slice
        : | `expr` "[" ".." `expr` "]" "'"*  ; left-open slice
        : | `expr` `expr`+              ; application
        : | `prefix_op` `expr`          ; prefix operator
        : | `expr` `infix_op_4` `expr`    ; infix operator 4
        : | `expr` `infix_op_3` `expr`    ; infix operator 3
        : | `expr` `infix_op_2` `expr`    ; infix operator 2
        : | `expr` `infix_op_1` `expr`    ; infix operator 1
        : | "not" `expr`              ; negation
        : | `expr` "&&" `expr`          ; lazy conjunction
        : | `expr` "||" `expr`          ; lazy disjunction
        : | `expr` ":" `type`           ; type cast
        : | `attribute`+ `expr`         ; attributes
        : | "ghost" `expr`            ; ghost expression
        : | `expr` ("," `expr`)+        ; tuple
        : | `expr` "<-" `expr`          ; assignment
        : | `expr` spec+                            ; added specification
        : | "if" `expr` "then" `expr` ("else" `expr`)?  ; conditional
        : | "match" `expr` "with" ("|" pattern "->" `expr`)+ "end"  ; pattern matching
        : | qualifier? "begin" spec+ `expr` "end"   ; abstract block
        : | `expr` ";" `expr`                         ; sequence
        : | "let" `pattern` "=" `expr` "in" `expr`      ; let-binding
        : | "let" `fun_defn` "in" `expr`              ; local function
        : | "let" "rec" `fun_defn` ("with" `fun_defn`)* "in" `expr`   ; recursive function
        : | "fun" `param`+ `spec`* "->" `spec`* `expr`    ; unnamed function
        : | "any" result `spec`*                    ; arbitrary value
    fun_defn: `fun-head` `spec`* "=" `spec`* `expr` ; function definition
    fun-head: "ghost"? `kind`? `symbol` `param`+ (":" `result`)? ; function header
    kind: "function" | "predicate" | "lemma" ; function kind
    result: `ret_type`                      ;
      : | "(" `ret_type` ("," `ret_type`)* ")"      ;
      : | "(" `ret-name` ("," `ret-name`)* ")"      ;
    ret_type: "ghost"? `type`                ; unnamed result
    ret_name: "ghost"? `binder` ":" `type`     ; named result
    spec: "requires"  "{" `term` "}"                      ; pre-condition
      : | "ensures"   "{" `term` "}"                      ; post-condition
      : | "returns"   "{" ("|" `pattern` "->" `term`)+  "}" ; post-condition
      : | "raises"    "{" ("|" `pattern` "->" `term`)+  "}" ; exceptional post-c.
      : | "raises"    "{" `uqualid` ("," `uqualid`)*    "}" ; raised exceptions
      : | "reads"     "{" `lqualid` ("," `lqualid`)*    "}" ; external reads
      : | "writes"    "{" `path` ("," `path`)*          "}" ; memory writes
      : | "alias"     "{" `alias` ("," `alias`)*        "}" ; memory aliases
      : | "variant"   "{" `variant` ("," `variant`)*    "}" ; termination variant
      : | "diverges"                                    ; may not terminate
      : | ("reads" | "writes" | "alias") "{" "}"        ; empty effect
    path: `lqualid` ("." `lqualid`)*           ; \texttt{v.field1.field2}
    alias: `path` "with" `path`                ; \texttt{arg1 with result}
    variant: `term` ("with" `lqualid`)?        ; variant + WF-order %


Keyword ``ghost`` marks the expression as ghost code added for
verification purposes. Ghost code is removed from the final code
intended for execution, and thus cannot affect the computation of the
program results nor the content of the observable memory.

Assignment updates in place a mutable record field or an element of a
collection. The former can be done simultaneously on a tuple of values:
``x.f, y.g <- a, b``. The latter form, ``a[i] <- v``, amounts to a call
of the ternary bracket operator ``([]<-)`` and cannot be used in a
multiple assignment.



The Why3 Language
-----------------

Terms
~~~~~

The syntax for terms is given in :token:`term`. The various
constructs have the following priorities and associativities, from
lowest to greatest priority:

+---------------------------------+-----------------+
| construct                       | associativity   |
+=================================+=================+
| ``if then else`` / ``let in``   | –               |
+---------------------------------+-----------------+
| label                           | –               |
+---------------------------------+-----------------+
| cast                            | –               |
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

Note the curryfied syntax for function application, though partial
application is not allowed (rejected at typing).

Formulas
~~~~~~~~

The syntax for formulas is given :token:`term`. The various
constructs have the following priorities and associativities, from
lowest to greatest priority:

+---------------------------------+-----------------+
| construct                       | associativity   |
+=================================+=================+
| ``if then else`` / ``let in``   | –               |
+---------------------------------+-----------------+
| label                           | –               |
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
| infix level 1                   | left            |
+---------------------------------+-----------------+
| infix level 2                   | left            |
+---------------------------------+-----------------+
| infix level 3                   | left            |
+---------------------------------+-----------------+
| infix level 4                   | left            |
+---------------------------------+-----------------+
| prefix                          | –               |
+---------------------------------+-----------------+

Note that infix symbols of level 1 include equality (``=``) and
disequality (``<>``).

Notice that there are two symbols for the conjunction: ``/\`` and
``&&``, and similarly for disjunction. They are logically equivalent,
but may be treated slightly differently by some transformations. For
instance, ``split`` transforms the goal ``A /\ B`` into subgoals ``A``
and ``B``, whereas it transforms ``A && B`` into subgoals ``A`` and
``A -> B``. Similarly, it transforms ``not (A || B)`` into subgoals
``not A`` and ``not ((not A) /\ B)``. The ``by``/``so`` connectives are
proof indications. They are logically equivalent to their first
argument, but may affect the result of some transformations. For
instance, the ``split_goal`` transformations interpret those connectives
as introduction of logical cuts (see [tech:trans:split] for details).

Theories
~~~~~~~~

.. productionlist::
    theory: "theory" `uident_nq` `label`* `decl`* "end"
    decl: "type" `type_decl` ("with" `type_decl`)* ;
      : | "constant" `constant_decl` ;
      : | "function" `function_decl` ("with" `logic_decl`)* ;
      : | "predicate" `predicate_decl` ("with" `logic_decl`)* ;
      : | "inductive" `inductive_decl` ("with" `inductive_decl`)* ;
      : | "coinductive" `inductive_decl` ("with" `inductive_decl`)* ;
      : | "axiom" `ident_nq` ":" `formula` 	   ;
      : | "lemma" `ident_nq` ":" `formula` 	   ;
      : | "goal"  `ident_nq` ":" `formula` 	   ;
      : | "use" `imp_exp` `tqualid` ("as" `uident`)?     ;
      : | "clone" `imp_exp` `tqualid` ("as" `uident`)? `subst`? ;
      : | "scope" "import"? `uident_nq` `decl`* "end" ;
      : | "import" `uident` ;
    logic_decl: `function_decl` ;
      : | `predicate_decl`
    constant_decl: `lident_nq` `label`* ":" `type` ;
      : | `lident_nq` `label`* ":" `type` "=" `term`
    function_decl: `lident_nq` `label`* `type_param`* ":" `type` ;
      : | `lident_nq` `label`* `type_param`* ":" `type` "=" `term`
    predicate_decl: `lident_nq` `label`* `type_param`* ;
      : | `lident_nq` `label`* `type_param`* "=" `formula`
    inductive_decl: `lident_nq` `label`* `type_param`* "=" "|"? `ind_case` ("|" `ind_case`)* ;
    ind_case: `ident_nq` `label`* ":" `formula` ;
    imp_exp: ("import" | "export")?
    subst: "with" ("," `subst_elt`)+
    subst_elt: "type" `lqualid` "=" `lqualid` ;
      : | "function" `lqualid` "=" `lqualid`          ;
      : | "predicate" `lqualid` "=" `lqualid`         ;
      : | "scope" (`uqualid` | ".") "=" (`uqualid` | ".")  ;
      : | "lemma" `qualid` 	  		   ;
      : | "goal"  `qualid`			   ;
    tqualid: `uident` | `ident` ("." `ident`)* "." `uident` ;
    type_decl: `lident_nq` `label`* ("'" `lident_nq` `label`*)* `type_defn`; %
    type_defn:                                      ; abstract type
      : | "=" `type `                                      ; alias type
      : | "=" "|"? `type_case` ("|" `type_case`)*            ; algebraic type
      : | "=" "{" `record_field` (";" `record_field`)* "}"   ; record type
      : | "<" "range" `integer` `integer` ">"                ; range type
      : | "<" "float" `integer` `integer` ">"                ; float type
    type_case: `uident` `label`* `type_param`*
    record_field: `lident` `label`* ":" `type`
    type_param: "'" `lident`   ;
     : | `lqualid`                  ;
     : | "(" `lident`+ ":" `type` ")" ;
     : | "(" `type` ("," `type`)* ")" ;
     : | "()"


Algebraic types
^^^^^^^^^^^^^^^

TO BE COMPLETED

Record types
^^^^^^^^^^^^

TO BE COMPLETED

Range types
^^^^^^^^^^^

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
transformation *eliminate_literal* introduces an axiom

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
transformation *eliminate\_literal* will introduce an axiom

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

Files
~~~~~

A Why3 input file is a (possibly empty) list of theories.

.. productionlist::
    file: `theory`*

The WhyML Language
------------------

Specification
~~~~~~~~~~~~~

The syntax for specification clauses in programs is given in
:token:`spec`.

Within specifications, terms are extended with new constructs ``old``
and ``at``:

Within a postcondition, :samp:`old {t}` refers to the value of term
*t* in the prestate. Within the scope of a code mark *L*,
the term :samp:`at {t} '{L}` refers to the value of term
*t* at the program point corresponding to *L*.

Expressions
~~~~~~~~~~~

The syntax for program expressions is given in :token:`expr`.

In applications, arguments are evaluated from right to left. This
includes applications of infix operators, with the only exception of
lazy operators ``&&`` and ``||`` that evaluate from left to right,
lazily.

Modules
~~~~~~~

The syntax for modules is as follows:

.. productionlist::
    module: "module" `uident_nq` `label`* `mdecl`* "end"
    mdecl: `decl`                                ; theory declaration
      : | "type" `mtype_decl` ("with" `mtype_decl`)*    ; mutable types
      : | "type" `lident_nq` ("'" `lident_nq`)* `invariant`+    ; added invariant
      : | "let" "ghost"? `lident_nq` `label`* `pgm_defn`     ;
      : | "let" "rec" `rec_defn`                      ;
      : | "val" "ghost"? `lident_nq` `label`* `pgm_decl`     ;
      : | "exception" `lident_nq` `label`* `type`?           ;
      : | "scope" "import"? `uident_nq` `mdecl`* "end" ;
    mtype_decl: `lident_nq` `label`* ("'" `lident_nq` `label`*)* `mtype_defn`
    mtype_defn:   ; abstract type
      : | "=" `type`    ; alias type
      : | "=" "|"? `type_case` ("|" `type_case`)* `invariant`* ; algebraic type
      : | "=" "{" `mrecord_field` (";" `mrecord_field`)* "}" `invariant`* ; record type
    mrecord_field: "ghost"? "mutable"? `lident_nq` `label`* ":" `type`
    pgm_defn: `fun_body` ;
      : | "=" "fun" `binder`+ `spec`* "->" `spec`* `expr` ;
    pgm_decl: ":" `type`    ; global variable
      : | `param` (`spec`* `param`)+ ":" `type` `spec`*  ; abstract function%


Any declaration which is accepted in a theory is also accepted in a
module. Additionally, modules can introduce record types with mutable
fields and declarations which are specific to programs (global
variables, functions, exceptions).

Files
~~~~~

A WhyML input file is a (possibly empty) list of theories and modules.

.. productionlist::
    file: (`theory` | `module`)*

A theory defined in a WhyML file can only be used within that
file. If a theory is supposed to be reused from other files, be they
Why or WhyML files, it should be defined in a Why file.


The Why3 Standard Library
-------------------------

The Why3 standard library provides general-purpose modules, to be used
in logic and/or programs. It can be browsed on-line at
http://why3.lri.fr/stdlib/. Each file contains one or several modules.
To ``use`` or ``clone`` a module ``M`` from file ``file``, use the
syntax ``file.M``, since ``file`` is available in Why3’s default load
path. For instance, the module of integers and the module of references
are imported as follows:

::

      use int.Int
      use ref.Ref

A sub-directory ``mach/`` provides various modules to model machine
arithmetic. For instance, the module of 63-bit integers and the module
of arrays indexed by 63-bit integers are imported as follows:

::

      use mach.int.Int63
      use mach.array.Array63

In particular, the types and operations from these modules are mapped to
native OCaml’s types and operations when Why3 code is extracted to OCaml
(see :numref:`sec.extract`).
