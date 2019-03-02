Language Reference
==================

In this chapter, we describe the syntax and semantics of WhyML.

Lexical Conventions
-------------------

Blank characters are space, horizontal tab, carriage return, and line
feed. Blanks separate lexemes but are otherwise ignored. Comments are
enclosed by ``(*`` and ``*)`` and can be nested. Note that ``(*)`` does
not start a comment.

Strings are enclosed in double quotes (``"``). Double quotes can be
escaped inside strings using the backslash character (``\``). The other
special sequences are ``\n`` for line feed and ``\t`` for horizontal
tab. In the following, strings are referred to with the non-terminal .

The syntax for numerical constants is given by the following rules:

``0``\ ``9``,\ ``0``\ ``9``\ ``a``\ ``f``\ ``A``\ ``F``,\ ``0``\ ``7``,\ ``0``\ ``1``,\ ``95``\ &
``0x``\ ``0X``\ ``95``\ & ``0o``\ ``0O``\ ``95``\ &
``0b``\ ``0B``\ ``95``\ & ,& ``46``\ & ``46``\ & ``0x``\ ``0X``\ &
``0x``\ ``0X``\ ``46``\ & ``0x``\ ``0X``\ ``46``\ &
,\ ``e``\ ``E``\ ``45``\ ``43``,\ ``p``\ ``P``\ ``45``\ ``43``

Integer and real constants have arbitrary precision. Integer constants
can be given in base 10, 16, 8 or 2. Real constants can be given in base
10 or 16. Notice that the exponent in hexadecimal real constants is
written in base 10.

Identifiers are composed of letters, digits, underscores, and primes.
The syntax distinguishes identifiers that start with a lowercase letter
or an underscore (), identifiers that start with an uppercase letter (),
and identifiers that start with a prime (, used exclusively for type
variables):

``a``\ ``z``\ ``A``\ ``Z``,\ ``39``\ ``95``,\ ``a``\ ``z``\ ``95``,\ ``A``\ ``Z``,\ ``39``\ ``a``\ ``z``

Identifiers that contain a prime followed by a letter, such as
``int32’max``, are reserved for symbols introduced by Why3 and cannot be
used for user-defined symbols.

In order to refer to symbols introduced in different namespaces
(*scopes*), we can put a dot-separated “qualifier prefix” in front of an
identifier (e.g. ``Map.S.get``). This allows us to use the symbol
``get`` from the scope ``Map.S`` without importing it in the current
namespace:

``46``, ,

All parenthesised expressions in WhyML (types, patterns, logical terms,
program expressions) admit a qualifier before the opening parenthesis,
e.g. \ ``Map.S.(get m i)``. This imports the indicated scope into the
current namespace during the parsing of the expression under the
qualifier. For the sake of convenience, the parentheses can be omitted
when the expression itself is enclosed in parentheses, square brackets
or curly braces.

Prefix and infix operators are built from characters organized in four
precedence groups (*op-char-1* to *op-char-4*), with optional primes at
the end:

1\ ``61``\ ``60``\ ``62``\ ``126``\ & ,2\ ``43``\ ``45``\ &
,3\ ``42``\ ``47``\ ``92``\ ``37``\ &
,4\ ``33``\ ``36``\ ``38``\ ``63``\ ``64``\ ``94``\ ``46``\ ``58``\ ``124``\ ``35``\ &
,12341234& ,234234& ,3434& ,1123411234\ ``39``\ & ,22342234\ ``39``\ &
,334334\ ``39``\ & ,44\ ``39``\ & ,1234\ ``39``\ &
,\ ``33``\ ``63``\ 4\ ``39``\ &

Infix operators from a high-numbered group bind stronger than the infix
operators from a low-numbered group. For example, infix operator ``.*.``
from group 3 would have a higher precedence than infix operator ``->-``
from group 1. Prefix operators always bind stronger than infix
operators. The so-called “tight operators” are prefix operators that
have even higher precedence than the juxtaposition (application)
operator, allowing us to write expressions like ``inv !x`` without
parentheses. Finally, any identifier, term, formula, or expression in a
WhyML source can be tagged either with a string *attribute* or a
location:

``9164`` ...``93``\ & ``9135``\ ``93``\ &

An attribute cannot contain newlines or closing square brackets; leading
and trailing spaces are ignored. A location consists of a file name in
double quotes, a line number, and starting and ending character
positions.

Type expressions
----------------

WhyML features an ML-style type system with polymorphic types, variants
(sum types), and records that can have mutable fields. The syntax for
type expressions is the following:

& ``4562``\ & ,& & ``4041``\ & ``40``\ ``44``\ ``41``\ &
``123``\ ``125``\ & ``40``\ ``41``\ &

Built-in types are ``int`` (arbitrary precision integers), ``real``
(real numbers), ``bool``, the arrow type (also called the *mapping
type*), and the tuple types. The empty tuple type is also called the
*unit type* and can be written as ``unit``.

Note that the syntax for type expressions notably differs from the usual
ML syntax. In particular, the type of polymorphic lists is written
``list ’a``, and not ``’a list``.

*Snapshot types* are specific to WhyML, they denote the types of ghost
values produced by pure logical functions in WhyML programs. A snapshot
of an immutable type is the type itself: thus, ``{int}`` is the same as
``int`` and ``{list ’a}`` is the same as ``list ’a``. A snapshot of a
mutable type, however, represents a snapshot value which cannot be
modified anymore. Thus, a snapshot array ``a`` of type ``{array int}``
can be read from (``a[42]`` is accepted) but not written into
(``a[42] <- 0`` is rejected). Generally speaking, a program function
that expects an argument of a mutable type will accept an argument of
the corresponding snapshot type as long as it is not modified by the
function.

Logical expressions: terms and formulas
---------------------------------------

& & ``true``\ ``false``\ & ``4041``\ & & ``40``\ ``41``\ &
``begin``\ ``end``\ & & ``123``\ ``125``\ &
``123``\ ``with``\ ``125``\ & ``46``\ & ``91``\ ``93``\ ``39``\ &
``91``\ ``6045``\ ``93``\ ``39``\ & ``91``\ ``4646``\ ``93``\ ``39``\ &
``91``\ ``4646``\ ``93``\ ``39``\ & ``91``\ ``4646``\ ``93``\ ``39``\ &
& & 4& 3& 2& ``at``\ & ``old``\ & 1& ...& ,\ ``61``\ ``59``\ & ,& ,&
``40``\ ``41``\ & ``40``\ ``41``\ ``95``\ ``39``\ & ,1& 2& 3& 4&
``95``\ & ``95``\ & ``91``\ ``93``\ ``39``\ &
``91``\ ``6045``\ ``93``\ ``39``\ & ``91``\ ``93``\ ``39``\ ``6045``\ &
``91``\ ``4646``\ ``93``\ ``39``\ &
``91``\ ``95``\ ``4646``\ ``93``\ ``39``\ &
``91``\ ``4646``\ ``95``\ ``93``\ ``39``\ &

...& ``not``\ & ``4792``\ & ``3838``\ & ``9247``\ & ``124124``\ &
``by``\ & ``so``\ & ``4562``\ & ``604562``\ & ``58``\ & & ``44``\ &
``46``\ & ...& ,\ ``forall``\ ``exists``,\ ``44``,\ ``58``,\ ``95``
,,\ ``91``\ ``124``\ ``93``\ & ,\ ``44``\ &

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
``s[i]’`` sequence access. Notice that the in-place update operator
``a[i] <- v`` cannot be used inside logical terms: all effectful
operations are restricted to program expressions. To represent the
result of a collection update, we should use a pure logical update
operator ``a[i <- v]`` instead. WhyML supports “associated” names for
operators, obtained by adding a suffix after the parenthesised operator
name. For example, an axiom that represents the specification of the
infix operator ``(+)`` may be called ``(+)’spec`` or ``(+)_spec``. As
with normal identifiers, names with a letter after a prime, such as
``(+)’spec``, can only be introduced by Why3, and not by the user in a
WhyML source.

The ``at`` and ``old`` operators are used inside postconditions and
assertions to refer to the value of a mutable program variable at some
past moment of execution (see the next section for details). These
operators have higher precedence than the infix operators from group 1
(*infix-op-1*): ``old i > j`` is parsed as ``(old i) > j`` and not as
``old (i > j)``.

Infix operators from groups 2-4 are left-associative. Infix operators
from group 1 are non-associative and can be chained. For example, the
term ``0 <= i < j < length a`` is parsed as the conjunction of three
inequalities ``0 <= i``, ``i < j``, and ``j < length a``.

As with normal identifiers, we can put a qualifier over a parenthesised
operator, e.g. \ ``Map.S.([]) m i``. Also, as noted above, a qualifier
can be put over a parenthesised term, and the parentheses can be omitted
if the term is a record or a record update.

The propositional connectives in WhyML formulas are listed in
:numref:`fig.bnf:term2`. The non-standard connectives — asymmetric
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
premise justifies the conclusion), ``(exists x. B /92 C) -> A`` (the
proof justifies the affirmation), and finally, ``A -> D`` (the proof of
``A`` is discarded and ``A`` is used to prove ``D``).

The behaviour of the splitting transformations is further controlled by
attributes ``[@stop_split]`` and ``[@case_split]``. Consult
:numref:`tech.trans:split` for details.

Among the propositional connectives, ``not`` has the highest precedence,
``&&`` has the same precedence as ``/92`` (weaker than negation), ``||``
has the same precedence as ``92/`` (weaker than conjunction), ``by``,
``so``, ``->``, and ``<->`` all have the same precedence (weaker than
disjunction). All binary connectives except equivalence are
right-associative. Equivalence is non-associative and is chained
instead: ``A <-> B <-> C`` is transformed into a conjunction of
``A <-> B`` and ``B <-> C``. To reduce ambiguity, WhyML forbids to place
a non-parenthesised implication at the right-hand side of an
equivalence: ``A <-> B -> C`` is rejected.

...& ``if``\ ``then``\ ``else``\ & ``match``\ ``with``\ ``end``\ &
``let``\ ``61``\ ``in``\ & ``let``\ ``61``\ ``in``\ &
``fun``\ ``4562``\ & ,\ ``124``\ ``4562`` ,& ``4041``\ &
``123``\ ``61``\ ``59``\ ``125``\ & & ``ghost``\ & ``as``\ ``ghost``\ &
``44``\ & ``124``\ & ``40``\ ``41``\ & ,& ,& &
``40``\ ``ghost``\ ``41``\ & ``40``\ ``ghost``\ ``41``\ &
``40``\ ``ghost``\ ``58``\ ``41``\ &

In :numref:`fig.bnf:term3`, we find the more advanced term constructions:
conditionals, let-bindings, pattern matching, and local function
definitions, either via the ``let-in`` construction or the ``fun``
keyword. The pure logical functions defined in this way are called
*mappings*; they are first-class values of “arrow” type
``\tau_1 -> \tau_2``.

The patterns are similar to those of OCaml, though the ``when`` clauses
and numerical constants are not supported. Unlike in OCaml, ``as`` binds
stronger than the comma: in the pattern ``(p_1,p_2 as x)``, variable
``x`` is bound to the value matched by pattern :math:`p_2`. Also notice
the closing ``end`` after the ``match-with`` term. A ``let-in``
construction with a non-trivial pattern is translated as a
``match-with`` term with a single branch.

Inside logical terms, pattern matching must be exhaustive: WhyML rejects
a term like ``let Some x = o in \dots``, where ``o`` is a variable of an
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
``function add ’a (set ’a) : set ’a``. A standalone non-qualified
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

& & ``true``\ ``false``\ & ``4041``\ & & ``40``\ ``41``\ &
``begin``\ ``end``\ & & ``123``\ ``61``\ ``59``\ ``125``\ &
``123``\ ``with``\ ``61``\ ``59``\ ``125``\ & ``46``\ &
``91``\ ``93``\ ``39``\ & ``91``\ ``6045``\ ``93``\ ``39``\ &
``91``\ ``4646``\ ``93``\ ``39``\ & ``91``\ ``4646``\ ``93``\ ``39``\ &
``91``\ ``4646``\ ``93``\ ``39``\ & & & 4& 3& 2& 1& ``not``\ &
``3838``\ & ``124124``\ & ``58``\ & & ``ghost``\ & ``44``\ & ``6045``\ &
...&

Keyword ``ghost`` marks the expression as ghost code added for
verification purposes. Ghost code is removed from the final code
intended for execution, and thus cannot affect the computation of the
program results nor the content of the observable memory.

Assignment updates in place a mutable record field or an element of a
collection. The former can be done simultaneously on a tuple of values:
``x.f, y.g <- a, b``. The latter form, ``a[i] <- v``, amounts to a call
of the ternary bracket operator ``([]<-)`` and cannot be used in a
multiple assignment.

...& & ``if``\ ``then``\ ``else``\ &
``match``\ ``with``\ ``124``\ ``4562``\ ``end``\ & ``begin``\ ``end``\ &
``59``\ & ``let``\ ``61``\ ``in``\ & ``let``\ ``in``\ &
``let``\ ``rec``\ ``with``\ ``in``\ & ``fun``\ ``4562``\ & ``any``\ &
,\ ``61``\ & ,\ ``ghost``\ ``58``\ &
,\ ``function``\ ``predicate``\ ``lemma``\ & ,&
``40``\ ``44``\ ``41``\ & ``40``\ ``44``\ ``41``\ & ,\ ``ghost``\ &
,\ ``ghost``\ ``58``\ & ,\ ``requires``\ ``123``\ ``125``\ &
``ensures``\ ``123``\ ``125``\ &
``returns``\ ``123``\ ``124``\ ``4562``\ ``125``\ &
``raises``\ ``123``\ ``124``\ ``4562``\ ``125``\ &
``raises``\ ``123``\ ``44``\ ``125``\ &
``reads``\ ``123``\ ``44``\ ``125``\ &
``writes``\ ``123``\ ``44``\ ``125``\ &
``alias``\ ``123``\ ``44``\ ``125``\ &
``variant``\ ``123``\ ``44``\ ``125``\ & ``diverges``\ &
``reads``\ ``writes``\ ``alias``\ ``123``\ ``125``\ & ,\ ``46``\ &
,\ ``with``\ & ,\ ``with``\ &

The Why3 Language
-----------------

Terms
~~~~~

The syntax for terms is given in :numref:`fig.bnf:term1`. The various
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

The syntax for formulas is given :numref:`fig.bnf:formula`. The various
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

The syntax for theories is given on :numref:`fig.bnf:theorya`
and [fig:bnf:theoryb].

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

The function ``r’int`` projects a term of type ``r`` to its integer
value. The two constants represent the high bound and low bound of the
range respectively.

Unless specified otherwise with the meta ``keep:literal`` on ``r``, the
transformation *eliminate\_literal* introduces an axiom

::

    axiom r'axiom : forall i:r. r'minInt <= r'int i <= r'maxInt

and replaces all casts of the form ``(42:r)`` with a constant and an
axiom as in:

::

    constant rliteral7 : r
    axiom rliteral7_axiom : r'int rliteral7 = 42

This type is used in the standard library in the theories ``bv.BV8``,
``bv.BV16``, ``bv.BV32``, ``bv.BV64``.

Floating-point Types
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
``f’isFinite`` indicates whether its argument is neither infinite nor
NaN. The function ``f’real`` projects a finite term of type ``f`` to its
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

The WhyML Language
------------------

Specification
~~~~~~~~~~~~~

The syntax for specification clauses in programs is given in
:numref:`fig.bnf:spec`.

Within specifications, terms are extended with new constructs ``old``
and ``at``:

Within a postcondition, :math:`\verb|old|~t` refers to the value of term
:math:`t` in the prestate. Within the scope of a code mark :math:`L`,
the term :math:`\verb|at|~t~\verb|'|L` refers to the value of term
:math:`t` at the program point corresponding to :math:`L`.

Expressions
~~~~~~~~~~~

The syntax for program expressions is given in :numref:`fig.bnf:expra`
and :numref:`fig.bnf:exprb`.

In applications, arguments are evaluated from right to left. This
includes applications of infix operators, with the only exception of
lazy operators ``&&`` and ``||`` that evaluate from left to right,
lazily.

Modules
~~~~~~~

The syntax for modules is given in :numref:`fig.bnf:module`.

Any declaration which is accepted in a theory is also accepted in a
module. Additionally, modules can introduce record types with mutable
fields and declarations which are specific to programs (global
variables, functions, exceptions).

Files
~~~~~

A WhyML input file is a (possibly empty) list of theories and modules.

A theory defined in a WhyML file can only be used within that file. If a
theory is supposed to be reused from other files, be they Why3 or WhyML
files, it should be defined in a Why3 file.

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

      use import int.Int
      use import ref.Ref

A sub-directory ``mach/`` provides various modules to model machine
arithmetic. For instance, the module of 63-bit integers and the module
of arrays indexed by 63-bit integers are imported as follows:

::

      use import mach.int.Int63
      use import mach.array.Array63

In particular, the types and operations from these modules are mapped to
native OCaml’s types and operations when Why3 code is extracted to OCaml
(see :numref:`sec.extract`).
