Technical Informations
======================

Structure of Session Files
--------------------------

The proof session state is stored in an XML file named
``<dir>/why3session.xml``, where ``<dir>`` is the directory of the
project. The XML file follows the DTD given in ``share/why3session.dtd``
and reproduced below.

.. _sec.proverdetectiondata:

Prover Detection
----------------

The data configuration for the automatic detection of installed provers
is stored in the file ``provers-detection-data.conf`` typically located
in directory ``/usr/local/share/why3`` after installation. The content
of this file is reproduced below.

.. _sec.whyconffile:

The ``why3.conf`` Configuration File
------------------------------------

One can use a custom configuration file. The Why3 tools look for it in
the following order:

#. the file specified by the ``-C`` or ``--config`` options,

#. the file specified by the environment variable ``WHY3CONFIG`` if set,

#. the file ``$HOME/.why3.conf`` (``$USERPROFILE/.why3.conf`` under
   Windows) or, in the case of local installation, ``why3.conf`` in the
   top directory of Why3 sources.

If none of these files exist, a built-in default configuration is used.

A section begins with a header inside square brackets and ends at the
beginning of the next section. The header of a section can be a single
identifier, ``[main]``, or it can be composed by a family name and a
single family argument, ``[prover alt-ergo]``.

Sections contain associations ``key=value``. A value is either an
integer (``-555``), a boolean (``true``, ``false``), or a string
(``emacs``). Some specific keys can be attributed multiple values and
are thus allowed to occur several times inside a given section. In that
case, the relative order of these associations matters.

.. _sec.drivers:

Drivers for External Provers
----------------------------

Drivers for external provers are readable files from directory
``drivers``. Experimented users can modify them to change the way the
external provers are called, in particular which transformations are
applied to goals.

[TO BE COMPLETED LATER]

.. _sec.transformations:

Transformations
---------------

This section documents the available transformations. We first describe
the most important ones, and then we provide a quick documentation of
the others, first the non-splitting ones, those which produce exactly
one goal as result, and the others which produce any number of goals.

Notice that the set of available transformations in your own
installation is given by

::

    why3 --list-transforms

Inlining definitions
~~~~~~~~~~~~~~~~~~~~

Those transformations generally amount to replace some applications of
function or predicate symbols with its definition.

inline\_trivial
    expands and removes definitions of the form

    ::

        function  f x_1 ... x_n = (g e_1 ... e_k)
        predicate p x_1 ... x_n = (q e_1 ... e_k)

    when each :math:`e_i` is either a ground term or one of the
    :math:`x_j`, and each :math:`x_1 \dots x_n` occurs at most once in
    all the :math:`e_i`.

inline\_goal
    expands all outermost symbols of the goal that have a non-recursive
    definition.

inline\_all
    expands all non-recursive definitions.

Induction Transformations
~~~~~~~~~~~~~~~~~~~~~~~~~

induction\_ty\_lex
    performs structural, lexicographic induction on goals involving
    universally quantified variables of algebraic data types, such as
    lists, trees, etc. For instance, it transforms the following goal

    ::

        goal G: forall l: list 'a. length l >= 0

    into this one:

    ::

        goal G :
          forall l:list 'a.
             match l with
             | Nil -> length l >= 0
             | Cons a l1 -> length l1 >= 0 -> length l >= 0
             end

    When induction can be applied to several variables, the
    transformation picks one heuristically. The ``[@induction]``
    attribute can be used to force induction over one particular
    variable, with

    ::

        goal G: forall l1 [@induction] l2 l3: list 'a.
                l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3

    induction will be applied on ``l1``. If this attribute is attached
    to several variables, a lexicographic induction is performed on
    these variables, from left to right.

Simplification by Computation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

These transformations simplify the goal by applying several kinds of
simplification, described below. The transformations differ only by the
kind of rules they apply:

compute\_in\_goal
    aggressively applies all known computation/simplification rules.

compute\_specified
    performs rewriting using only built-in operators and user-provided
    rules.

The kinds of simplification are as follows.

-  Computations with built-in symbols, operations on integers, when
   applied to explicit constants, are evaluated. This includes
   evaluation of equality when a decision can be made (on integer
   constants, on constructors of algebraic data types), Boolean
   evaluation, simplification of pattern-matching/conditional
   expression, extraction of record fields, and beta-reduction. At best,
   these computations reduce the goal to ``true`` and the
   transformations thus does not produce any sub-goal. For example, a
   goal like ``6*7=42`` is solved by those transformations.

-  Unfolding of definitions, as done by ``inline_goal``. Transformation
   ``compute_in_goal`` unfolds all definitions, including recursive
   ones. For ``compute_specified``, the user can enable unfolding of a
   specific logic symbol by attaching the meta ``rewrite_def`` to the
   symbol.

   ::

       function sqr (x:int) : int = x * x
       meta "rewrite_def" function sqr

-  Rewriting using axioms or lemmas declared as rewrite rules. When an
   axiom (or a lemma) has one of the forms

   ::

       axiom a: forall ... t1 = t2

   or

   ::

       axiom a: forall ... f1 <-> f2

   then the user can declare

   ::

       meta "rewrite" prop a

   to turn this axiom into a rewrite rule. Rewriting is always done from
   left to right. Beware that there is no check for termination nor for
   confluence of the set of rewrite rules declared.

Instead of using a meta, it is possible to declare an axiom as a rewrite
rule by adding the ``[@rewrite]`` attribute on the axiom name or on the
axiom itself, e.g.:

::

    axiom a [@rewrite]: forall ... t1 = t2
    lemma b: [@rewrite] forall ... f1 <-> f2

The second form allows some form of local rewriting, e.g.

::

    lemma l: forall x y. ([@rewrite] x = y) -> f x = f y

can be proved by ``introduce_premises`` followed by
``compute_specified``.

Bound on the number of reductions
'''''''''''''''''''''''''''''''''

The computations performed by these transformations can take an
arbitrarily large number of steps, or even not terminate. For this
reason, the number of steps is bounded by a maximal value, which is set
by default to 1000. This value can be increased by another meta,

::

    meta "compute_max_steps" 1_000_000

When this upper limit is reached, a warning is issued, and the
partly-reduced goal is returned as the result of the transformation.

Other Non-Splitting Transformations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

eliminate\_algebraic
    replaces algebraic data types by first-order
    definitions :raw-latex:`\cite{paskevich09rr}`.

eliminate\_builtin
    removes definitions of symbols that are declared as builtin in the
    driver, with a “syntax” rule.

eliminate\_definition\_func
    replaces all function definitions with axioms.

eliminate\_definition\_pred
    replaces all predicate definitions with axioms.

eliminate\_definition
    applies both transformations above.

eliminate\_mutual\_recursion
    replaces mutually recursive definitions with axioms.

eliminate\_recursion
    replaces all recursive definitions with axioms.

eliminate\_if\_term
    replaces terms of the form ``if formula then t2 else t3`` by lifting
    them at the level of formulas. This may introduce ``if then else``
    in formulas.

eliminate\_if\_fmla
    replaces formulas of the form ``if f1 then f2 else f3`` by an
    equivalent formula using implications and other connectives.

eliminate\_if
    applies both transformations above.

eliminate\_inductive
    replaces inductive predicates by (incomplete) axiomatic definitions,
    construction axioms and an inversion axiom.

eliminate\_let\_fmla
    eliminates ``let`` by substitution, at the predicate level.

eliminate\_let\_term
    eliminates ``let`` by substitution, at the term level.

eliminate\_let
    applies both transformations above.

encoding\_smt
    encodes polymorphic types into monomorphic
    types :raw-latex:`\cite{conchon08smt}`.

encoding\_tptp
    encodes theories into unsorted logic.

introduce\_premises
    moves antecedents of implications and universal quantifications of
    the goal into the premises of the task.

simplify\_array
    automatically rewrites the task using the lemma ``Select_eq`` of
    theory ``map.Map``.

simplify\_formula
    reduces trivial equalities :math:`t=t` to true and then simplifies
    propositional structure: removes true, false, simplifies
    :math:`f \land f` to :math:`f`, etc.

simplify\_recursive\_definition
    reduces mutually recursive definitions if they are not really
    mutually recursive,

    ::

        function f : ... = ... g ...
        with g : ... = e

    becomes

    ::

        function g : ... = e
        function f : ... = ... g ...

    if :math:`f` does not occur in :math:`e`.

simplify\_trivial\_quantification
    simplifies quantifications of the form

    ::

        forall x, x = t -> P(x)

    into

    ::

        P(t)

    when :math:`x` does not occur in :math:`t`. More generally, this
    simplification is applied whenever :math:`x=t` or :math:`t=x`
    appears in negative position.

simplify\_trivial\_quantification\_in\_goal
    is the same as above but it applies only in the goal.

split\_premise
    replaces axioms in conjunctive form by an equivalent collection of
    axioms. In absence of case analysis attributes (see ``split_goal``
    for details), the number of axiom generated per initial axiom is
    linear in the size of that initial axiom.

split\_premise\_full
    is similar to ``split_premise``, but it also converts the axioms to
    conjunctive normal form. The number of axioms generated per initial
    axiom may be exponential in the size of the initial axiom.

Other Splitting Transformations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

simplify\_formula\_and\_task
    is the same as ``simplify_formula`` but it also removes the goal if
    it is equivalent to true.

split\_goal
    changes conjunctive goals into the corresponding set of subgoals. In
    absence of case analysis attributes, the number of subgoals
    generated is linear in the size of the initial goal.

    .. rubric:: Behavior on asymmetric connectives and ``by``/``so``
       :name: behavior-on-asymmetric-connectives-and-byso

    The transformation treats specially asymmetric and ``by``/``so``
    connectives. Asymmetric conjunction ``A && B`` in goal position is
    handled as syntactic sugar for ``A /\ (A -> B)``. The conclusion of
    the first subgoal can then be used to prove the second one.

    Asymmetric disjunction ``A || B`` in hypothesis position is handled
    as syntactic sugar for ``A \/ ((not A) /\ B)``. In particular, a
    case analysis on such hypothesis would give the negation of the
    first hypothesis in the second case.

    The ``by`` connective is treated as a proof indication. In
    hypothesis position, ``A by B`` is treated as if it were syntactic
    sugar for its regular interpretation ``A``. In goal position, it is
    treated as if ``B`` was an intermediate step for proving ``A``.
    ``A by B`` is then replaced by ``B`` and the transformation also
    generates a side-condition subgoal ``B -> A`` representing the
    logical cut.

    Although splitting stops at disjunctive points like symmetric
    disjunction and left-hand sides of implications, the occurrences of
    the ``by`` connective are not restricted. For instance:

    -  Splitting

       ::

           goal G : (A by B) && C

       generates the subgoals

       ::

           goal G1 : B
           goal G2 : A -> C
           goal G3 : B -> A (* side-condition *)

    -  Splitting

       ::

           goal G : (A by B) \/ (C by D)

       generates

       ::

           goal G1 : B \/ D
           goal G2 : B -> A (* side-condition *)
           goal G3 : D -> C (* side-condition *)

    -  Splitting

       ::

           goal G : (A by B) || (C by D)

       generates

       ::

           goal G1 : B || D
           goal G2 : B -> A        (* side-condition *)
           goal G3 : B || (D -> C) (* side-condition *)

       Note that due to the asymmetric disjunction, the disjunction is
       kept in the second side-condition subgoal.

    -  Splitting

       ::

           goal G : exists x. P x by x = 42

       generates

       ::

           goal G1 : exists x. x = 42
           goal G2 : forall x. x = 42 -> P x (* side-condition *)

       Note that in the side-condition subgoal, the context is
       universally closed.

    The ``so`` connective plays a similar role in hypothesis position,
    as it serves as a consequence indication. In goal position,
    ``A so B`` is treated as if it were syntactic sugar for its regular
    interpretation ``A``. In hypothesis position, it is treated as if
    both ``A`` and ``B`` were true because ``B`` is a consequence of
    ``A``. ``A so B`` is replaced by ``A /\ B`` and the transformation
    also generates a side-condition subgoal ``A -> B`` corresponding to
    the consequence relation between formula.

    As with the ``by`` connective, occurrences of ``so`` are
    unrestricted. For instance:

    -  Splitting

       ::

           goal G : (((A so B) \/ C) -> D) && E

       generates

       ::

           goal G1 : ((A /\ B) \/ C) -> D
           goal G2 : (A \/ C -> D) -> E
           goal G3 : A -> B               (* side-condition *)

    -  Splitting

       ::

           goal G : A by exists x. P x so Q x so R x by T x
           (* reads: A by (exists x. P x so (Q x so (R x by T x))) *)

       generates

       ::

           goal G1 : exists x. P x
           goal G2 : forall x. P x -> Q x               (* side-condition *)
           goal G3 : forall x. P x -> Q x -> T x        (* side-condition *)
           goal G4 : forall x. P x -> Q x -> T x -> R x (* side-condition *)
           goal G5 : (exists x. P x /\ Q x /\ R x) -> A (* side-condition *)

       In natural language, this corresponds to the following proof
       scheme for ``A``: There exists a ``x`` for which ``P`` holds.
       Then, for that witness ``Q`` and ``R`` also holds. The last one
       holds because ``T`` holds as well. And from those three
       conditions on ``x``, we can deduce ``A``.

    .. rubric:: Attributes controlling the transformation
       :name: attributes-controlling-the-transformation

    The transformations in the split family can be controlled by using
    attributes on formulas.

    The ``[@stop_split]`` attribute can be used to block the splitting
    of a formula. The attribute is removed after blocking, so applying
    the transformation a second time will split the formula. This is can
    be used to decompose the splitting process in several steps. Also,
    if a formula with this attribute is found in non-goal position, its
    ``by``/``so`` proof indication will be erased by the transformation.
    In a sense, formulas tagged by ``[@stop_split]`` are handled as if
    they were local lemmas.

    The ``[@case_split]`` attribute can be used to force case analysis
    on hypotheses. For instance, applying ``split_goal`` on

    ::

        goal G : ([@case_split] A \/ B) -> C

    generates the subgoals

    ::

        goal G1 : A -> C
        goal G2 : B -> C

    Without the attribute, the transformation does nothing because
    undesired case analysis may easily lead to an exponential blow-up.

    Note that the precise behavior of splitting transformations in
    presence of the ``[@case_split]`` attribute is not yet specified and
    is likely to change in future versions.

split\_all
    performs both ``split_premise`` and ``split_goal``.

split\_intro
    performs both ``split_goal`` and ``introduce_premises``.

split\_goal\_full
    has a behavior similar to ``split_goal``, but also converts the goal
    to conjunctive normal form. The number of subgoals generated may be
    exponential in the size of the initial goal.

split\_all\_full
    performs both ``split_premise`` and ``split_goal_full``.

.. _sec.strategies:

Proof Strategies
----------------

As seen in :numref:`sec.ideref`, the IDE provides a few buttons that
trigger the run of simple proof strategies on the selected goals. Proof
strategies can be defined using a basic assembly-style language, and put
into the Why3 configuration file. The commands of this basic language
are:

-  ``c p t m`` calls the prover :math:`p` with a time limit :math:`t`
   and memory limit :math:`m`. On success, the strategy ends, it
   continues to next line otherwise

-  ``t n lab`` applies the transformation :math:`n`. On success, the
   strategy continues to label :math:`lab`, and is applied to each
   generated sub-goals. It continues to next line otherwise.

-  ``g lab`` inconditionally jumps to label :math:`lab`

-  ``lab:`` declares the label :math:`lab`. The default label ``exit``
   allows to stop the program.

To examplify this basic programming language, we give below the default
strategies that are attached to the default buttons of the IDE, assuming
that the provers Alt-Ergo 1.30, CVC4 1.5 and Z3 4.5.0 were detected by
the ``why3 config --detect`` command

Split
    is bound to the 1-line strategy

    ::

        t split_goal_wp exit

Auto level 0
    is bound to

    ::

        c Z3,4.5.0, 1 1000
        c Alt-Ergo,1.30, 1 1000
        c CVC4,1.5, 1 1000

    The three provers are tried for a time limit of 1 second and memory
    limit of 1 Gb, each in turn. This is a perfect strategy for a first
    attempt to discharge a new goal.

Auto level 1
    is bound to

    ::

        start:
        c Z3,4.5.0, 1 1000
        c Alt-Ergo,1.30, 1 1000
        c CVC4,1.5, 1 1000
        t split_goal_wp start
        c Z3,4.5.0, 10 4000
        c Alt-Ergo,1.30, 10 4000
        c CVC4,1.5, 10 4000

    The three provers are first tried for a time limit of 1 second and
    memory limit of 1 Gb, each in turn. If none of them succeed, a split
    is attempted. If the split works then the same strategy is retried
    on each sub-goals. If the split does not succeed, the provers are
    tried again with a larger limits.

Auto level 2
    is bound to

    ::

        start:
        c Z3,4.5.0, 1 1000
        c Eprover,2.0, 1 1000
        c Spass,3.7, 1 1000
        c Alt-Ergo,1.30, 1 1000
        c CVC4,1.5, 1 1000
        t split_goal_wp start
        c Z3,4.5.0, 5 2000
        c Eprover,2.0, 5 2000
        c Spass,3.7, 5 2000
        c Alt-Ergo,1.30, 5 2000
        c CVC4,1.5, 5 2000
        t introduce_premises afterintro
        afterintro:
        t inline_goal afterinline
        g trylongertime
        afterinline:
        t split_goal_wp start
        trylongertime:
        c Z3,4.5.0, 30 4000
        c Eprover,2.0, 30 4000
        c Spass,3.7, 30 4000
        c Alt-Ergo,1.30, 30 4000
        c CVC4,1.5, 30 4000

    Notice that now 5 provers are used. The provers are first tried for
    a time limit of 1 second and memory limit of 1 Gb, each in turn. If
    none of them succeed, a split is attempted. If the split works then
    the same strategy is retried on each sub-goals. If the split does
    not succeed, the prover are tried again with limits of 5 s and 2 Gb.
    If all fail, we attempt the transformation of introduction of
    premises in the context, followed by an inlining of the definitions
    in the goals. We then attempt a split again, if the split succeeds,
    we restart from the beginning, if it fails then provers are tried
    again with 30s and 4 Gb.
