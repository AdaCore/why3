Technical Informations
======================

Structure of Session Files
--------------------------

The proof session state is stored in an XML file named
:file:`{dir}/why3session.xml`, where *dir* is the directory of the
project. The XML file follows the DTD given in :file:`share/why3session.dtd`
and reproduced below.

.. literalinclude:: ../share/why3session.dtd
   :language: dtd

.. _sec.proverdetectiondata:

Prover Detection
----------------

The data configuration for the automatic detection of installed provers
is stored in the file :file:`provers-detection-data.conf` typically located
in directory :file:`/usr/local/share/why3` after installation.

.. _sec.whyconffile:

The :file:`why3.conf` Configuration File
----------------------------------------

One can use a custom configuration file. The Why3 tools look for it in
the following order:

#. the file specified by the :option:`why3 --config` option,

#. the file specified by the environment variable :envvar:`WHY3CONFIG` if set,

#. the file :file:`$HOME/.why3.conf` (:file:`$USERPROFILE/.why3.conf` under
   Windows) or, in the case of local installation, :file:`why3.conf` in the
   top directory of Why3 sources.

If none of these files exist, a built-in default configuration is used.

A section begins with a header inside square brackets and ends at the
beginning of the next section. The header of a section can be a single
identifier, e.g., ``[main]``, or it can be composed by a family name and a
single family argument, e.g., ``[prover alt-ergo]``.

Sections contain associations ``key=value``. A value is either an
integer (e.g., ``-555``), a boolean (``true``, ``false``), or a string
(e.g., ``"emacs"``). Some specific keys can be attributed multiple values and
are thus allowed to occur several times inside a given section. In that
case, the relative order of these associations matters.

.. _sec.drivers:

Drivers for External Provers
----------------------------

Drivers for external provers are readable files from directory
``drivers``. They describe how Why3 should interact
with external provers.

Files with :file:`.drv` extension represent drivers that might be
associated to a specific solver in the :file:`why3.conf`
configuration file (see :numref:`sec.whyconffile` for more information);
files with :file:`.gen` extension are intended to be imported by
other drivers; finally, files with :file:`.aux` extension are
automatically generated from the main :file:`Makefile`.

.. graphviz:: generated/drivers-smt.dot
   :caption: Driver dependencies for SMT solvers
   :name: fig.drv.smt

.. graphviz:: generated/drivers-tptp.dot
   :caption: Driver dependencies for TPTP solvers
   :name: fig.drv.tptp

.. graphviz:: generated/drivers-coq.dot
   :caption: Driver dependencies for Coq
   :name: fig.drv.coq

.. graphviz:: generated/drivers-isabelle.dot
   :caption: Driver dependencies for Isabelle/HOL
   :name: fig.drv.isabelle

.. graphviz:: generated/drivers-pvs.dot
   :caption: Driver dependencies for PVS
   :name: fig.drv.pvs

The most important drivers dependencies are shown in the following
figures: :numref:`fig.drv.smt` shows the drivers files for SMT
solvers, :numref:`fig.drv.tptp` for TPTP solvers, :numref:`fig.drv.coq`
for Coq, :numref:`fig.drv.isabelle` for Isabelle/HOL,
and :numref:`fig.drv.pvs` for PVS.

.. _sec.transformations:

Transformations
---------------

This section documents the available transformations. Note that the set
of available transformations in your own installation is given
by :option:`why3 --list-transforms`.

.. why3:transform:: apply

   Apply an hypothesis to the goal of the task using a *modus ponens*
   rule. The hypothesis should be an implication whose conclusion can be
   matched with the goal. The intuitive behavior
   of :why3:transform:`apply` can be translated as follows.
   Given :math:`\Gamma, h: f_1 \rightarrow f_2 \vdash G: f_2`, ``apply h``
   generates a new task :math:`\Gamma, h: f_1 \rightarrow f_2 \vdash G: f_1`.

   In practice, the transformation also manages to instantiate some variables
   with the appropriate terms.

   For example, applying the transformation ``apply zero_is_even`` on the
   following goal

   .. code-block:: whyml

      predicate is_even int
      predicate is_zero int
      axiom zero_is_even: forall x: int. is_zero x -> is_even x
      goal G: is_even 0

   produces the following goal:

   .. code-block:: whyml

      predicate is_even int
      predicate is_zero int
      axiom zero_is_even: forall x:int. is_zero x -> is_even x
      goal G: is_zero 0

   The transformation first matched the goal against the hypothesis and
   instantiated ``x`` with ``0``. It then applied the *modus ponens* rule
   to generate the new goal.

   This transformation helps automated provers when they do not know
   which hypothesis to use in order to prove a goal.

.. why3:transform:: apply with

   Variant of :why3:transform:`apply` intended to be used in contexts
   where the latter cannot infer what terms to use for variables given in
   the applied hypothesis.

   For example, applying the transformation ``apply transitivity`` on the
   following goal

   .. code-block:: whyml

      axiom ac: a = c
      axiom cb: c = b
      axiom transitivity : forall x y z:int. x = y -> y = z -> x = z
      goal G1 : a = b

   raises the following error:

   ::

      apply: Unable to infer arguments (try using "with") for: y

   It means that the tool is not able to infer the right term to
   instantiate symbol ``y``. In our case, the user knows that the term
   ``c`` should work. So, it can be specified as follows:
   ``apply transitivity with c``

   This generates two goals which are easily provable with hypotheses
   ``ac`` and ``cb``.

   When multiple variables are needed, they should be provided as a list
   in the transformation. For the sake of the example, we complicate
   the ``transitivity`` hypothesis:

   .. code-block:: whyml

      axiom t : forall x y z k:int. k = k -> x = y -> y = z -> x = z

   A value can be provided for ``k`` as follows: ``apply t with c,0``.

.. why3:transform:: assert

   Create an intermediate subgoal. This is comparable to ``assert``
   written in WhyML code. Here, the intent is only to help provers by
   specifying one key argument of the reasoning they should use.

   Example: From a goal of the form :math:`\Gamma \vdash G`, the
   transformation ``assert (n = 0)`` produces the following two
   tasks: :math:`\Gamma \vdash h: n = 0` and :math:`\Gamma, h: n =
   0 \vdash G`. This effectively adds ``h`` as an intermediate goal to prove.

.. why3:transform:: assert as

   Same as :why3:transform:`assert`, except that a name can be given to
   the new hypothesis. Example: ``assert (x = 0) as x0``.

.. why3:transform:: case

   Split a goal into two subgoal, using the *excluded middle* on a given
   formula. On the task :math:`\Gamma \vdash G`, the transformation
   ``case f`` produces two tasks: :math:`\Gamma, h: f \vdash G` and
   :math:`\Gamma, h: \neg f \vdash G`.

   For example, applying ``case (x = 0)`` on the following goals

   .. code-block:: whyml

      constant x : int
      constant y : int
      goal G: if x = 0 then y = 2 else y = 3

   produces the following goals:

   .. code-block:: whyml

      constant x : int
      constant y : int
      axiom h : x = 0
      goal G : if x = 0 then y = 2 else y = 3

   .. code-block:: whyml

      constant x : int
      constant y : int
      axiom h : not x = 0
      goal G : if x = 0 then y = 2 else y = 3

   The intent is again to simplify the job of automated provers by giving
   them a key argument of the reasoning behind the proof of a subgoal.

.. why3:transform:: case as

   Same as :why3:transform:`case`, except that a name can be given to
   the new hypothesis. Example: ``case (x = 0) as x0``.

.. why3:transform:: clear_but

   Remove all the hypotheses except those specified in the arguments.
   This is useful when a prover fails to find relevant hypotheses in
   a very large context. Example: ``clear_but h23,h25``.

.. why3:transform:: compute_hyp

   Apply the transformation :why3:transform:`compute_in_goal` on the given
   hypothesis.

.. why3:transform:: compute_hyp_specified

   Apply the transformation :why3:transform:`compute_specified` on the
   given hypothesis.

.. why3:transform:: compute_in_goal

   Aggressively apply all known computation/simplification rules.

   The kinds of simplification are as follows.

   -  Computations with built-in symbols, e.g., operations on integers, when
      applied to explicit constants, are evaluated. This includes
      evaluation of equality when a decision can be made (on integer
      constants, on constructors of algebraic data types), Boolean
      evaluation, simplification of pattern-matching/conditional
      expression, extraction of record fields, and beta-reduction. At best,
      these computations reduce the goal to ``true`` and the
      transformations thus does not produce any sub-goal. For example, a
      goal like ``6*7=42`` is solved by those transformations.

   -  Unfolding of definitions, as done by :why3:transform:`inline_goal`. Transformation
      :why3:transform:`compute_in_goal` unfolds all definitions, including recursive
      ones. For :why3:transform:`compute_specified`, the user can enable unfolding of a
      specific logic symbol by attaching the meta :why3:meta:`rewrite_def` to the
      symbol.

      .. code-block:: whyml

         function sqr (x:int) : int = x * x
         meta "rewrite_def" function sqr

   -  Rewriting using axioms or lemmas declared as rewrite rules. When an
      axiom (or a lemma) has one of the forms

      .. code-block:: whyml

         axiom a: forall ... t1 = t2

      or

      .. code-block:: whyml

         axiom a: forall ... f1 <-> f2

      then the user can declare

      .. code-block:: whyml

         meta "rewrite" prop a

      to turn this axiom into a rewrite rule. Rewriting is always done from
      left to right. Beware that there is no check for termination nor for
      confluence of the set of rewrite rules declared.

   Instead of using a meta, it is possible to declare an axiom as a rewrite
   rule by adding the :why3:attribute:`[@rewrite]` attribute on the axiom name or on the
   axiom itself, e.g.,

   .. code-block:: whyml

       axiom a [@rewrite]: forall ... t1 = t2
       lemma b: [@rewrite] forall ... f1 <-> f2

   The second form allows some form of local rewriting, e.g.,

   .. code-block:: whyml

       lemma l: forall x y. ([@rewrite] x = y) -> f x = f y

   can be proved by :why3:transform:`introduce_premises` followed by
   :why3:transform:`compute_specified`.

   The computations performed by this transformation can take an
   arbitrarily large number of steps, or even not terminate. For this
   reason, the number of steps is bounded by a maximal value, which is set
   by default to 1000. This value can be increased by another meta, e.g.,

   .. code-block:: whyml

       meta "compute_max_steps" 1_000_000

   When this upper limit is reached, a warning is issued, and the
   partly-reduced goal is returned as the result of the transformation.

.. why3:transform:: compute_specified

   Same as :why3:transform:`compute_in_goal`, but perform rewriting using
   only built-in operators and user-provided rules.

.. why3:transform:: cut

   Same as :why3:transform:`assert`, but the order of generated subgoals
   is reversed.

.. why3:transform:: destruct

   Eliminate the head symbol of a hypothesis.

   For example, applying ``destruct h`` on the following goal

   .. code-block:: whyml

      constant p1 : bool
      predicate p2 int
      axiom h : p1 = True /\ (forall x:int. p2 x)
      goal G : p2 0

   removes the logical connective ``/\`` and produces

   .. code-block:: whyml

      constant p1 : bool
      predicate p2 int
      axiom h1 : p1 = True
      axiom h : forall x:int. p2 x
      goal G : p2 0

   :why3:transform:`destruct` can be applied on the following constructions:

   - ``false``, ``true``,
   - ``/\``, ``\/``, ``->``, ``not``,
   - ``exists``,
   - ``if ... then ... else ...``,
   - ``match ... with ... end``,
   - (in)equality on constructors of the same type.

.. why3:transform:: destruct_rec

   Recursively call :why3:transform:`destruct` on the generated
   hypotheses. The recursion on implication and ``match`` stops after the
   first occurence of a different symbol.

   For example, applying ``destruct_rec H`` on the following goal

   .. code-block:: whyml

      predicate a
      predicate b
      predicate c
      axiom H : (a -> b) /\ (b /\ c)
      goal G : false

   does not destruct the implication symbol because it occurs as
   a subterm of an already destructed symbol. This restriction applies
   only to implication and ``match`` Other symbols are destructed
   recursively. Thus, in the generated task, the second ``/\`` is
   simplified:

   .. code-block:: whyml

      predicate a
      predicate b
      predicate c
      axiom H2 : a -> b
      axiom H1 : b
      axiom H: c
      goal G : false

.. why3:transform:: destruct_term

   Destruct an expression according to the type of the expression. The
   transformation produces all possible outcomes of a destruction of the
   algebraic type.

   For example, applying ``destruct_term a`` on the following goal

   .. code-block:: whyml

      type t = A | B int
      constant a : t
      goal G : a = A

   produces the following two goals:

   .. code-block:: whyml

      type t = A | B int
      constant a : t
      constant x : int
      axiom h : a = B x
      goal G : a = A

   .. code-block:: whyml

      type t = A | B int
      constant a : t
      axiom h : a = A
      goal G : a = A

   The term was destructed according to all the possible outcomes in the
   type. Note that, during destruction, a new constant ``x`` has been
   introduced for the argument of constructor ``B``.

.. why3:transform:: destruct_term using

   Same as :why3:transform:`destruct_term`, except that names can be given to
   the constants that were generated.

.. why3:transform:: destruct_term_subst

   Same as :why3:transform:`destruct_term`, except that it also
   substitutes the created term.

.. why3:transform:: eliminate_algebraic

   Replace algebraic data types by first-order definitions :cite:`paskevich09rr`.

.. why3:transform:: eliminate_builtin

   Remove definitions of symbols that are declared as builtin in the
   driver, with a “syntax” rule.

.. why3:transform:: eliminate_definition_func

   Replace all function definitions with axioms.

.. why3:transform:: eliminate_definition_pred

   Replace all predicate definitions with axioms.

.. why3:transform:: eliminate_definition

   Apply both :why3:transform:`eliminate_definition_func` and
   :why3:transform:`eliminate_definition_pred`.

.. why3:transform:: eliminate_if

   Apply both :why3:transform:`eliminate_if_term` and :why3:transform:`eliminate_if_fmla`.

.. why3:transform:: eliminate_if_fmla

   Replace formulas of the form ``if f1 then f2 else f3`` by an
   equivalent formula using implications and other connectives.

.. why3:transform:: eliminate_if_term

   Replace terms of the form ``if formula then t2 else t3`` by lifting
   them at the level of formulas. This may introduce ``if then else``
   in formulas.

.. why3:transform:: eliminate_inductive

   Replace inductive predicates by (incomplete) axiomatic definitions,
   construction axioms and an inversion axiom.

.. why3:transform:: eliminate_let

   Apply both :why3:transform:`eliminate_let_fmla` and :why3:transform:`eliminate_let_term`.

.. why3:transform:: eliminate_let_fmla

   Eliminate ``let`` by substitution, at the predicate level.

.. why3:transform:: eliminate_let_term

   Eliminate ``let`` by substitution, at the term level.

.. why3:transform:: eliminate_literal

.. why3:transform:: eliminate_mutual_recursion

   Replace mutually recursive definitions with axioms.

.. why3:transform:: eliminate_recursion

   Replace all recursive definitions with axioms.

.. why3:transform:: encoding_smt

   Encode polymorphic types into monomorphic types :cite:`conchon08smt`.

.. why3:transform:: encoding_tptp

   Encode theories into unsorted logic.

.. why3:transform:: exists

   Instantiate an existential quantification with a witness.

   For example, applying ``exists 0`` on the following goal

   .. code-block:: whyml

      goal G : exists x:int. x = 0

   instantiates the symbol ``x`` with ``0``. Thus, the goal becomes

   .. code-block:: whyml

      goal G : 0 = 0

.. why3:transform:: hide

   Hide a given term, by creating a new constant equal to the term and
   then replacing all occurences of the term in the context by this
   constant.

   For example, applying ``hide t (1 + 1)`` on the goal

   .. code-block:: whyml

      constant y : int
      axiom h : forall x:int. x = (1 + 1)
      goal G : (y - (1 + 1)) = ((1 + 1) - (1 + 1))

   replaces all the occurrences of ``(1 + 1)`` with ``t``, which gives
   the following goal:

   .. code-block:: whyml

      constant y : int
      constant t : int
      axiom H : t = (1 + 1)
      axiom h : forall x:int. x = t
      goal G : (y - t) = (t - t)

.. why3:transform:: hide_and_clear

   First apply :why3:transform:`hide` and then remove the equality
   between the hidden term and the introduced constant. This means that
   the hidden term completely disappears and cannot be recovered.

.. why3:transform:: induction

   Perform a reasoning by induction for the current goal.

   For example, applying ``induction n`` on the following goal

   .. code-block:: whyml

      constant n : int
      predicate p int
      predicate p1 int
      axiom h : p1 n
      goal G : p n

   performs an induction on ``n`` starting at ``0``. The goal for the
   base case is

   .. code-block:: whyml

      constant n : int
      predicate p int
      predicate p1 int
      axiom h : p1 n
      axiom Init : n <= 0
      goal G : p n

   while the recursive case is

   .. code-block:: whyml

      constant n : int
      predicate p int
      predicate p1 int
      axiom h : p1 n
      axiom Init : 0 < n
      axiom Hrec : forall n1:int. n1 < n -> p1 n1 -> p n1
      goal G : p n

.. why3:transform:: induction from

   Same as :why3:transform:`induction`, but it starts the induction from
   a given integer instead of ``0``.

.. why3:transform:: induction_arg_pr

   Apply :why3:transform:`induction_pr` on the given hypothesis/goal symbol.

.. why3:transform:: induction_arg_ty_lex

   Apply :why3:transform:`induction_ty_lex` on the given symbol.

.. why3:transform:: induction_pr

.. why3:transform:: induction_ty_lex

    Perform structural, lexicographic induction on goals involving
    universally quantified variables of algebraic data types, such as
    lists, trees, etc. For instance, it transforms the following goal

    .. code-block:: whyml

        goal G: forall l: list 'a. length l >= 0

    into this one:

    .. code-block:: whyml

        goal G :
          forall l:list 'a.
             match l with
             | Nil -> length l >= 0
             | Cons a l1 -> length l1 >= 0 -> length l >= 0
             end

    When induction can be applied to several variables, the
    transformation picks one heuristically. The :why3:attribute:`[@induction]`
    attribute can be used to force induction over one particular
    variable, with

    .. code-block:: whyml

        goal G: forall l1 [@induction] l2 l3: list 'a.
                l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3

    induction will be applied on ``l1``. If this attribute is attached
    to several variables, a lexicographic induction is performed on
    these variables, from left to right.

.. why3:transform:: inline_trivial

    Expand and remove definitions of the form

    .. code-block:: whyml

        function  f x1 ... xn = g e1 ... ek
        predicate p x1 ... xn = q e1 ... ek

    when each :samp:`e{i}` is either a ground term or one of the
    :samp:`x{j}`, and each ``x1 ... xn`` occurs at most once in
    all the :samp:`e{i}`.

    The attribute :why3:attribute:`[@inline:trivial]` can be used to tag functions, so
    that the transformation forcefully expands them (not using the
    conditions above). This can be used to ensure that some specific
    functions are inlined for automatic provers
    (:why3:transform:`inline_trivial` is used in many drivers).

.. why3:transform:: inline_goal

   Expand all outermost symbols of the goal that have a non-recursive
   definition.

.. why3:transform:: inline_all

   Expand all non-recursive definitions.

.. why3:transform:: instantiate

   Generate a new hypothesis with quantified variables
   replaced by the given terms.

   For example, applying ``instantiate h 0, 1`` on the following goal

   .. code-block:: whyml

      predicate p int
      axiom h : forall x:int, y:int. x <= y -> p x /\ p y
      goal G : p 0

   generates a new hypothesis:

   .. code-block:: whyml

      predicate p int
      axiom h : forall x:int, y:int. x <= y -> p x /\ p y
      axiom Hinst : 0 <= 1 -> p 0 /\ p 1
      goal G : p 0

   This is used to help automatic provers that are generally better at
   working on instantiated hypothesis.

.. why3:transform:: inst_rem

   Apply :why3:transform:`instantiate` then remove the original
   instantiated hypothesis.

.. why3:transform:: introduce_premises

   Move antecedents of implications and universal quantifications of
   the goal into the premises of the task.

.. why3:transform:: intros

   Introduce universal quantifiers in the context.

   For example, applying ``intros n, m`` on the following goal

   .. code-block:: whyml

      predicate p int int int
      goal G : forall x:int, y:int, z:int. p x y z

   produces the following goal:

   .. code-block:: whyml

      predicate p int int int
      constant n : int
      constant m : int
      goal G : forall z:int. p n m z

.. why3:transform:: intros_n

   Same as :why3:transform:`intros`, but stops after the nth quantified
   variable or premise.

   For example, applying ``intros_n 2`` on the following goal

   .. code-block:: whyml

      predicate p int int int
      goal G : forall x:int, y:int, z:int. p x y z

   produces the following goal:

   .. code-block:: whyml

      predicate p int int int
      constant x : int
      constant y : int
      goal G : forall z:int. p x y z

.. why3:transform:: inversion_arg_pr

   Apply :why3:transform:`inversion_pr` on the given hypothesis/goal symbol.

.. why3:transform:: inversion_pr

.. why3:transform:: left

   Remove the right part of the head disjunction of the goal.

   For example, applying ``left`` on the following goal

   .. code-block:: whyml

      constant x : int
      goal G : x = 0 \/ x = 1

   produces the following goal:

   .. code-block:: whyml

      constant x : int
      goal G : x = 0

.. why3:transform:: pose

   Add a new constant equal to the given term.

   For example, applying ``pose t (x + 2)`` to the following goal

   .. code-block:: whyml

      constant x : int
      goal G : true

   produces the following goal:

   .. code-block:: whyml

      constant x : int
      constant t : int
      axiom H : t = (x + 2)
      goal G : true

.. why3:transform:: remove

   Remove a hypothesis from the context.

   For example, applying ``remove h`` on the following goal

   .. code-block:: whyml

      axiom h : true
      goal G : true

   produces the following goal:

   .. code-block:: whyml

      goal G : true

.. why3:transform:: replace

   Replace a term with another one in a hypothesis or in the goal. This
   generates a new goal which asks for the proof of the equality.

   For example, applying ``replace (y + 1) (x + 2) in h`` on the
   following goal

   .. code-block:: whyml

      constant x : int
      constant y : int
      axiom h : x >= (y + 1)
      goal G : true

   produces the following two goals:

   .. code-block:: whyml

      constant x : int
      constant y : int
      axiom h : x >= (x + 2)
      goal G : true

   .. code-block:: whyml

      constant x : int
      constant y : int
      axiom h : x >= (y + 1)
      goal G : (y + 1) = (x + 2)

   It can be seen as the combination of :why3:transform:`assert`
   and :why3:transform:`rewrite`.

.. why3:transform:: revert

   Opposite of :why3:transform:`intros`. It takes hypotheses/constants
   and quantifies them in the goal.

   For example, applying ``revert x`` on the following goal

   .. code-block:: whyml

      constant x : int
      constant y : int
      axiom h : x = y
      goal G : true

   produces the following goal:

   .. code-block:: whyml

      constant y : int
      goal G : forall x:int. x = y -> true

.. why3:transform:: rewrite

   Rewrite using the given equality hypothesis.

   For example, applying ``rewrite eq`` on the following goal

   .. code-block:: whyml

      function a int : bool
      function b int : bool
      constant y : int
      axiom eq : forall x:int. not x = 0 -> a x = b x
      goal G : a y = True

   produces the following goal:

   .. code-block:: whyml

      function a int : bool
      function b int : bool
      constant y : int
      axiom eq : forall x:int. not x = 0 -> a x = b x
      goal G : b y = True

   It also produces a goal for the premise of the equality hypothesis (as
   would :why3:transform:`apply`):

   .. code-block:: whyml

      function a int : bool
      function b int : bool
      constant y : int
      axiom eq : forall x:int. not x = 0 -> a x = b x
      goal G : not y = 0

.. why3:transform:: rewrite with

   Variant of :why3:transform:`rewrite` intended to be used in contexts
   where the latter cannot infer what terms to use for the variables of
   the given hypotheses (see also :why3:transform:`apply with`).

   For example, the transformation ``rewrite eq with 0`` can be applied
   to the following goal:

   .. code-block:: whyml

      function a int : bool
      function b int : bool
      constant y : int
      axiom eq : forall x:int, z:int. z = 0 -> not x = 0 -> a x = b x
      goal G : a y = True

   Here, a value is provided for the symbol ``z``. This leads to the
   following three goals. One is the rewritten one, while the other two
   are for the premises of the equality hypothesis.

   .. code-block:: whyml

      function a int : bool
      function b int : bool
      constant y : int
      axiom eq : forall x:int, z:int. z = 0 -> not x = 0 -> a x = b x
      goal G : b y = True

   .. code-block:: whyml

      function a int : bool
      function b int : bool
      constant y : int
      axiom eq : forall x:int, z:int. z = 0 -> not x = 0 -> a x = b x
      goal G : 0 = 0

   .. code-block:: whyml

      function a int : bool
      function b int : bool
      constant y : int
      axiom eq : forall x:int, z:int. z = 0 -> not x = 0 -> a x = b x
      goal G : not y = 0

.. why3:transform:: rewrite_list

   Variant of :why3:transform:`rewrite` that allows simultaneous rewriting in
   a list of hypothesis/goals.

.. why3:transform:: right

   Remove the left part of the head disjunction of the goal.

   For example, applying ``right`` on the following goal

   .. code-block:: whyml

      constant x : int
      goal G : x = 0 \/ x = 1

   produces the following goal:

   .. code-block:: whyml

      constant x : int
      goal G : x = 1

.. why3:transform:: simplify_array

   Automatically rewrite the task using the lemma ``Select_eq`` of
   theory ``map.Map``.

.. why3:transform:: simplify_formula

   Reduce trivial equalities ``t=t`` to true and then simplify
   propositional structure: removes ``true``, ``false``, simplifies
   ``f /\ f`` to ``f``, etc.

.. why3:transform:: simplify_formula_and_task

   Apply :why3:transform:`simplify_formula` and remove the goal if
   it is equivalent to true.

.. why3:transform:: simplify_recursive_definition

    Reduce mutually recursive definitions if they are not really
    mutually recursive, e.g.,

    ::

        function f : ... = ... g ...
        with g : ... = e

    becomes

    ::

        function g : ... = e
        function f : ... = ... g ...

    if ``f`` does not occur in ``e``.

.. why3:transform:: simplify_trivial_quantification

    Simplify quantifications of the form

    ::

        forall x, x = t -> P(x)

    into

    ::

        P(t)

    when ``x`` does not occur in ``t``. More generally, this
    simplification is applied whenever ``x=t`` or ``t=x``
    appears in negative position.

.. why3:transform:: simplify_trivial_quantification_in_goal

   Apply :why3:transform:`simplify_trivial_quantification`, but only in the goal.

.. why3:transform:: split_all

   Perform both :why3:transform:`split_premise` and :why3:transform:`split_goal`.

.. why3:transform:: split_all_full

   Perform both :why3:transform:`split_premise` and :why3:transform:`split_goal_full`.

.. why3:transform:: split_goal

    Change conjunctive goals into the corresponding set of subgoals. In
    absence of case analysis attributes, the number of subgoals
    generated is linear in the size of the initial goal.

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
    unrestricted. Examples:

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

    The transformations in the “split” family can be controlled by using
    attributes on formulas.

    The :why3:attribute:`[@stop_split]` attribute can be used to block the splitting
    of a formula. The attribute is removed after blocking, so applying
    the transformation a second time will split the formula. This is can
    be used to decompose the splitting process in several steps. Also,
    if a formula with this attribute is found in non-goal position, its
    ``by``/``so`` proof indication will be erased by the transformation.
    In a sense, formulas tagged by :why3:attribute:`[@stop_split]` are handled as if
    they were local lemmas.

    The :why3:attribute:`[@case_split]` attribute can be used to force case analysis
    on hypotheses. For instance, applying :why3:transform:`split_goal` on

    ::

        goal G : ([@case_split] A \/ B) -> C

    generates the subgoals

    ::

        goal G1 : A -> C
        goal G2 : B -> C

    Without the attribute, the transformation does nothing because
    undesired case analysis may easily lead to an exponential blow-up.

    Note that the precise behavior of splitting transformations in
    presence of the :why3:attribute:`[@case_split]` attribute is not yet specified and
    is likely to change in future versions.

.. why3:transform:: split_goal_full

    Behave similarly to :why3:transform:`split_goal`, but also convert the goal
    to conjunctive normal form. The number of subgoals generated may be
    exponential in the size of the initial goal.

.. why3:transform:: split_intro

   Perform both :why3:transform:`split_goal` and :why3:transform:`introduce_premises`.

.. why3:transform:: split_premise

    Replace axioms in conjunctive form by an equivalent collection of
    axioms. In absence of case analysis attributes (see :why3:transform:`split_goal`
    for details), the number of axiom generated per initial axiom is
    linear in the size of that initial axiom.

.. why3:transform:: split_premise_full

    Behave similarly to :why3:transform:`split_premise`, but also convert the axioms to
    conjunctive normal form. The number of axioms generated per initial
    axiom may be exponential in the size of the initial axiom.

.. why3:transform:: subst

   Substitute a given constant using an equality found in the context.
   The constant is removed.

   For example, when applying ``subst x`` on the following goal

   .. code-block:: whyml

      constant x : int
      constant y : int
      constant z : int
      axiom h : x = y + 1
      axiom h1 : z = (x + y)
      goal G : x = z

   the transformation first finds the hypothesis ``h`` that can be used to
   rewrite ``x``. Then, it replaces every occurrences of ``x`` with ``y + 1``.
   Finally, it removes ``h`` and ``x``. The resulting goal is as follows:

   .. code-block:: whyml

      constant y : int
      constant z : int
      axiom h1 : z = ((y + 1) + y)
      goal G : (y + 1) = z

   This transformation is used to make the task more easily readable by
   a human during debugging. This transformation should not help
   automatic provers at all as they generally implement substitution
   rules in their logic.

.. why3:transform: subst_all

   Substitute all the variables that can be substituted.

   For example, applying ``subst_all`` on the following goal

   .. code-block:: whyml

      constant x : int
      constant x1 : int
      constant y : int
      constant z : int
      axiom h : x = (y + 1)
      axiom hx1 : x = x1
      axiom h1 : z = (x + y)
      goal G : x = z

   produces the following goal, where ``x``, ``x1``, and ``z`` have been
   removed:

   .. code-block:: whyml

      constant y : int
      goal G : (y + 1) = ((y + 1) + y)

   The order in which constants are substituted is not specified.

.. why3:transform:: unfold

   Unfold the definition of a logical symbol in the given hypothesis.

   For example, applying ``unfold p`` on the following goal

   .. code-block:: whyml

      predicate p (x:int) = x <= 22
      axiom h : forall x:int. p x -> p (x - 1)
      goal G : p 21

   produces the following goal:

   .. code-block:: whyml

      predicate p (x:int) = x <= 22
      axiom h : forall x:int. p x -> p (x - 1)
      goal G : 21 <= 22

   One can also unfold in the hypothesis, using ``unfold p in h``, which
   gives the following goal:

   .. code-block:: whyml

      predicate p (x:int) = x <= 22
      axiom h : forall x:int. x <= 22 -> (x - 1) <= 22
      goal G : 21 <= 22

.. why3:transform:: use_th

   Import a theory inside the current context. This is used, in some rare
   case, to reduced the size of the context in other goals, since
   importing a theory in the WhyML code would the theory available in all
   goals whereas the theory is only needed in one specific goal.

   For example, applying ``use_th int.Int`` on the following goal

   .. code-block:: whyml

      predicate p int
      goal G : p 5

   imports the ``Int`` theory. So, one is able to use the addition over
   integers, e.g., ``replace 5 (2 + 3)``.

   Any lemma appearing in the imported theory can also be used.

   Note that axioms are also imported. So, this transformation should be
   used with care. We recommend to use only theories that do not contain
   any axiom because this transformation could easily make the context
   inconsistent.

.. _sec.strategies:

Proof Strategies
----------------

As seen in :numref:`sec.ideref`, the IDE provides a few buttons that
trigger the run of simple proof strategies on the selected goals. Proof
strategies can be defined using a basic assembly-style language, and put
into the Why3 configuration file. The commands of this basic language
are:

-  :samp:`c {p} {t} {m}` calls the prover *p* with a time limit *t*
   and memory limit *m*. On success, the strategy ends, it
   continues to next line otherwise.

-  :samp:`t {n} {lab}` applies the transformation *n*. On success, the
   strategy continues to label *lab*, and is applied to each
   generated sub-goals. It continues to next line otherwise.

-  :samp:`g {lab}` unconditionally jumps to label *lab*.

-  :samp:`{lab}:` declares the label *lab*. The default label ``exit``
   stops the program.

To examplify this basic programming language, we give below the default
strategies that are attached to the default buttons of the IDE, assuming
that the provers Alt-Ergo 2.3.0, CVC4 1.7 and Z3 4.8.4 were detected by
the :option:`why3 config --detect` command

Split_VC
    is bound to the 1-line strategy

    ::

        t split_vc exit

Auto_level_0
    is bound to

    ::

        c Z3,4.8.4, 1 1000
        c Alt-Ergo,2.3.0, 1 1000
        c CVC4,1.7, 1 1000

    The three provers are tried for a time limit of 1 second and memory
    limit of 1 Gb, each in turn. This is a perfect strategy for a first
    attempt to discharge a new goal.

Auto_level_1
    is bound to

    ::

        c Z3,4.8.4, 5 1000
        c Alt-Ergo,2.3.0, 5 1000
        c CVC4,1.7, 5 1000

    Same as Auto_level_0 but with 5 seconds instead of 1.

Auto_level_2
    is bound to

    ::

        start:
        c Z3,4.8.4, 1 1000
        c Alt-Ergo,2.3.0, 1 1000
        c CVC4,1.7, 1 1000
        t split_vc start
        c Z3,4.8.4, 10 4000
        c Alt-Ergo,2.3.0, 10 4000
        c CVC4,1.7, 10 4000

    The three provers are first tried for a time limit of 1 second and
    memory limit of 1 Gb, each in turn. If none of them succeed, a split
    is attempted. If the split works then the same strategy is retried
    on each sub-goals. If the split does not succeed, the provers are
    tried again with larger limits.

Auto level 3
    is bound to

    ::

        start:
        c Z3,4.8.4, 1 1000
        c Eprover,2.0, 1 1000
        c Spass,3.7, 1 1000
        c Alt-Ergo,2.3.0, 1 1000
        c CVC4,1.7, 1 1000
        t split_vc start
        c Z3,4.8.4, 5 2000
        c Eprover,2.0, 5 2000
        c Spass,3.7, 5 2000
        c Alt-Ergo,2.3.0, 5 2000
        c CVC4,1.7, 5 2000
        t introduce_premises afterintro
        afterintro:
        t inline_goal afterinline
        g trylongertime
        afterinline:
        t split_all_full start
        trylongertime:
        c Z3,4.8.4, 30 4000
        c Eprover,2.0, 30 4000
        c Spass,3.7, 30 4000
        c Alt-Ergo,2.3.0, 30 4000
        c CVC4,1.7, 30 4000

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

WhyML Attributes
----------------

.. why3:attribute:: case_split

.. why3:attribute:: induction

.. why3:attribute:: inline:trivial

.. why3:attribute:: model_trace

.. why3:attribute:: rewrite

.. why3:attribute:: stop_split

.. why3:attribute:: vc:annotation

.. why3:attribute:: vc:divergent

.. why3:attribute:: vc:sp

.. _sec.meta:

Why3 Metas
----------

.. why3:meta:: compute_max_steps

.. why3:meta:: keep:literal

.. why3:meta:: realized_theory

.. why3:meta:: rewrite

.. why3:meta:: rewrite_def

.. _sec.debug:

Debug Flags
-----------

.. why3:debug:: stack_trace
