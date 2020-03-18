Release Notes
=============

.. _auto-dereference:

Release Notes for version 1.2: new syntax for “auto-dereference”
----------------------------------------------------------------

.. index:: auto-dereference

Version 1.2 introduces a simplified syntax for reference variables, to
avoid the somehow heavy OCaml syntax using bang character. In short, this
is syntactic sugar summarized in the following table. An example using
this new syntax is in :file:`examples/isqrt.mlw`.

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
``contents`` require importing ``ref.Ref`` or ``why3.Ref.Ref``.
Operations ``(:=)`` and ``(!)`` require importing ``ref.Ref``.

Operation ``(:=)`` is fully subsumed by direct assignment ``(<-)``.

Release Notes for version 1.0: syntax changes w.r.t. 0.88
---------------------------------------------------------

The syntax of WhyML programs changed in release 1.0.
The following table summarizes the changes.

+---------------------------------------------+---------------------------------------------------------------+
| version 0.88                                | version 1.0                                                   |
+=============================================+===============================================================+
| ``function f ...``                          | ``let function f ...`` if called in programs                  |
+---------------------------------------------+---------------------------------------------------------------+
| ``'L:``                                     | ``label L in``                                                |
+---------------------------------------------+---------------------------------------------------------------+
| ``at x 'L``                                 | ``x at L``                                                    |
+---------------------------------------------+---------------------------------------------------------------+
| ``\ x. e``                                  | ``fun x -> e``                                                |
+---------------------------------------------+---------------------------------------------------------------+
| ``use HighOrd``                             | not needed anymore                                            |
+---------------------------------------------+---------------------------------------------------------------+
| ``HighOrd.pred ty``                         | ``ty -> bool``                                                |
+---------------------------------------------+---------------------------------------------------------------+
| ``type t model ...``                        | ``type t = abstract ...``                                     |
+---------------------------------------------+---------------------------------------------------------------+
| ``abstract e ensures { Q }``                | ``begin ensures { Q } e end``                                 |
+---------------------------------------------+---------------------------------------------------------------+
| ``namespace N``                             | ``scope N``                                                   |
+---------------------------------------------+---------------------------------------------------------------+
| ``use import M``                            | ``use M``                                                     |
+---------------------------------------------+---------------------------------------------------------------+
| ``"attribute"``                             | ``[@attribute]``                                              |
+---------------------------------------------+---------------------------------------------------------------+
| ``meta M prop P``                           | ``meta M lemma P`` or ``meta M axiom P`` or ``meta M goal P`` |
+---------------------------------------------+---------------------------------------------------------------+
| ``loop ... end``                            | ``while true do ... done``                                    |
+---------------------------------------------+---------------------------------------------------------------+
| ``type ... invariant { ... self.foo ... }`` | ``type ... invariant { ... foo ... }``                        |
+---------------------------------------------+---------------------------------------------------------------+

Note also that logical symbols can no longer be used in non-ghost code;
in particular, there is no polymorphic equality in programs anymore, so
equality functions must be declared/defined on a per-type basis (already
done for type ``int`` in the standard library). The :file:`CHANGES.md` file
describes other potential sources of incompatibility.

Here are a few more semantic changes.

Proving only partial correctness:

  In versions 0.xx of Why3, when a program function is recursive but not
  given a variant, or contains a while loop not given a variant, then it
  was assumed that the user wants to prove partial correctness only.
  A warning was issued, recommending to add an extra ``diverges`` clause
  to that function's contract. It was also possible to disable that
  warning by adding the label ``"W:diverges:N"`` to the function's name.
  Version 1.0 of Why3 is more aggressively requiring the user to prove
  the termination of functions which are not given the ``diverges``
  clause, and the previous warning is now an error. The possibility of
  proving only partial correctness is now given on a more fine-grain
  basis: any expression for which one wants to prove partial correctness
  only, must by annotated with the attribute ``[@vc:divergent]``.

  In other words, if one was using the following structure in Why3 0.xx:

  ::

     let f "W:diverges:N" <parameters> <contract> = <body>

  then in 1.0 it should be written as

  ::

     let f <parameters> <contract> = [@vc:divergent] <body>

Semantics of the ``any`` construct:

  The ``any`` construct in Why3 0.xx was introducing an arbitrary value
  satisfying the associated post-condition. In some sense, this construct
  was introducing some form of an axiom stating that such a value exists.
  In Why3 1.0, it is now mandatory to prove the existence of such
  a value, and a VC is generated for that purpose.

  To obtain the effect of the former semantics of the ``any`` construct,
  one should use instead a local ``val`` function. In other words, if one
  was using the following structure in Why3 0.xx:

  ::

     any t ensures { P }

  then in 1.0 it should be written as

  ::

     val x:t ensures { P } in x

Release Notes for version 0.80: syntax changes w.r.t. 0.73
----------------------------------------------------------

The syntax of WhyML programs changed in release 0.80. The following table
summarizes the changes.

+---------------------------------+---------------------------------+
| version 0.73                    | version 0.80                    |
+=================================+=================================+
| ``type t = {| field: int |}``   | ``type t = { field~:~int }``    |
+---------------------------------+---------------------------------+
| ``{| field = 5 |}``             | ``{ field = 5 }``               |
+---------------------------------+---------------------------------+
| ``use import module M``         | ``use import M``                |
+---------------------------------+---------------------------------+
| .. code-block:: whyml           | .. code-block:: whyml           |
|                                 |                                 |
|    let rec f (x:int) (y:int): t |    let rec f (x:int) (y:int): t |
|      variant { t } with rel =   |      variant { t with rel }     |
|      { P }                      |      requires { P }             |
|      e                          |      ensures { Q }              |
|      { Q }                      |      raises { Exc1 -> R1        |
|      | Exc1 -> { R1 }           |             | Exc2 n -> R2 }    |
|      | Exc2 n -> { R2 }         |    = e                          |
+---------------------------------+---------------------------------+
| .. code-block:: whyml           | .. code-block:: whyml           |
|                                 |                                 |
|    val f (x:int) (y:int):       |    val f (x:int) (y:int): t     |
|      { P }                      |      requires { P }             |
|      t                          |      writes { a, b }            |
|      writes a b                 |      ensures { Q }              |
|      { Q }                      |      raises { Exc1 -> R1        |
|      | Exc1 -> { R1 }           |             | Exc2 n -> R2 }    |
|      | Exc2 n -> { R2 }         |                                 |
+---------------------------------+---------------------------------+
| ``abstract e { Q }``            | ``abstract e ensures { Q }``    |
+---------------------------------+---------------------------------+

Summary of Changes w.r.t. Why 2
-------------------------------

The main new features with respect to Why 2.xx
are the following.

1. Completely redesigned input syntax for logic declarations

   - new syntax for terms and formulas
   - enumerated and algebraic data types, pattern matching
   - recursive definitions of logic functions and predicates, with
     termination checking
   - inductive definitions of predicates
   - declarations are structured in components called “theories”,
     which can be reused and instantiated

2. More generic handling of goals and lemmas to prove

   - concept of proof task
   - generic concept of task transformation
   - generic approach for communicating with external provers

3. Source code organized as a library with a documented API, to
   allow access to Why3 features programmatically.

4. GUI with new features with respect to the former GWhy

   - session save and restore
   - prover calls in parallel
   - splitting, and more generally applying task transformations,
     on demand
   - ability to edit proofs for interactive provers (Coq only for
     the moment) on any subtask

5. Extensible architecture via plugins

   - users can define new transformations
   - users can add connections to additional provers
