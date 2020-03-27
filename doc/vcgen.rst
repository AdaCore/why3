.. _chap.vcgen:

The VC generators
=================

This chapter gives information about the various processes that generates the so-called verification conditions, VC for shot, from WhyML code.


VC generation for program functions
-----------------------------------

For each program function of the form

..

  `let` :math:`f (x_1:t_1) (x_n:t_n) : t`
    `requires` { :math:`Pre` }
    `ensures`  { :math:`Post` }
    `=` :math:`body`

a new logic goal called `f'VC` is generated. Its shape is

.. math:: \forall x_1,..,x_n.  Pre \rightarrow WP(body,Post)

where :math:`WP(e,Q)` is a formula computed automatically using rules defined recursively on :math:`e`.

TODO: Refer to `A Pragmatic Type System for Deductive Verification <https://hal.archives-ouvertes.fr/hal-01256434v3>`_

VC generated for type invariants
--------------------------------

How a VC is generated for proving that a type with invariant is
inhabited. Explain also the use of the `by` keyword in this context.

VC generation and lemma functions
---------------------------------

How a VC for a program function marked as `lemma` is turned into an
hypothesis for the remaining of the module.

Using Strongest Post-conditions
-------------------------------

To avoid exponential explosion of WP computation, Why3 provides a
mechanism similar to (TODO: cite papers here).

This can be activited locally on any program expression, by putting
the :why3:attribute:`[@vc:sp]` attribute on that expression. Yet, the simplest usage
is to pose this attribute on the whole body of a program function.

Show an example.

Automatic inference of loop invariants
--------------------------------------

Doc by Claudio to insert here.
