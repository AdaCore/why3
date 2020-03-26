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
the attribute `[@vc:sp]` on that expression. Yet, the simplest usage
is to pose this attribute on the whole body of a program function.

Show an example.

.. _sec.runwithinferloop:

Automatic inference of loop invariants
--------------------------------------

Why3 can be executed with support for inferring loop invariants
:cite:`baudin17` (for information about compilation of the
`infer-loop` mechanism refer to :numref:`sec.installinferloop`). This
can be done by passing the *debug* flag ``infer-loop`` to Why3 or by
annotating *let* declarations with the ``[@infer]`` attribute.

As an example consider the following invocation of Why3.

::

   why3 ide tests/infer/incr.mlw --debug infer-loop

In this case, Why3 will infer invariants for all the loops inside all
the let declarations. Note that, the *Polyhedra* default domain will
be used together with the default widening value of *3*. Why3 GUI will
not display the inferred invariants in the source code, but the VCs
corresponding to those invariants will be displayed and labeled with
the ``infer-loop`` keyword as shown in :numref:`fig.gui.infer`.

.. _fig.gui.infer:

.. figure:: images/gui-infer.png
   :alt: The GUI with inferred invariants (after split).

Alternatively, attributes can be used in let declarations so that
invariants are inferred for all the loops in that declaration. In this
case, it is possible to select the desired domain and widening
value. In the example below, invariants will be inferred using the
*Polyhedra* domain and a widening value of *4*. These two arguments of
the attribute can swapped, for instance, ``[@infer:Polyhedra:4]`` will
produce exactly the same invariants.

.. code-block:: whyml

  module Incr

    use int.Int
    use int.MinMax
    use ref.Ref
    use ref.Refint

    let incr[@infer:4:Polyhedra](x:int) : int
      ensures { result = max x 0 }
    = let i = ref 0 in
      while !i < x do
        variant { x - !i }
        incr i;
      done;
      !i
  end
