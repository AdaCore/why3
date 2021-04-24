.. _chap.vcgen:

The VC Generators
=================

This chapter gives information about the various processes that generate
the so-called verification conditions, VC for short, from WhyML code.


VC generation for program functions
-----------------------------------

For each program function of the form

.. parsed-literal::

   let *f* (*x*:sub:`1`: *t*:sub:`1`) ... (*x*:sub:`n`: *t*:sub:`n`): *t*
     requires { *Pre* }
     ensures  { *Post* }
   = *body*

a new logic goal called ``f'VC`` is generated. Its shape is

.. math::

   \forall x_1,\dots,x_n,\quad \mathit{Pre} \Rightarrow \mathit{WP}(\mathit{body},\mathit{Post})

where :math:`\mathit{WP}(e,Q)` is a formula computed automatically using
rules defined recursively on :math:`e`.

TODO: Refer to `A Pragmatic Type System for Deductive Verification <https://hal.archives-ouvertes.fr/hal-01256434v3>`_


Attributes: :why3:attribute:`[@vc:divergent]` disables generation of VC for termination

Other attributes: :why3:attribute:`[@vc:annotation]`, :why3:attribute:`[@vc:sp]`, :why3:attribute:`[@vc:wp]`, :why3:attribute:`[@vc:white_box]`, :why3:attribute:`[@vc:keep_precondition]`



VC generated for type invariants
--------------------------------

How a VC is generated for proving that a type with invariant is
inhabited. Explain also the use of the `by` keyword in this context.

VC generation and lemma functions
---------------------------------

How a VC for a program function marked as `lemma` is turned into an
hypothesis for the remaining of the module.

Using strongest post-conditions
-------------------------------

To avoid exponential explosion of WP computation, Why3 provides a
mechanism similar to (TODO: cite papers here).

This can be activited locally on any program expression, by putting
the :why3:attribute:`[@vc:sp]` attribute on that expression. Yet, the simplest usage
is to pose this attribute on the whole body of a program function.

Show an example.


.. _sec.runwithinferloop:

Automatic inference of loop invariants
--------------------------------------

Why3 can be executed with support for inferring loop invariants
:cite:`baudin17` (see :numref:`sec.installinferloop` for information
about the compilation of Why3 with support for `infer-loop`).

There are two ways of enabling the inference of loop invariants: by
passing the debug flag :why3:debug:`infer-loop` to Why3 or by annotating ``let``
declarations with the :why3:attribute:`[@infer]` attribute.

Below is an example on how to invoke Why3 such that invariants are
inferred for all the loops in the given file.

::

   why3 ide tests/infer/incr.mlw --debug=infer-loop

In this case, the *Polyhedra* default domain will be used together
with the default widening value of *3*. Why3 GUI will not display the
inferred invariants in the source code, but the VCs corresponding to
those invariants will be displayed and labeled with the ``infer-loop``
keyword as shown in :numref:`fig.gui.infer`.

.. _fig.gui.infer:

.. figure:: images/gui-infer.png
   :alt: The GUI with inferred invariants (after split).

   The GUI with inferred invariants (after split).

Alternatively, attributes can be used in ``let`` declarations so that
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


There are a few debugging flags that can be passed to Why3 to output
additional information about the inference of loop invariants. Flag
:why3:debug:`infer-print-cfg` will print the Control Flow Graph (CFG) used for
abstract interpretation in a file with the name :file:`inferdbg.dot`;
:why3:debug:`infer-print-ai-result` will print to the standard output the
computed abstract values at each point of the CFG;
:why3:debug:`print-inferred-invs` will print the inferred invariants to the
standard output (note that the displayed identifiers names might not
be consistent with those in the initial program); finally,
:why3:debug:`print-domains-loop` will print for each loop the
loop expression, the domain at that point, and its translation into a
Why3 term.

Current limitations
"""""""""""""""""""

1. Loop invariants can only be inferred for loops inside
   (non-recursive) ``let`` declarations.
