
.. _chap.inferloop:

Inference of Loop Invariants
============================

This chapter shows how to install and use *infer-loop*, an utility
based on *abstract interpretation* to infer loop invariants. This is
still work in progress and many features are still very limited.

Availability
------------

The ``infer-loop`` utility has the following OCaml dependencies.

-  ``apron``: can be installed using ``opam``.

-  ``camllib``: can be installed using ``opam``.

-  ``fixpoint``: follow instructions below.

The ``fixpoint`` library is not available in ``opam``. To install it
one needs to download the its sources and install it manually. The
following instructions can be performed in any directory.

::

    svn co svn://scm.gforge.inria.fr/svnroot/bjeannet/pkg/fixpoint
    cd fixpoint/trunk/
    cp Makefile.config.model Makefile.config
    # if required make modifications to Makefile.config
    make all     # compiles
    make install # uses ocamlfind to install the library

By default *infer-loop* is not compiled and integrated with Why3. So,
once the dependencies above are installed, the configuration script of
Why3 should enable the compilation of the ``infer-loop`` utility, as
follows:

::

    ./configure --enable-infer
    # ...
    Components
        Invariant inference(exp): yes
    # ...

Running it
----------

[TODO]

For information about how to use the API to infer loop invariants refer
to :numref:`sec:infer-loop-api`.
