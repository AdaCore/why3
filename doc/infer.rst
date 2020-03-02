Inference of Loop Invariants
============================

This chapter shows how to install and use ``loop-infer``, an utility
based in *abstract interpretation* to infer loop invariants. This is
still work in progress and many features are still not covered.

Availability
------------

The ``loop-infer`` utility has the following OCaml dependencies.

-  ``apron``: can be installed using .

-  ``camllib``: required by ``fixpoint`` and can also be installed using
   .

-  ``fixpoint``: follow instructions below.

The ``fixpoint`` library is not available in . To install it one needs
to download the sources and install it. The following instructions can
be performed in any directory.

::

    > svn co svn://scm.gforge.inria.fr/svnroot/bjeannet/pkg/fixpoint
    > cd fixpoint/trunk/
    > cp Makefile.config.model Makefile.config
    > # if required make modifications to Makefile.config
    > make all     # compiles
    > make install # uses ocamlfind to install the library

Once the dependencies are installed, the configuration script of should
enable the compilation of the ``loop-infer`` utility when the flag
``–enable-infer`` is passed.

::

    > ./configure --enable-infer
    # ...
    Components
        Invariant inference     : yes
    # ...

Running it
----------

Why3 compilation should generate a new why3 subcommand ’infer’

run it with

::

    why3 infer <file>.mlw

it produces a file ``<file>.mlw_inferred.mlw`` where the invariants
found are inserted

For information about how to use the API to infer loop invariants refer
to Section [sec:infer-loop-api].
