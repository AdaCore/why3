Foreword
========

Why3 is a platform for deductive program verification. It provides a
rich language for specification and programming, called WhyML, and
relies on external theorem provers, both automated and interactive, to
discharge verification conditions. Why3 comes with a standard library of
logical theories (integer and real arithmetic, Boolean operations, sets
and maps, etc.) and basic programming data structures (arrays, queues,
hash tables, etc.). A user can write WhyML programs directly and get
correct-by-construction OCaml programs through an automated extraction
mechanism. WhyML is also used as an intermediate language for the
verification of C, Java, or Ada programs.

Why3 is a complete reimplementation of the former Why
platform :cite:`filliatre07cav`. Among the new features are:
numerous extensions to the input language, a new architecture for
calling external provers, and a well-designed API, allowing to use Why3
as a software library. An important emphasis is put on modularity and
genericity, giving the end user a possibility to easily reuse Why3
formalizations or to add support for a new external prover if wanted.

Availability
~~~~~~~~~~~~

Why3 project page is http://why3.lri.fr/. The last distribution is
available there, in source format, together with this documentation and
several examples.

Why3 is also distributed under the form of an OPAM package and a Debian
package.

Why3 is distributed as open source and freely available under the terms
of the GNU LGPL 2.1. See the file :file:`LICENSE`.

See the file :file:`INSTALL` for quick installation instructions, and
:numref:`sec.install` of this document for more detailed instructions.

Contact
~~~~~~~

There is a public mailing list for users’ discussions:
http://lists.gforge.inria.fr/mailman/listinfo/why3-club.

Report any bug to the Why3 Bug Tracking System:
https://gitlab.inria.fr/why3/why3/issues.

Acknowledgements
~~~~~~~~~~~~~~~~

We gratefully thank the people who contributed to Why3, directly or
indirectly: Stefan Berghofer, Sylvie Boldo, Martin Clochard, Simon
Cruanes, Sylvain Dailler, Clément Fumex, Léon Gondelman, David Hauzar,
Daisuke Ishii, Johannes Kanig, Mikhail Mandrykin, David Mentré, Benjamin
Monate, Kim Nguyen, Thi-Minh-Tuyen Nguyen, Mário Pereira, Raphaël
Rieu-Helft, Simāo Melo de Sousa, Asma Tafat, Piotr Trojanek, Makarius
Wenzel.
