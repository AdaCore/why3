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
verification of C, Java, Rust, and Ada programs.

Why3 is a complete reimplementation of the former Why
platform :cite:`filliatre07cav`. Among the new features are:
numerous extensions to the input language, a new architecture for
calling external provers, and a well-designed API, allowing to use Why3
as a software library. An important emphasis is put on modularity and
genericity, giving the end user a possibility to easily reuse Why3
formalizations or to add support for a new external prover if wanted.

Availability
~~~~~~~~~~~~

Why3 project page is https://www.why3.org/. The latest release is
available there, in source format, together with this documentation and
several examples.

Why3 is also distributed under the form of an OPAM package and a Debian
package.

Why3 is distributed as open source and freely available under the terms
of the GNU LGPL 2.1. See the file :file:`LICENSE`.

See the file :file:`INSTALL.md` for quick installation instructions, and
:numref:`sec.install` of this document for more detailed instructions.

Contact
~~~~~~~

There is a Zulip discussion forum for users' discussion:
https://why3.zulipchat.com/
together with a public mailing list:
https://groupes.renater.fr/sympa/info/why3-club.

Report any bug to the Why3 Bug Tracking System (if you have an account there):
https://gitlab.inria.fr/why3/why3/issues
or to the Zulip forum.

Acknowledgements
~~~~~~~~~~~~~~~~

We gratefully thank the people who contributed to Why3, directly or
indirectly: Lucas Baudin, Benedikt Becker, Cláudio Belo Lourenço,
Stefan Berghofer, Sylvie Boldo, Paul Bonnot, Martin Clochard,
Guillaume Cluzel, Simon Cruanes, Sylvain Dailler, Xavier Denis, Yacine
El Haddad, Clément Fumex, Quentin Garchery, Léon Gondelman, David
Hauzar, Daisuke Ishii, Benjamin Jorge, Jacques-Henri Jourdan, Johannes
Kanig, Mikhail Mandrykin, Matteo Manighetti, David Mentré, Benjamin
Monate, Solène Moreau, Kim Nguyễn, Thi-Minh-Tuyen Nguyen, Paul
Patault, Mário Pereira, Gérald Point, Raphaël Rieu-Helft, Gabriel
Scherer, Simão Melo de Sousa, Asma Tafat, Piotr Trojanek, Makarius
Wenzel.
