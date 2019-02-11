
Note
====

This repository is NOT the official Why3 repository. It is a clone of Why3 for
its use in [SPARK](https://github.com/adacore/spark2014). Please report any
issues or pull requests to the [original
project](https://gitlab.inria.fr/why3/why3).

WHY3
====

Why3 is a platform for deductive program verification. It provides
a rich language for specification and programming, called WhyML, and
relies on external theorem provers, both automated and interactive,
to discharge verification conditions. Why3 comes with a standard
library of logical theories (integer and real arithmetic, Boolean
operations, sets and maps, etc.) and basic programming data structures
(arrays, queues, hash tables, etc.). A user can write WhyML programs
directly and get correct-by-construction OCaml programs through an
automated extraction mechanism. WhyML is also used as an intermediate
language for the verification of C, Java, or Ada programs.

PROJECT HOME
------------

http://why3.lri.fr/

https://gitlab.inria.fr/why3/why3

DOCUMENTATION
-------------

The documentation (a tutorial and a reference manual) is in the file
[doc/manual.pdf](http://why3.lri.fr/manual.pdf) or online at
http://why3.lri.fr/doc/.

Various examples can be found in the subdirectories [stdlib/](stdlib)
and [examples/](examples).

Mailing list (Why3 Club):
  http://lists.gforge.inria.fr/mailman/listinfo/why3-club

Bug Tracking System:
  https://gitlab.inria.fr/why3/why3/issues

COPYRIGHT
---------

This program is distributed under the GNU LGPL 2.1. See the enclosed
file [LICENSE](LICENSE).

The files [src/util/extmap.ml{i}](src/util/extmap.mli) are derived from the
sources of OCaml 3.12 standard library, and are distributed under the GNU
LGPL version 2 (see file [OCAML-LICENSE](OCAML-LICENSE)).

Icon sets for the graphical interface of Why3 are subject to specific
licenses, some of them may forbid commercial usage. These specific
licenses are detailed in files [share/images/\*/\*.txt](share/images).

INSTALLATION
------------

See the file [INSTALL.md](INSTALL.md).
