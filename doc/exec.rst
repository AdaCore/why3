.. _chap.exec:

Executing WhyML Programs
========================

This chapter shows how WhyML code can be executed, either by being
interpreted or compiled to some existing programming language.

Let us consider the program of :numref:`sec.maxandsum` that computes the
maximum and the sum of an array of integers.

Let us assume it is contained in a file :file:`maxsum.mlw`.

.. _sec.execute:

Interpreting WhyML Code
-----------------------

To test function ``max_sum``, we can introduce a WhyML test function in
module ``MaxAndSum``

.. code-block:: whyml

      let test () =
        let n = 10 in
        let a = make n 0 in
        a[0] <- 9; a[1] <- 5; a[2] <- 0; a[3] <- 2;  a[4] <- 7;
        a[5] <- 3; a[6] <- 2; a[7] <- 1; a[8] <- 10; a[9] <- 6;
        max_sum a n

and then we use the :why3:tool:`execute` command to interpret this function, as
follows:

::

    > why3 execute maxsum.mlw MaxAndSum.test
    Execution of MaxAndSum.test ():
         type: (int, int)
       result: (45, 10)
      globals:

We get the expected output, namely the pair ``(45, 10)``.

.. _sec.extract:

Compiling WhyML to OCaml
------------------------

.. program:: why3 extract

An alternative to interpretation is to compile WhyML to OCaml. We do so
using the :why3:tool:`extract` command, as follows:

::

    > why3 extract -D ocaml64 maxsum.mlw -o max_sum.ml

The :why3:tool:`extract` command requires the name of a driver, which indicates
how theories/modules from the Why3 standard library are translated to
OCaml. Here we assume a 64-bit architecture and thus we pass
``ocaml64``. We also specify an output file using option :option:`-o`, namely
:file:`max_sum.ml`. After this command, the file :file:`max_sum.ml` contains an
OCaml code for function ``max_sum``. To compile it, we create a file
:file:`main.ml` containing a call to ``max_sum``, *e.g.*,

.. code-block:: ocaml

    let a = Array.map Z.of_int [| 9; 5; 0; 2; 7; 3; 2; 1; 10; 6 |]
    let s, m = Max_sum.max_sum a (Z.of_int 10)
    let () = Format.printf "sum=%s, max=%s@." (Z.to_string s) (Z.to_string m)

It is convenient to use :program:`ocamlbuild` to compile and link both files
:file:`max_sum.ml` and :file:`main.ml`:

::

    > ocamlbuild -pkg zarith main.native

Since Why3’s type ``int`` is translated to OCaml arbitrary precision
integers using the ``ZArith`` library, we have to pass option
``-pkg zarith`` to :program:`ocamlbuild`. In order to get extracted code that
uses OCaml’s native integers instead, one has to use Why3’s types for
63-bit integers from libraries ``mach.int.Int63`` and
``mach.array.Array63``.

Extraction Starting Point
'''''''''''''''''''''''''

The :why3:tool:`extract` command accepts three different targets for extraction:
a WhyML file, a module, or a symbol (function, type, exception). To
extract all the symbols from every module of a file named :file:`f.mlw`, one
should write

::

    > why3 extract -D <driver> f.mlw

To extract only the symbols from module ``M`` of file :file:`f.mlw`, one
should write

::

    > why3 extract -D <driver> -L <dir> f.M

To extract only the symbol ``s`` (a function, a type, or an exception)
from module ``M`` of file :file:`f.mlw`, one should write

::

    > why3 extract -D <driver> -L <dir> f.M.s

Note the use of :option:`-L`, for both extraction of a module and a
symbol, in order to state the location of file :file:`f.mlw`.

Options
'''''''

The following options can be added to the extraction command line:

.. option:: --flat

   Perform a flat extraction, *i.e.*, everything is extracted into a
   single file. This is the default behavior. The :option:`-o` option should
   be given the name of a file or, if omitted, the result of extraction
   is printed to the standard output.

.. option:: --modular

    Each module is extracted in its own, separated file. The :option:`-o`
    option cannot be omitted, and it should be given the name of an
    existing directory. This directory will be populated with the
    resulting OCaml files.

.. option:: --recursive

    Recursively extract all the dependencies of the chosen entry point.
    This option is valid for both :option:`--modular` and :option:`--flat` options.

Examples
''''''''

We illustrate different ways of using the :why3:tool:`extract` command through
some examples.

Consider the program of :numref:`sec.aqueue`.

If we are only interested in extracting function ``enqueue``, we can
proceed as follows:

::

    > why3 extract -D ocaml64 -L . aqueue.AmortizedQueue.enqueue -o aqueue.ml

Here we assume that file :file:`aqueue.mlw` contains this program, and that
we invoke the :why3:tool:`extract` command from the directory where this file is stored. File
:file:`aqueue.ml` now contains the following OCaml code:

.. code-block:: ocaml

    let enqueue (x: 'a) (q: 'a queue) : 'a queue =
      create (q.front) (q.lenf) (x :: (q.rear))
        (Z.add (q.lenr) (Z.of_string "1"))

Choosing a function symbol as the entry point of extraction allows us to
focus only on specific parts of the program. However, the generated code
cannot be type-checked by the OCaml compiler, as it depends on function
``create`` and on type ``'a queue``, whose definitions are not given. In
order to obtain a *complete* OCaml implementation, we can perform a
recursive extraction:

::

    > why3 extract --recursive -D ocaml64 -L . \
        aqueue.AmortizedQueue.enqueue -o aqueue.ml

This updates the contents of file :file:`aqueue.ml` as follows:

.. code-block:: ocaml

    type 'a queue = {
      front: 'a list;
      lenf: Z.t;
      rear: 'a list;
      lenr: Z.t;
      }

    let create (f: 'a list) (lf: Z.t) (r: 'a list) (lr: Z.t) : 'a queue =
      if Z.geq lf lr
      then
        { front = f; lenf = lf; rear = r; lenr = lr }
      else
        let f1 = List.append f (List.rev r) in
        { front = f1; lenf = Z.add lf lr; rear = []; lenr = (Z.of_string "0") }

    let enqueue (x: 'a) (q: 'a queue) : 'a queue =
      create (q.front) (q.lenf) (x :: (q.rear))
        (Z.add (q.lenr) (Z.of_string "1"))

This new version of the code is now accepted by the OCaml compiler
(provided the ``ZArith`` library is available, as above).

Custom Extraction Drivers
'''''''''''''''''''''''''

Several OCaml drivers can be specified on the command line, using option
:option:`-D` several times. In particular, one can provide a custom driver to
map some symbols of a Why3 development to existing OCaml code. Suppose
for instance we have a file :file:`file.mlw` containing a proof
parameterized with some type ``elt`` and some binary function ``f``:

.. code-block:: whyml

    module M
      type elt
      val f (x y: elt) : elt
      let double (x: elt) : elt = f x x
      ...

When it comes to extract this module to OCaml, we may want to
instantiate type ``elt`` with OCaml’s type ``int`` and function ``f``
with OCaml’s addition. For this purpose, we provide the following in a
file :file:`mydriver.drv`:

::

    module file.M
      syntax type elt "int"
      syntax val  f   "%1 + %2"
    end

OCaml fragments to be substituted for Why3 symbols are given as
arbitrary strings, where ``%1``, ``%2``, etc., will be replaced with
actual arguments. Here is the extraction command line and its output:

::

    > why3 extract -D ocaml64 -D mydriver.drv -L . file.M
    let double (x: int) : int = x + x
    ...

When using such custom drivers, it is not possible to pass Why3 file
names on the command line; one has to specify module names to be
extracted, as done above.
