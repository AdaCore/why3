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

.. code-block:: console

    > why3 execute maxsum.mlw --use=MaxAndSum 'test ()'
    result: (int, int) = (45, 10)
    globals:

We get the expected output, namely the pair ``(45, 10)``.

.. _sec.extract:

Compiling WhyML to OCaml
------------------------

.. program:: why3 extract

An alternative to interpretation is to compile WhyML to OCaml. We do so
using the :why3:tool:`extract` command, as follows:

::

    why3 extract -D ocaml64 maxsum.mlw -o max_sum.ml

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

    ocamlbuild -pkg zarith main.native

Since Why3’s type ``int`` is translated to OCaml arbitrary precision
integers using the ``ZArith`` library, we have to pass option
``-pkg zarith`` to :program:`ocamlbuild`. In order to get extracted code that
uses OCaml’s native integers instead, one has to use Why3’s types for
63-bit integers from libraries ``mach.int.Int63`` and
``mach.array.Array63``.

Examples
''''''''

We illustrate different ways of using the :why3:tool:`extract` command through
some examples.

Consider the program of :numref:`sec.aqueue`.

If we are only interested in extracting function ``enqueue``, we can
proceed as follows:

::

    why3 extract -D ocaml64 -L . aqueue.AmortizedQueue.enqueue -o aqueue.ml

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

    why3 extract --recursive -D ocaml64 -L . aqueue.AmortizedQueue.enqueue -o aqueue.ml

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

Extraction of Functors
''''''''''''''''''''''

WhyML and OCaml are both dialects of the ML-family, sharing many syntactic and
semantics traits. Yet their module systems differ significantly.
A WhyML program is a list of modules, a module is a list of top-level
declarations, and declarations can be organized within *scopes*, the WhyML unit
for namespaces management. In particular, there is no support for sub-modules in
Why3, nor a dedicated syntactic construction for functors. The latter are
represented, instead, as modules containing only abstract symbols
:cite:`paskevich20isola`. One must follow exactly this programming pattern when
it comes to extract an OCaml functor from a Why3 proof. Let us consider the
following (excerpt) of a WhyML module implementing binary search
trees:

.. code-block:: whyml

    module BST
      scope Make
        scope Ord
          type t
          val compare : t -> t -> int
        end

        type elt = Ord.t

        type t = E | N t elt t

        use int.Int

        let rec insert (x: elt) (t: t)
        = match t with
          | E -> N E x E
          | N l y r ->
              if Ord.compare x y > 0 then N l y (insert x r)
              else N (insert x l) y r
          end
      end
    end

For the sake of simplicity, we omit here behavioral specification. Assuming the
above example is contained in a file named :file:`bst.mlw`, one can
readily extract it into OCaml, as follows:

.. code-block:: console

    > why3 extract -D ocaml64 bst.mlw --modular -o .

This produces the following functorial implementation:

.. code-block:: ocaml

    module Make (Ord: sig type t
      val compare : t -> t -> Z.t end) =
    struct
      type elt = Ord.t

      type t =
      | E
      | N of t * Ord.t * t

      let rec insert (x: Ord.t) (t: t) : t =
        match t with
        | E -> N (E, x, E)
        | N (l, y, r) ->
            if Z.gt (Ord.compare x y) Z.zero
            then N (l, y, insert x r)
            else N (insert x l, y, r)
    end

The extracted code features the functor ``Make`` parameterized with a
module containing the abstract type ``t`` and function
``compare``. This is similar to the OCaml standard library when it
comes to data structures parameterized by an order relation, *e.g.*,
the ``Set`` and ``Map`` modules.

From the result of the extraction, one understands that scope ``Make``
is turned into a functor, while the nested scope ``Ord`` is extracted
as the functor argument. In summary, for a WhyML implementation of the
form

.. code-block:: whyml

    module M
      scope A
        scope X ... end
        scope Y ... end
        scope Z ... end
      end
      ...
    end

contained in file :file:`f.mlw`, the Why3 extraction engine produces the
following OCaml code:

.. code-block:: ocaml

    module A (X: ...) (Y: ...) (Z: ...) = struct
      ...
    end

and prints it into file :file:`f__M.ml`. In order for functor extraction
to succeed, scopes ``X``, ``Y``, and ``Z`` can only contain
non-defined programming symbols, *i.e.*, abstract type declarations,
function signatures, and exception declarations. If ever a scope mixes
non-defined and defined symbols, or if there is no surrounding scope
such as ``Make``, the extraction will complain about
the presence of non-defined symbols that cannot be extracted.

It is worth noting that extraction of functors only works for
*modular* extraction (*i.e.* with command-line option :option:`--modular`).


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

.. code-block:: console

    > why3 extract -D ocaml64 -D mydriver.drv -L . file.M
    let double (x: int) : int = x + x
    ...

When using such custom drivers, it is not possible to pass Why3 file
names on the command line; one has to specify module names to be
extracted, as done above.
