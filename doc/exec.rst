.. _chap.exec:

Executing WhyML Programs
========================

This chapter shows how WhyML code can be executed, either by being
interpreted or compiled to some existing programming language.

.. _sec.execute:

Interpreting WhyML Code
-----------------------

Consider the program of :numref:`sec.maxandsum` that computes the
maximum and the sum of an array of integers.
Let us assume it is contained in a file :file:`maxsum.mlw`.

To test function ``max_sum``, we can introduce a WhyML test function
in module ``MaxAndSum``

.. code-block:: whyml

      let test () =
        let n = 10 in
        let a = make n 0 in
        a[0] <- 9; a[1] <- 5; a[2] <- 0; a[3] <- 2;  a[4] <- 7;
        a[5] <- 3; a[6] <- 2; a[7] <- 1; a[8] <- 10; a[9] <- 6;
        max_sum a n

and then we use the :why3:tool:`execute` command to interpret this
function, as follows:

.. code-block:: console

    $ why3 execute maxsum.mlw --use=MaxAndSum 'test ()'
    result: (int, int) = (45, 10)
    globals:

We get the expected output, namely the pair ``(45, 10)``.

Notice that the WhyML interpreter optionally supports Runtime
Assertion Checking (RAC). This is detailed in
:numref:`sec.why3execute`.

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

Extraction of functors
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

::

    why3 extract -D ocaml64 bst.mlw --modular -o .

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


Custom extraction drivers
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

    $ why3 extract -D ocaml64 -D mydriver.drv -L . file.M
    let double (x: int) : int = x + x
    ...

When using such custom drivers, it is not possible to pass Why3 file
names on the command line; one has to specify module names to be
extracted, as done above.

Compiling to Other Languages
----------------------------

The :why3:tool:`extract` command can produce code for languages other
than just OCaml. This is a matter of choosing a suitable driver.

Compiling to C
''''''''''''''

Consider the following example. It defines a function that returns the
position of the maximum element in an array ``a`` of size ``n``.

.. code-block:: whyml

   use int.Int
   use map.Map as Map
   use mach.c.C
   use mach.int.Int32
   use mach.int.Int64

   function ([]) (a: ptr 'a) (i: int): 'a = Map.get a.data.Array.elts (a.offset + i)

   let locate_max (a: ptr int64) (n: int32): int32
     requires { 0 < n }
     requires { valid a n }
     ensures  { 0 <= result < n }
     ensures  { forall i. 0 <= i < n -> a[i] <= a[result] }
   = let ref idx = 0 in
     for j = 1 to n - 1 do
       invariant { 0 <= idx < n }
       invariant { forall i. 0 <= i < j -> a[i] <= a[idx] }
       if get_ofs a idx < get_ofs a j then idx <- j
     done;
     idx

There are a few differences with a standard WhyML program. The main
one is that the array is described by a value of type ``ptr int64``,
which models a C pointer of type ``int64_t *``.

Among other things, the type ``ptr 'a`` has two fields: ``data`` and
``offset``. The ``data`` field is of type ``array 'a``; its value
represents the content of the memory block (as allocated by
``malloc``) the pointer points into. The ``offset`` field indicates
the actual position of the pointer into that block, as it might not
point at the start of the block.

The WhyML expression ``get_ofs a j`` in the example corresponds to the
C expression ``a[j]``. The assignment ``a[j] = v`` could be expressed
as ``set_ofs a j v``. To access just ``*a`` (i.e., ``a[0]``), one
could use ``get a`` and ``set a v``.

For the access ``a[j]`` to have a well-defined behavior, the memory
block needs to have been allocated and not yet freed, and it needs to
be large enough to accommodate the offset ``j``. This is expressed
using the precondition ``valid a n``, which means that the block
extends at least until ``a.offset + n``.

The code can be extracted to C using the following command:

::

   why3 extract -D c locate_max.mlw

This gives the following C code.

.. code-block:: C

   #include <stdint.h>

   int32_t locate_max(int64_t * a, int32_t n) {
     int32_t idx;
     int32_t j, o;
     idx = 0;
     o = n - 1;
     if (1 <= o) {
       for (j = 1; ; ++j) {
         if (a[idx] < a[j]) {
           idx = j;
         }
         if (j == o) break;
       }
     }
     return idx;
   }

Not any WhyML code can be extracted to C. Here is a list of supported features and a few rules that your code must follow for extraction to succeed.

* Basic datatypes

   * Integer types declared in ``mach.int`` library are supported for
     sizes 16, 32 and 64 bits. They are translated into C types of
     appropriate size and sign, say ``int32_t``, ``uint64_t``, etc.

   * The mathematical integer type ``int`` is not supported.

   * The Boolean type is translated to C type ``int``. The bitwise operators from ``bool.Bool`` are
     supported.

   * Character and strings are partially supported via the functions
     declared in ``mach.c.String`` library

   * Floating-point types are not yet supported

* Compound datatypes

   * Record types are supported. When they have no mutable fields,
     they are translated into C structs, and as such are passed by value and returned by
     value. For example the WhyML code

     .. code-block:: whyml

        use mach.int.Int32
        type r = { x : int32; y : int32 }
        let swap (a : r) : r = { x = a.y ; y = a.x }

     is extracted as

     .. code-block:: c

        #include <stdint.h>

        struct r {
          int32_t x;
          int32_t y;
        };

        struct r swap(struct r a) {
          struct r r;
          r.x = a.y;
          r.y = a.x;
          return r;
        }

     On the other hand, records with mutable fields are interpreted as
     pointers to structs, and are thus passed by reference. For example the WhyML code

     .. code-block:: whyml

        use mach.int.Int32
        type r = { mutable x : int32; mutable y : int32 }
        let swap (a : r) : unit =
           let tmp = a.y in a.y <- a.x; a.x <- tmp

     is extracted as

     .. code-block:: c

        struct r {
          int32_t x;
          int32_t y;
        };

        void swap(struct r * a) {
          int32_t tmp;
          tmp = a->y;
          a->y = a->x;
          a->x = tmp;
        }

   * WhyML arrays are not supported

   * Pointer types are supported via the type ``ptr`` declared in
     library ``mach.c.C``. See above for an example of use.

   * Algebraic datatypes are not supported (even enumerations)

* Pointer aliasing constraints

   The type ``ptr`` from ``mach.c.C`` must be seen as a WhyML mutable
   type, and as such is subject to the WhyML restrictions regarding
   aliasing. In particular, two pointers passed as argument to a
   function are implicitly not aliased.

* Control flow structures

   * Sequences, conditionals, ``while`` loops and ``for`` loops are supported
   * Pattern matching is not supported
   * Exception raising and catching is not supported
   * ``break``, ``continue`` and ``return`` are supported

.. include:: whyml2java.inc
