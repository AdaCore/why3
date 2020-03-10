.. _chap.whyml:

Why3 by Examples
================

This chapter describes the WhyML specification and programming language.
A WhyML source file has suffix :file:`.mlw`. It contains a list of modules.
Each module contains a list of declarations. These include

-  Logical declarations:

   -  types (abstract, record, or algebraic data types);

   -  functions and predicates;

   -  axioms, lemmas, and goals.

-  Program data types. In a record type declaration, some fields can be
   declared ``mutable`` and/or ``ghost``. Additionally, a record type
   can be declared ``abstract`` (its fields are only visible in ghost
   code / specification).

-  Program declarations and definitions. Programs include many
   constructs with no counterpart in the logic:

   -  mutable field assignment;

   -  sequence;

   -  loops;

   -  exceptions;

   -  local and anonymous functions;

   -  ghost parameters and ghost code;

   -  annotations: pre- and postconditions, assertions, loop invariants.

   A program may be non-terminating. (But termination can be proved if
   we wish.)

Command-line tools described in the previous chapter also apply to files
containing programs. For instance

::

    why3 prove myfile.mlw

displays the verification conditions for programs contained in file
:file:`myfile.mlw`, and

::

    why3 prove -P alt-ergo myfile.mlw

runs the SMT solver Alt-Ergo on these verification conditions. All this
can be performed within the GUI tool :why3:tool:`why3 ide` as well. See
:numref:`chap.manpages` for more details regarding command lines.

As an introduction to WhyML, we use a small logical puzzle
(:numref:`sec.einstein`) and then the five problems from the VSTTE 2010
verification competition :cite:`vstte10comp`. The source
code for all these examples is contained in Why3’s distribution, in
sub-directory :file:`examples/`. Look for files :file:`logic/einstein.why` and
:file:`vstte10_xxx.mlw`.

.. index:: Einstein’s problem
.. _sec.einstein:

Problem 0: Einstein’s Problem
-----------------------------

Let us use Why3 to solve a little puzzle known as “Einstein’s logic
problem”. (This Why3 example was contributed by Stéphane Lescuyer.)
The problem is stated as follows. Five persons, of five
different nationalities, live in five houses in a row, all painted with
different colors. These five persons own different pets, drink different
beverages, and smoke different brands of cigars. We are given the
following information:

-  The Englishman lives in a red house;

-  The Swede has dogs;

-  The Dane drinks tea;

-  The green house is on the left of the white one;

-  The green house’s owner drinks coffee;

-  The person who smokes Pall Mall has birds;

-  The yellow house’s owner smokes Dunhill;

-  In the house in the center lives someone who drinks milk;

-  The Norwegian lives in the first house;

-  The man who smokes Blends lives next to the one who has cats;

-  The man who owns a horse lives next to the one who smokes Dunhills;

-  The man who smokes Blue Masters drinks beer;

-  The German smokes Prince;

-  The Norwegian lives next to the blue house;

-  The man who smokes Blends has a neighbour who drinks water.

The question is: What is the nationality of the fish’s owner?

We start by introducing a general-purpose theory defining the notion of
*bijection*, as two abstract types together with two functions from one
to the other and two axioms stating that these functions are inverse of
each other.

.. code-block:: whyml

    theory Bijection
      type t
      type u

      function of t : u
      function to_ u : t

      axiom To_of : forall x : t. to_ (of x) = x
      axiom Of_to : forall y : u. of (to_ y) = y
    end

We now start a new theory, ``Einstein``, which will contain all the
individuals of the problem.

.. code-block:: whyml

    theory Einstein

First, we introduce enumeration types for houses, colors, persons,
drinks, cigars, and pets.

.. code-block:: whyml

      type house  = H1 | H2 | H3 | H4 | H5
      type color  = Blue | Green | Red | White | Yellow
      type person = Dane | Englishman | German | Norwegian | Swede
      type drink  = Beer | Coffee | Milk | Tea | Water
      type cigar  = Blend | BlueMaster | Dunhill | PallMall | Prince
      type pet    = Birds | Cats | Dogs | Fish | Horse

We now express that each house is associated bijectively to a color, by
*cloning* the ``Bijection`` theory appropriately.

.. code-block:: whyml

      clone Bijection as Color with type t = house, type u = color

Cloning a theory makes a copy of all its declarations, possibly in
combination with a user-provided substitution
(see :numref:`Module Cloning`).
Here we substitute type
``house`` for type ``t`` and type ``color`` for type ``u``. As a result,
we get two new functions, namely ``Color.of`` and ``Color.to_``, from
houses to colors and colors to houses, respectively, and two new axioms
relating them. Similarly, we express that each house is associated
bijectively to a person

.. code-block:: whyml

      clone Bijection as Owner with type t = house, type u = person

and that drinks, cigars, and pets are all associated bijectively to
persons:

.. code-block:: whyml

      clone Bijection as Drink with type t = person, type u = drink
      clone Bijection as Cigar with type t = person, type u = cigar
      clone Bijection as Pet   with type t = person, type u = pet

Next, we need a way to state that a person lives next to another. We
first define a predicate ``leftof`` over two houses.

.. code-block:: whyml

      predicate leftof (h1 h2 : house) =
        match h1, h2 with
        | H1, H2
        | H2, H3
        | H3, H4
        | H4, H5 -> true
        | _      -> false
        end

Note how we advantageously used pattern matching, with an or-pattern for
the four positive cases and a universal pattern for the remaining 21
cases. It is then immediate to define a ``neighbour`` predicate over two
houses, which completes theory ``Einstein``.

.. code-block:: whyml

      predicate rightof (h1 h2 : house) =
        leftof h2 h1
      predicate neighbour (h1 h2 : house) =
        leftof h1 h2 \/ rightof h1 h2
    end

The next theory contains the 15 hypotheses. It starts by importing
theory ``Einstein``.

.. code-block:: whyml

    theory EinsteinHints
      use Einstein

Then each hypothesis is stated in terms of ``to_`` and ``of`` functions.
For instance, the hypothesis “The Englishman lives in a red house” is
declared as the following axiom.

.. code-block:: whyml

      axiom Hint1: Color.of (Owner.to_ Englishman) = Red

And so on for all other hypotheses, up to “The man who smokes Blends has
a neighbour who drinks water”, which completes this theory.

.. code-block:: whyml

      ...
      axiom Hint15:
        neighbour (Owner.to_ (Cigar.to_ Blend)) (Owner.to_ (Drink.to_ Water))
    end

Finally, we declare the goal in a fourth theory:

.. code-block:: whyml

    theory Problem
      use Einstein
      use EinsteinHints

      goal G: Pet.to_ Fish = German
    end

and we can use Why3 to discharge this goal with any prover of our
choice.

.. code-block:: console

    > why3 prove -P alt-ergo einstein.why
    einstein.why Goals G: Valid (1.27s, 989 steps)

The source code for this puzzle is available in the source distribution
of Why3, in file :file:`examples/logic/einstein.why`.

.. _sec.maxandsum:

Problem 1: Sum and Maximum
--------------------------

Let us now move to the problems of the VSTTE 2010 verification
competition :cite:`vstte10comp`. The first problem is stated
as follows:

    Given an :math:`N`-element array of natural numbers, write a program
    to compute the sum and the maximum of the elements in the array.

We assume :math:`N \ge 0` and :math:`a[i] \ge 0` for
:math:`0 \le i < N`, as precondition, and we have to prove the following
postcondition:

.. math:: sum \le N \times max.

In a file :file:`max_sum.mlw`, we start a new module:

.. code-block:: whyml

    module MaxAndSum

We are obviously needing arithmetic, so we import the corresponding
theory, exactly as we would do within a theory definition:

.. code-block:: whyml

      use int.Int

We are also going to use references and arrays from Why3 standard
library, so we import the corresponding modules:

.. code-block:: whyml

      use ref.Ref
      use array.Array

Modules ``Ref`` and ``Array`` respectively provide a type ``ref ’a`` for
references and a type ``array ’a`` for arrays, together with useful
operations and traditional syntax. They are loaded from the WhyML files
:file:`ref.mlw` and :file:`array.mlw` in the standard library.

We are now in position to define a program function ``max_sum``. A
function definition is introduced with the keyword ``let``. In our case,
it introduces a function with two arguments, an array ``a`` and its size
``n``:

.. code-block:: whyml

      let max_sum (a: array int) (n: int) : (int, int) = ...

(There is a function ``length`` to get the size of an array but we add
this extra parameter ``n`` to stay close to the original problem
statement.) The function body is a Hoare triple, that is a precondition,
a program expression, and a postcondition.

.. code-block:: whyml

      let max_sum (a: array int) (n: int) : (int, int)
        requires { n = length a }
        requires { forall i. 0 <= i < n -> a[i] >= 0 }
        ensures  { let (sum, max) = result in sum <= n * max }
      = ... expression ...

The first precondition expresses that ``n`` is equal to the length of
``a`` (this will be needed for verification conditions related to array
bound checking). The second precondition expresses that all elements of
``a`` are non-negative. The postcondition decomposes the value returned
by the function as a pair of integers ``(sum, max)`` and states the
required property.

.. code-block:: whyml

        returns { sum, max -> sum <= n * max }

We are now left with the function body itself, that is a code computing
the sum and the maximum of all elements in ``a``. With no surprise, it
is as simple as introducing two local references

.. code-block:: whyml

        let sum = ref 0 in
        let max = ref 0 in

scanning the array with a ``for`` loop, updating ``max`` and ``sum``

.. code-block:: whyml

        for i = 0 to n - 1 do
          if !max < a[i] then max := a[i];
          sum := !sum + a[i]
        done;

and finally returning the pair of the values contained in ``sum`` and
``max``:

.. code-block:: whyml

      !sum, !max

This completes the code for function ``max_sum``. As such, it cannot be
proved correct, since the loop is still lacking a loop invariant. In
this case, the loop invariant is as simple as ``!sum <= i * !max``,
since the postcondition only requires us to prove ``sum <= n * max``.
The loop invariant is introduced with the keyword ``invariant``,
immediately after the keyword ``do``:

.. code-block:: whyml

        for i = 0 to n - 1 do
          invariant { !sum <= i * !max }
          ...
        done

There is no need to introduce a variant, as the termination of a ``for``
loop is automatically guaranteed. This completes module ``MaxAndSum``,
shown below.

.. code-block:: whyml

    module MaxAndSum

      use int.Int
      use ref.Ref
      use array.Array

      let max_sum (a: array int) (n: int) : (int, int)
        requires { n = length a }
        requires { forall i. 0 <= i < n -> a[i] >= 0 }
        returns  { sum, max -> sum <= n * max }
      = let sum = ref 0 in
        let max = ref 0 in
        for i = 0 to n - 1 do
          invariant { !sum <= i * !max }
          if !max < a[i] then max := a[i];
          sum := !sum + a[i]
        done;
        !sum, !max

    end

We can now proceed to its verification. Running :program:`why3`, or better
:why3:tool:`why3 ide`, on file :file:`max_sum.mlw` shows a single verification
condition with name ``WP max_sum``. Discharging this verification
condition requires a little bit of non-linear arithmetic. Thus some SMT
solvers may fail at proving it, but other succeed, *e.g.*, CVC4.

Note: It is of course possible to *execute* the code to test it,
before or after you prove it correct. This is detailed in
:numref:`sec.execute`.

.. index:: auto-dereference
.. rubric:: Auto-dereference

Why3 features an auto-dereferencing mechanism, which simplifies the use of
references. When a reference is introduced using ``let ref x`` (instead
of ``let x = ref``), the use of operator ``!`` to access its value
is not needed anymore. For instance, we can rewrite the program above
as follows (the contract being unchanged and omitted):

.. code-block:: whyml

    let max_sum (a: array int) (n: int) : (sum: int, max: int)
    = let ref sum = 0 in
      let ref max = 0 in
      for i = 0 to n - 1 do
        invariant { sum <= i * max }
        if max < a[i] then max <- a[i];
        sum <- sum + a[i]
      done;
      sum, max

Note that use of operator ``<-`` for assignment (instead of ``:=``)
and the absence of ``!`` both in the loop invariant and in the program.
See :numref:`auto-dereference` for more details about the
auto-dereferencing mechanism.


Problem 2: Inverting an Injection
---------------------------------

The second problem is stated as follows:

    Invert an injective array :math:`A` on :math:`N` elements in the
    subrange from :math:`0` to :math:`N - 1`, the output array :math:`B`
    must be such that :math:`B[A[i]] = i` for :math:`0 \le i < N`.

The code is immediate, since it is as simple as

.. code-block:: whyml

        for i = 0 to n - 1 do b[a[i]] <- i done

so it is more a matter of specification and of getting the proof done
with as much automation as possible. In a new file, we start a new
module and we import arithmetic and arrays:

.. code-block:: whyml

    module InvertingAnInjection
      use int.Int
      use array.Array

It is convenient to introduce predicate definitions for the properties
of being injective and surjective. These are purely logical
declarations:

.. code-block:: whyml

      predicate injective (a: array int) (n: int) =
        forall i j. 0 <= i < n -> 0 <= j < n -> i <> j -> a[i] <> a[j]

      predicate surjective (a: array int) (n: int) =
        forall i. 0 <= i < n -> exists j: int. (0 <= j < n /\ a[j] = i)

It is also convenient to introduce the predicate “being in the subrange
from 0 to :math:`n-1`”:

.. code-block:: whyml

      predicate range (a: array int) (n: int) =
        forall i. 0 <= i < n -> 0 <= a[i] < n

Using these predicates, we can formulate the assumption that any
injective array of size :math:`n` within the range :math:`0..n-1` is
also surjective:

.. code-block:: whyml

      lemma injective_surjective:
        forall a: array int, n: int.
          injective a n -> range a n -> surjective a n

We declare it as a lemma rather than as an axiom, since it is actually
provable. It requires induction and can be proved using the Coq proof
assistant for instance. Finally we can give the code a specification,
with a loop invariant which simply expresses the values assigned to
array ``b`` so far:

.. code-block:: whyml

      let inverting (a: array int) (b: array int) (n: int)
        requires { n = length a = length b }
        requires { injective a n /\ range a n }
        ensures  { injective b n }
      = for i = 0 to n - 1 do
          invariant { forall j. 0 <= j < i -> b[a[j]] = j }
          b[a[i]] <- i
        done

Here we chose to have array ``b`` as argument; returning a freshly
allocated array would be equally simple. The whole module is given below.
The verification conditions for function
``inverting`` are easily discharged automatically, thanks to the lemma.

.. code-block:: whyml

    module InvertingAnInjection

      use int.Int
      use array.Array

      predicate injective (a: array int) (n: int) =
        forall i j. 0 <= i < n -> 0 <= j < n -> i <> j -> a[i] <> a[j]

      predicate surjective (a: array int) (n: int) =
        forall i. 0 <= i < n -> exists j: int. (0 <= j < n /\ a[j] = i)

      predicate range (a: array int) (n: int) =
        forall i. 0 <= i < n -> 0 <= a[i] < n

      lemma injective_surjective:
        forall a: array int, n: int.
          injective a n -> range a n -> surjective a n

      let inverting (a: array int) (b: array int) (n: int)
        requires { n = length a = length b }
        requires { injective a n /\ range a n }
        ensures  { injective b n }
      = for i = 0 to n - 1 do
          invariant { forall j. 0 <= j < i -> b[a[j]] = j }
          b[a[i]] <- i
        done

    end

Problem 3: Searching a Linked List
----------------------------------

The third problem is stated as follows:

    Given a linked list representation of a list of integers, find the
    index of the first element that is equal to 0.

More precisely, the specification says

    You have to show that the program returns an index *i* equal
    to the length of the list if there is no such element. Otherwise,
    the *i*-th element of the list must be equal to 0, and all the
    preceding elements must be non-zero.

Since the list is not mutated, we can use the algebraic data type of
polymorphic lists from Why3’s standard library, defined in theory
``list.List``. It comes with other handy theories: ``list.Length``,
which provides a function ``length``, and ``list.Nth``, which provides a
function ``nth`` for the nth element of a list. The latter
returns an option type, depending on whether the index is meaningful or
not.

.. code-block:: whyml

    module SearchingALinkedList
      use int.Int
      use option.Option
      use export list.List
      use export list.Length
      use export list.Nth

It is helpful to introduce two predicates: a first one for a successful
search,

.. code-block:: whyml

      predicate zero_at (l: list int) (i: int) =
        nth i l = Some 0 /\ forall j. 0 <= j < i -> nth j l <> Some 0

and a second one for a non-successful search,

.. code-block:: whyml

      predicate no_zero (l: list int) =
        forall j. 0 <= j < length l -> nth j l <> Some 0

We are now in position to give the code for the search function. We
write it as a recursive function ``search`` that scans a list for the
first zero value:

.. code-block:: whyml

      let rec search (i: int) (l: list int) : int =
        match l with
        | Nil      -> i
        | Cons x r -> if x = 0 then i else search (i+1) r
        end

Passing an index ``i`` as first argument allows to perform a tail call.
A simpler code (yet less efficient) would return 0 in the first branch
and ``1 + search ...`` in the second one, avoiding the extra argument
``i``.

We first prove the termination of this recursive function. It amounts to
giving it a *variant*, that is a value that strictly decreases at each
recursive call with respect to some well-founded ordering. Here it is as
simple as the list ``l`` itself:

.. code-block:: whyml

      let rec search (i: int) (l: list int) : int variant { l } = ...

It is worth pointing out that variants are not limited to values of
algebraic types. A non-negative integer term (for example, ``length l``)
can be used, or a term of any other type equipped with a well-founded
order relation. Several terms can be given, separated with commas, for
lexicographic ordering.

There is no precondition for function ``search``. The postcondition
expresses that either a zero value is found, and consequently the value
returned is bounded accordingly,

.. code-block:: whyml

      i <= result < i + length l /\ zero_at l (result - i)

or no zero value was found, and thus the returned value is exactly ``i``
plus the length of ``l``:

.. code-block:: whyml

      result = i + length l /\ no_zero l

Solving the problem is simply a matter of calling ``search`` with 0 as
first argument. The code is given below. The
verification conditions are all discharged automatically.

.. code-block:: whyml

    module SearchingALinkedList

      use int.Int
      use export list.List
      use export list.Length
      use export list.Nth

      predicate zero_at (l: list int) (i: int) =
        nth i l = Some 0 /\ forall j. 0 <= j < i -> nth j l <> Some 0

      predicate no_zero (l: list int) =
        forall j. 0 <= j < length l -> nth j l <> Some 0

      let rec search (i: int) (l: list int) : int variant { l }
        ensures { (i <= result < i + length l /\ zero_at l (result - i))
               \/ (result = i + length l /\ no_zero l) }
      = match l with
        | Nil -> i
        | Cons x r -> if x = 0 then i else search (i+1) r
        end

      let search_list (l: list int) : int
        ensures { (0 <= result < length l /\ zero_at l result)
               \/ (result = length l /\ no_zero l) }
      = search 0 l

    end

Alternatively, we can implement the search with a ``while`` loop. To do
this, we need to import references from the standard library, together
with theory ``list.HdTl`` which defines functions ``hd`` and ``tl`` over
lists.

.. code-block:: whyml

      use ref.Ref
      use list.HdTl

Being partial functions, ``hd`` and ``tl`` return options. For the
purpose of our code, though, it is simpler to have functions which do
not return options, but have preconditions instead. Such a function
``head`` is defined as follows:

.. code-block:: whyml

      let head (l: list 'a) : 'a
        requires { l <> Nil } ensures { hd l = Some result }
      = match l with Nil -> absurd | Cons h _ -> h end

The program construct ``absurd`` denotes an unreachable piece of code.
It generates the verification condition ``false``, which is here
provable using the precondition (the list cannot be ``Nil``). Function
``tail`` is defined similarly:

.. code-block:: whyml

      let tail (l: list 'a) : list 'a
        requires { l <> Nil } ensures { tl l = Some result }
      = match l with Nil -> absurd | Cons _ t -> t end

Using ``head`` and ``tail``, it is straightforward to implement the
search as a ``while`` loop. It uses a local reference ``i`` to store the
index and another local reference ``s`` to store the list being scanned.
As long as ``s`` is not empty and its head is not zero, it increments
``i`` and advances in ``s`` using function ``tail``.

.. code-block:: whyml

      let search_loop (l: list int) : int =
        ensures { ... same postcondition as in search_list ... }
      = let i = ref 0 in
        let s = ref l in
        while !s <> Nil && head !s <> 0 do
          invariant { ... }
          variant   { !s }
          i := !i + 1;
          s := tail !s
        done;
        !i

The postcondition is exactly the same as for function ``search_list``.
The termination of the ``while`` loop is ensured using a variant,
exactly as for a recursive function. Such a variant must strictly
decrease at each execution of the loop body. The reader is invited to
figure out the loop invariant.

Problem 4: N-Queens
-------------------

The fourth problem is probably the most challenging one. We have to
verify the implementation of a program which solves the *N*-queens
puzzle: place *N* queens on an *N*×*N* chess board so
that no queen can capture another one with a legal move. The program
should return a placement if there is a solution and indicates that
there is no solution otherwise. A placement is a *N*-element array
which assigns the queen on row *i* to its column. Thus we start
our module by importing arithmetic and arrays:

.. code-block:: whyml

    module NQueens
      use int.Int
      use array.Array

The code is a simple backtracking algorithm, which tries to put a queen
on each row of the chess board, one by one (there is basically no better
way to solve the *N*-queens puzzle). A building block is a
function which checks whether the queen on a given row may attack
another queen on a previous row. To verify this function, we first
define a more elementary predicate, which expresses that queens on row
``pos`` and ``q`` do no attack each other:

.. code-block:: whyml

      predicate consistent_row (board: array int) (pos: int) (q: int) =
        board[q] <> board[pos] /\
        board[q] - board[pos] <> pos - q /\
        board[pos] - board[q] <> pos - q

Then it is possible to define the consistency of row ``pos`` with
respect to all previous rows:

.. code-block:: whyml

      predicate is_consistent (board: array int) (pos: int) =
        forall q. 0 <= q < pos -> consistent_row board pos q

Implementing a function which decides this predicate is another matter.
In order for it to be efficient, we want to return ``False`` as soon as
a queen attacks the queen on row ``pos``. We use an exception for this
purpose and it carries the row of the attacking queen:

.. code-block:: whyml

      exception Inconsistent int

The check is implemented by a function ``check_is_consistent``, which
takes the board and the row ``pos`` as arguments, and scans rows from 0
to ``pos - 1`` looking for an attacking queen. As soon as one is found,
the exception is raised. It is caught immediately outside the loop and
``False`` is returned. Whenever the end of the loop is reached, ``True``
is returned.

.. code-block:: whyml

      let check_is_consistent (board: array int) (pos: int) : bool
        requires { 0 <= pos < length board }
        ensures  { result <-> is_consistent board pos }
      = try
          for q = 0 to pos - 1 do
            invariant {
              forall j:int. 0 <= j < q -> consistent_row board pos j
            }
            let bq   = board[q]   in
            let bpos = board[pos] in
            if bq        = bpos    then raise (Inconsistent q);
            if bq - bpos = pos - q then raise (Inconsistent q);
            if bpos - bq = pos - q then raise (Inconsistent q)
          done;
          True
        with Inconsistent q ->
          assert { not (consistent_row board pos q) };
          False
        end

The assertion in the exception handler is a cut for SMT solvers. This
first part of the solution is given below.

.. code-block:: whyml

    module NQueens
      use int.Int
      use array.Array

      predicate consistent_row (board: array int) (pos: int) (q: int) =
        board[q] <> board[pos] /\
        board[q] - board[pos] <> pos - q /\
        board[pos] - board[q] <> pos - q

      predicate is_consistent (board: array int) (pos: int) =
        forall q. 0 <= q < pos -> consistent_row board pos q

      exception Inconsistent int

      let check_is_consistent (board: array int) (pos: int)
        requires { 0 <= pos < length board }
        ensures  { result <-> is_consistent board pos }
      = try
          for q = 0 to pos - 1 do
            invariant {
              forall j:int. 0 <= j < q -> consistent_row board pos j
            }
            let bq   = board[q]   in
            let bpos = board[pos] in
            if bq        = bpos    then raise (Inconsistent q);
            if bq - bpos = pos - q then raise (Inconsistent q);
            if bpos - bq = pos - q then raise (Inconsistent q)
          done;
          True
        with Inconsistent q ->
          assert { not (consistent_row board pos q) };
          False
        end

We now proceed with the verification of the backtracking algorithm. The
specification requires us to define the notion of solution, which is
straightforward using the predicate ``is_consistent`` above. However,
since the algorithm will try to complete a given partial solution, it is
more convenient to define the notion of partial solution, up to a given
row. It is even more convenient to split it in two predicates, one
related to legal column values and another to consistency of rows:

.. code-block:: whyml

      predicate is_board (board: array int) (pos: int) =
        forall q. 0 <= q < pos -> 0 <= board[q] < length board

      predicate solution (board: array int) (pos: int) =
        is_board board pos /\
        forall q. 0 <= q < pos -> is_consistent board q

The algorithm will not mutate the partial solution it is given and, in
case of a search failure, will claim that there is no solution extending
this prefix. For this reason, we introduce a predicate comparing two
chess boards for equality up to a given row:

.. code-block:: whyml

      predicate eq_board (b1 b2: array int) (pos: int) =
        forall q. 0 <= q < pos -> b1[q] = b2[q]

The search itself makes use of an exception to signal a successful
search:

.. code-block:: whyml

      exception Solution

The backtracking code is a recursive function ``bt_queens`` which takes
the chess board, its size, and the starting row for the search. The
termination is ensured by the obvious variant ``n - pos``.

.. code-block:: whyml

      let rec bt_queens (board: array int) (n: int) (pos: int) : unit
        variant  { n - pos }

The precondition relates ``board``, ``pos``, and ``n`` and requires
``board`` to be a solution up to ``pos``:

.. code-block:: whyml

        requires { 0 <= pos <= n = length board }
        requires { solution board pos }

The postcondition is twofold: either the function exits normally and
then there is no solution extending the prefix in ``board``, which has
not been modified; or the function raises ``Solution`` and we have a
solution in ``board``.

.. code-block:: whyml

        ensures  { eq_board board (old board) pos }
        ensures  { forall b:array int. length b = n -> is_board b n ->
                     eq_board board b pos -> not (solution b n) }
        raises   { Solution -> solution board n }
      =

Whenever we reach the end of the chess board, we have found a solution
and we signal it using exception ``Solution``:

.. code-block:: whyml

        if pos = n then raise Solution;

Otherwise we scan all possible positions for the queen on row ``pos``
with a ``for`` loop:

.. code-block:: whyml

        for i = 0 to n - 1 do

The loop invariant states that we have not modified the solution prefix
so far, and that we have not found any solution that would extend this
prefix with a queen on row ``pos`` at a column below ``i``:

.. code-block:: whyml

          invariant { eq_board board (old board) pos }
          invariant { forall b:array int.  length b = n -> is_board b n ->
            eq_board board b pos -> 0 <= b[pos] < i -> not (solution b n) }

Then we assign column ``i`` to the queen on row ``pos`` and we check for
a possible attack with ``check_is_consistent``. If not, we call
``bt_queens`` recursively on the next row.

.. code-block:: whyml

          board[pos] <- i;
          if check_is_consistent board pos then bt_queens board n (pos + 1)
        done

This completes the loop and function ``bt_queens`` as well. Solving the
puzzle is a simple call to ``bt_queens``, starting the search on row 0.
The postcondition is also twofold, as for ``bt_queens``, yet slightly
simpler.

.. code-block:: whyml

      let queens (board: array int) (n: int) : unit
        requires { length board = n }
        ensures  { forall b:array int.
                     length b = n -> is_board b n -> not (solution b n) }
        raises   { Solution -> solution board n }
      = bt_queens board n 0

This second part of the solution is given below. With
the help of a few auxiliary lemmas — not given here but available from
Why3’s sources — the verification conditions are all discharged
automatically, including the verification of the lemmas themselves.

.. code-block:: whyml

      predicate is_board (board: array int) (pos: int) =
        forall q. 0 <= q < pos -> 0 <= board[q] < length board

      predicate solution (board: array int) (pos: int) =
        is_board board pos /\
        forall q. 0 <= q < pos -> is_consistent board q

      predicate eq_board (b1 b2: array int) (pos: int) =
        forall q. 0 <= q < pos -> b1[q] = b2[q]

      exception Solution

      let rec bt_queens (board: array int) (n: int) (pos: int) : unit
        variant  { n - pos }
        requires { 0 <= pos <= n = length board }
        requires { solution board pos }
        ensures  { eq_board board (old board) pos }
        ensures  { forall b:array int. length b = n -> is_board b n ->
                     eq_board board b pos -> not (solution b n) }
        raises   { Solution -> solution board n }
      = if pos = n then raise Solution;
        for i = 0 to n - 1 do
          invariant { eq_board board (old board) pos }
          invariant { forall b:array int. length b = n -> is_board b n ->
            eq_board board b pos -> 0 <= b[pos] < i -> not (solution b n) }
          board[pos] <- i;
          if check_is_consistent board pos then bt_queens board n (pos + 1)
        done

      let queens (board: array int) (n: int) : unit
        requires { length board = n }
        ensures  { forall b:array int.
                     length b = n -> is_board b n -> not (solution b n) }
        raises   { Solution -> solution board n }
      = bt_queens board n 0

    end

.. _sec.aqueue:

Problem 5: Amortized Queue
--------------------------

The last problem consists in verifying the implementation of a
well-known purely applicative data structure for queues. A queue is
composed of two lists, *front* and *rear*. We push elements at the head
of list *rear* and pop them off the head of list *front*. We maintain
that the length of *front* is always greater or equal to the length of
*rear*. (See for instance Okasaki’s *Purely Functional Data
Structures* :cite:`okasaki98` for more details.)

We have to implement operations ``empty``, ``head``, ``tail``, and
``enqueue`` over this data type, to show that the invariant over lengths
is maintained, and finally
to show that a client invoking these operations observes an abstract
queue given by a sequence.

In a new module, we import arithmetic and theory ``list.ListRich``, a
combo theory that imports all list operations we will require: length,
reversal, and concatenation.

.. code-block:: whyml

    module AmortizedQueue
      use int.Int
      use option.Option
      use export list.ListRich

The queue data type is naturally introduced as a polymorphic record
type. The two list lengths are explicitly stored, for greater
efficiency.

.. code-block:: whyml

      type queue 'a = { front: list 'a; lenf: int;
                        rear : list 'a; lenr: int; }
      invariant { length front = lenf >= length rear = lenr }
      by { front = Nil; lenf = 0; rear = Nil; lenr = 0 }

The type definition is accompanied with an invariant — a logical
property imposed on any value of the type. Why3 assumes that any
queue satisfies the invariant at any function entry and
it requires that any queue satisfies the invariant at function exit
(be the queue created or modified).
The ``by`` clause ensures the non-vacuity of this type with
invariant. If you omit it, a goal with an existential statement is
generated. (See :numref:`Record Types` for more details about record
types with invariants.)

For the purpose of the specification, it is convenient to introduce a
function ``sequence`` which builds the sequence of elements of a queue,
that is the front list concatenated to the reversed rear list.

.. code-block:: whyml

      function sequence (q: queue 'a) : list 'a = q.front ++ reverse q.rear

It is worth pointing out that this function can only be used in
specifications. We start with the easiest operation: building the empty
queue.

.. code-block:: whyml

      let empty () : queue 'a
        ensures { sequence result = Nil }
      = { front = Nil; lenf = 0; rear = Nil; lenr = 0 }

The postcondition states that the returned queue represents the empty
sequence. Another postcondition, saying that the returned queue
satisfies the type invariant, is implicit. Note the cast to type
``queue 'a``. It is required, for the type checker not to complain about
an undefined type variable.

The next operation is ``head``, which returns the first element from a
given queue ``q``. It naturally requires the queue to be non empty,
which is conveniently expressed as ``sequence q`` not being ``Nil``.

.. code-block:: whyml

      let head (q: queue 'a) : 'a
        requires { sequence q <> Nil }
        ensures  { hd (sequence q) = Some result }
      = let Cons x _ = q.front in x

The fact that the argument ``q`` satisfies the type invariant is
implicitly assumed. The type invariant is required to prove the
absurdity of ``q.front`` being ``Nil`` (otherwise, ``sequence q`` would
be ``Nil`` as well).

The next operation is ``tail``, which removes the first element from a
given queue. This is more subtle than ``head``, since we may have to
re-structure the queue to maintain the invariant. Since we will have to
perform a similar operation when implementing operation ``enqueue``
later, it is a good idea to introduce a smart constructor ``create``
that builds a queue from two lists while ensuring the invariant. The
list lengths are also passed as arguments, to avoid unnecessary
computations.

.. code-block:: whyml

      let create (f: list 'a) (lf: int) (r: list 'a) (lr: int) : queue 'a
        requires { lf = length f /\ lr = length r }
        ensures  { sequence result = f ++ reverse r }
      = if lf >= lr then
          { front = f; lenf = lf; rear = r; lenr = lr }
        else
          let f = f ++ reverse r in
          { front = f; lenf = lf + lr; rear = Nil; lenr = 0 }

If the invariant already holds, it is simply a matter of building the
record. Otherwise, we empty the rear list and build a new front list as
the concatenation of list ``f`` and the reversal of list ``r``. The
principle of this implementation is that the cost of this reversal will
be amortized over all queue operations. Implementing function ``tail``
is now straightforward and follows the structure of function ``head``.

.. code-block:: whyml

      let tail (q: queue 'a) : queue 'a
        requires { sequence q <> Nil }
        ensures  { tl (sequence q) = Some (sequence result) }
      = let Cons _ r = q.front in
        create r (q.lenf - 1) q.rear q.lenr

The last operation is ``enqueue``, which pushes a new element in a given
queue. Reusing the smart constructor ``create`` makes it a one line
code.

.. code-block:: whyml

      let enqueue (x: 'a) (q: queue 'a) : queue 'a
        ensures { sequence result = sequence q ++ Cons x Nil }
      = create q.front q.lenf (Cons x q.rear) (q.lenr + 1)

The code is given below. The verification conditions are
all discharged automatically.

.. code-block:: whyml

    module AmortizedQueue

      use int.Int
      use option.Option
      use list.ListRich

      type queue 'a = { front: list 'a; lenf: int;
                        rear : list 'a; lenr: int; }
        invariant { length front = lenf >= length rear = lenr }
        by { front = Nil; lenf = 0; rear = Nil; lenr = 0 }

      function sequence (q: queue 'a) : list 'a =
        q.front ++ reverse q.rear

      let empty () : queue 'a
        ensures { sequence result = Nil }
      = { front = Nil; lenf = 0; rear = Nil; lenr = 0 }

      let head (q: queue 'a) : 'a
        requires { sequence q <> Nil }
        ensures  { hd (sequence q) = Some result }
      = let Cons x _ = q.front in x

      let create (f: list 'a) (lf: int) (r: list 'a) (lr: int) : queue 'a
        requires { lf = length f /\ lr = length r }
        ensures  { sequence result = f ++ reverse r }
      = if lf >= lr then
          { front = f; lenf = lf; rear = r; lenr = lr }
        else
          let f = f ++ reverse r in
          { front = f; lenf = lf + lr; rear = Nil; lenr = 0 }

      let tail (q: queue 'a) : queue 'a
        requires { sequence q <> Nil }
        ensures  { tl (sequence q) = Some (sequence result) }
      = let Cons _ r = q.front in
        create r (q.lenf - 1) q.rear q.lenr

      let enqueue (x: 'a) (q: queue 'a) : queue 'a
        ensures { sequence result = sequence q ++ Cons x Nil }
      = create q.front q.lenf (Cons x q.rear) (q.lenr + 1)

    end
