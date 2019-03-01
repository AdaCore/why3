.. _chap.api:

The Why3 API
============

This chapter is a tutorial for the users who want to link their own
OCaml code with the Why3 library. We progressively introduce the way one
can use the library to build terms, formulas, theories, proof tasks,
call external provers on tasks, and apply transformations on tasks. The
complete documentation for API calls is given

at URL .

We assume the reader has a fair knowledge of the OCaml language. Notice
that the Why3 library must be installed, see :numref:`sec.installlib`.
The OCaml code given below is available in the source distribution in
directory ``examples/use_api/`` together with a few other examples.

.. _sec.prop_form:

Building Propositional Formulas
-------------------------------

The first step is to know how to build propositional formulas. The
module ``Term`` gives a few functions for building these. Here is a
piece of OCaml code for building the formula :math:`\mathit{true} \lor
\mathit{false}`. The library uses the common type ``term`` both for
terms (expressions that produce a value of some particular type) and
formulas (boolean-valued expressions). Such a formula can be printed
using the module ``Pretty`` providing pretty-printers.

Assuming the lines above are written in a file ``f.ml``, it can be
compiled using

::

    ocamlfind ocamlc -package why3 -linkpkg f.ml -o f

Running the generated executable ``f`` results in the following output.

::

    formula 1 is: true \/ false

Let us now build a formula with propositional variables:
:math:`A \land B
\rightarrow A`. Propositional variables must be declared first before
using them in formulas. This is done as follows. The type ``lsymbol`` is
the type of function and predicate symbols (which we call logic symbols
for brevity). Then the atoms :math:`A` and :math:`B` must be built by
the general function for applying a predicate symbol to a list of terms.
Here we just need the empty list of arguments.

As expected, the output is as follows.

::

    formula 2 is: A /\ B -> A

Notice that the concrete syntax of Why3 forbids function and predicate
names to start with a capital letter (except for the algebraic type
constructors which must start with one). This constraint is not enforced
when building those directly using library calls.

Building Tasks
--------------

Let us see how we can call a prover to prove a formula. As said in
previous chapters, a prover must be given a task, so we need to build
tasks from our formulas. Task can be build incrementally from an empty
task by adding declaration to it, using the functions ``add__decl`` of
module ``Task``. For the formula :math:`\mathit{true} \lor
\mathit{false}` above, this is done as follows. To make the formula a
goal, we must give a name to it, here “goal1”. A goal name has type
``prsymbol``, for identifiers denoting propositions in a theory or a
task. Notice again that the concrete syntax of Why3 requires these
symbols to be capitalized, but it is not mandatory when using the
library. The second argument of ``add_prop_decl`` is the kind of the
proposition: ``Paxiom``, ``Plemma`` or ``Pgoal``. Notice that lemmas are
not allowed in tasks and can only be used in theories.

Once a task is built, it can be printed.

The task for our second formula is a bit more complex to build, because
the variables A and B must be added as abstract (not defined)
propositional symbols in the task.

Execution of our OCaml program now outputs:

::

    task 1 is:
    theory Task
      goal Goal1 : true \/ false
    end

    task 2 is:
    theory Task
      predicate A

      predicate B

      goal Goal2 : A /\ B -> A
    end

.. _sec.api.callingprovers:

Calling External Provers
------------------------

To call an external prover, we need to access the Why3 configuration
file ``why3.conf``, as it was built using the ``why3config`` command
line tool or the menu of the graphical IDE. The following API calls
allow to access the content of this configuration file. The type
``’a Whyconf.Mprover.t`` is a map indexed by provers. A prover is a
record with a name, a version, and an alternative description (to
differentiate between various configurations of a given prover). Its
definition is in the module ``Whyconf``: The map ``provers`` provides
the set of existing provers. In the following, we directly attempt to
access a prover named “Alt-Ergo”, any version. We could also get a
specific version with :

The next step is to obtain the driver associated to this prover. A
driver typically depends on the standard theories so these should be
loaded first.

We are now ready to call the prover on the tasks. This is done by a
function call that launches the external executable and waits for its
termination. Here is a simple way to proceed: This way to call a prover
is in general too naive, since it may never return if the prover runs
without time limit. The function ``prove_task`` has an optional
parameter ``limit``, a record defined in module ``Call_provers``: where
the field ``limit_time`` is the maximum allowed running time in seconds,
and ``limit_mem`` is the maximum allowed memory in megabytes. The type
``prover_result`` is a record defined in module ``Call_provers``: with
in particular the fields:

-  ``pr_answer``: the prover answer, explained below;

-  ``pr_time`` : the time taken by the prover, in seconds.

A ``pr_answer`` is the sum type defined in module ``Call_provers``:
corresponding to these kinds of answers:

-  ``Valid``: the task is valid according to the prover.

-  ``Invalid``: the task is invalid.

-  ``Timeout``: the prover exceeds the time limit.

-  ``OutOfMemory``: the prover exceeds the memory limit.

-  ``Unknown`` :math:`msg`: the prover can’t determine if the task is
   valid; the string parameter :math:`msg` indicates some extra
   information.

-  ``Failure`` :math:`msg`: the prover reports a failure, it was unable
   to read correctly its input task.

-  ``HighFailure``: an error occurred while trying to call the prover,
   or the prover answer was not understood (none of the given regular
   expressions in the driver file matches the output of the prover).

Here is thus another way of calling the Alt-Ergo prover, on our second
task. The output of our program is now as follows.

::

    On task 1, alt-ergo answers Valid (0.01s)
    On task 2, alt-ergo answers Valid in  0.01 seconds

Building Terms
--------------

An important feature of the functions for building terms and formulas is
that they statically guarantee that only well-typed terms can be
constructed.

Here is the way we build the formula :math:`2+2=4`. The main difficulty
is to access the internal identifier for addition: it must be retrieved
from the standard theory ``Int`` of the file ``int.why``. An important
point to notice as that when building the application of :math:`+` to
the arguments, it is checked that the types are correct. Indeed the
constructor ``t_app_infer`` infers the type of the resulting term. One
could also provide the expected type as follows.

When building a task with this formula, we need to declare that we use
theory ``Int``:

Building Quantified Formulas
----------------------------

To illustrate how to build quantified formulas, let us consider the
formula :math:`\forall x:int. x*x \geq 0`. The first step is to obtain
the symbols from ``Int``. The next step is to introduce the variable
:math:`x` with the type int. The formula :math:`x*x \geq 0` is obtained
as in the previous example. To quantify on :math:`x`, we use the
appropriate smart constructor as follows.

Building Theories
-----------------

We illustrate now how one can build theories. Building a theory must be
done by a sequence of calls:

-  creating a theory “under construction”, of type ``Theory.theory_uc``;

-  adding declarations, one at a time;

-  closing the theory under construction, obtaining something of type
   ``Theory.theory``.

Creation of a theory named ``My_theory`` is done by First let us add
formula 1 above as a goal: Note that we reused the goal identifier
``goal_id1`` that we already defined to create task 1 above.

Adding formula 2 needs to add the declarations of predicate variables A
and B first:

Adding formula 3 is a bit more complex since it uses integers, thus it
requires to “use” the theory ``int.Int``. Using a theory is indeed not a
primitive operation in the API: it must be done by a combination of an
“export” and the creation of a namespace. We provide a helper function
for that: Addition of formula 3 is then

Addition of goal 4 is nothing more complex:

Finally, we close our theory under construction as follows.

We can inspect what we did by printing that theory: which outputs

::

    my new theory is as follows:

    theory My_theory
      (* use BuiltIn *)

      goal goal1 : true \/ false

      predicate A

      predicate B

      goal goal2 : A /\ B -> A

      (* use int.Int *)

      goal goal3 : (2 + 2) = 4

      goal goal4 : forall x:int. (x * x) >= 0
    end

From a theory, one can compute at once all the proof tasks it contains
as follows: Note that the tasks are returned in reverse order, so we
reverse the list above.

We can check our generated tasks by printing them:

One can run provers on those tasks exactly as we did above.

Operations on Terms and Formulas, Transformations
-------------------------------------------------

The following code illustrates a simple recursive functions of formulas.
It explores the formula and when a negation is found, it tries to push
it down below a conjunction, a disjunction or a quantifier.

The following illustrates how to turn such an OCaml function into a
transformation in the sense of the Why3 API. Moreover, it registers that
transformation to make it available for example in Why3 IDE.

The directory ``src/transform`` contains the code for the many
transformations that are already available in Why3.

Proof Sessions
--------------

See the example ``examples/use_api/create_session.ml`` of the
distribution for an illustration on how to manipulate proof sessions
from an OCaml program.

ML Programs
-----------

The simplest way to build WhyML programs from OCaml is to build untyped
syntax trees for such programs, and then call the Why3 typing procedure
to build typed declarations.

The examples of this section are available in the file
``examples/use_api/mlw_tree.ml`` of the distribution.

The first step is to build an environment as already illustrated in
:numref:`sec.api.callingprovers`, and open the OCaml module ``Ptree``
which contains most of the OCaml functions we need in this section.

To contain all the example programs we are going to build we need a
module. We start the creation of that module using the following
declarations, that first introduces a pseudo “file” to hold the module,
then the module itself called ``Program``. Notice the use of a first
simple helper function ``mk_ident`` to build an identifier without any
attributes nor any location.

To write our programs, we need to import some other modules from the
standard library. The following introduces two helper functions for
building qualified identifiers and importing modules, and finally
imports ``int.Int``.

We want now to build a program equivalent to the following code in
concrete Why3 syntax.

The OCaml code that programmatically build this Why3 function is as
follows. This code makes uses of helper functions that are given in
:numref:`fig.helpers`.

We want now to build a program equivalent to the following code in
concrete Why3 syntax. We need to import the ``ref.Ref`` module first.
The rest is similar to the first example, the code is as follows

The next example makes use of arrays. The corresponding OCaml code is as
follows

Having declared all the programs we wanted to write, we can now close
the module and the file, and get as a result the set of modules of our
file, under the form of a map of module names to modules.

We can then construct the proofs tasks for our module, and then try to
call the Alt-Ergo prover. The rest of that code is using OCaml functions
that were already introduced before.

Generating counterexamples
--------------------------

That feature is presented in details in :numref:`sec.idece`, that should
be read first. The counterexamples can also be generated using the API.
The following explains how to change the source code (mainly adding
attributes) in order to display counterexamples and how to parse the
result given by Why3. To illustrate this, we will adapt the examples
from :numref:`sec.prop\_form` to display counterexamples.

Attributes and locations on identifiers
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

For variables to be used for counterexamples they need to contain an
attribute called ``model_trace`` and a location. The ``model_trace``
states the name the user wants the variable to be named in the output of
the counterexamples pass. Usually, people put a reference to their
program AST node in this attribute: this helps them to parse and display
the results given by Why3. The locations are also necessary as every
counterexamples values with no location won’t be displayed. For example,
an assignment of the source language such as the following will probably
trigger the creation of an ident (for the left value) in a user
subsequent tasks:

::

    x := !y + 1

This means that the ident generated for :math:`x` will hold both a
``model_trace`` and a location.

The example becomes the following: In the above, we defined a
proposition ident with a location and a ``model_trace``.

Attributes in formulas
~~~~~~~~~~~~~~~~~~~~~~

Now that variables are tagged, we can define formulas. To define a goal
formula for counterexamples, we need to tag it with the
``vc:annotation`` attribute. This attribute is automatically added when
using the VC generation of Why3, but on a user-built task, this needs to
be added. We also need to add a location for this goal. The following is
obtained for the simple formula linking :math:`A` and :math:`B`:

Note: the transformations used for counterexamples will create new
variables for each variable occuring inside the formula tagged by
``vc:annotation``. These variables are duplicates located at the VC
line. They allow giving all counterexample values located at that VC
line.

Counterexamples output formats
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Several output formats are available for counterexamples. For users who
want to pretty-print their counterexamples values, we recommend to use
the JSON output as follows:
