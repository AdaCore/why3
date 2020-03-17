.. _chap.api:

The Why3 API
============

This chapter is a tutorial for the users who want to link their own
OCaml code with the Why3 library. We progressively introduce the way one
can use the library to build terms, formulas, theories, proof tasks,
call external provers on tasks, and apply transformations on tasks. The
complete documentation for API calls is given at URL |apiurl|.

We assume the reader has a fair knowledge of the OCaml language. Notice
that the Why3 library must be installed, see :numref:`sec.installlib`.
The OCaml code given below is available in the source distribution in
directory :file:`examples/use_api/` together with a few other examples.

.. _sec.prop_form:

Building Propositional Formulas
-------------------------------

The first step is to know how to build propositional formulas. The
module ``Term`` gives a few functions for building these. Here is a
piece of OCaml code for building the formula ``true \/ false``.

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{opening}
   :end-before: END{opening}

The library uses the common type ``term`` both for terms (i.e.,
expressions that produce a value of some particular type) and formulas
(i.e., boolean-valued expressions).

Such a formula can be printed using the module ``Pretty`` providing
pretty-printers.

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{printformula}
   :end-before: END{printformula}

Assuming the lines above are written in a file :file:`f.ml`, it can be
compiled using

::

    ocamlfind ocamlc -package why3 -linkpkg f.ml -o f

Running the generated executable :file:`f` results in the following output.

::

    formula 1 is: true \/ false

Let us now build a formula with propositional variables: ``A /\ B -> A``.
Propositional variables must be declared first before
using them in formulas. This is done as follows.

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{declarepropvars}
   :end-before: END{declarepropvars}

The type ``lsymbol`` is the type of function and predicate symbols (which
we call logic symbols for brevity). Then the atoms ``A``
and ``B`` must be built by the general function for applying
a predicate symbol to a list of terms. Here we just need the empty list
of arguments.

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{declarepropatoms}
   :end-before: END{declarepropatoms}

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
task by adding declaration to it, using the functions ``add_*_decl`` of
module ``Task``. For the formula ``true \/ false`` above,
this is done as follows.

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{buildtask}
   :end-before: END{buildtask}

To make the formula a
goal, we must give a name to it, here “goal1”. A goal name has type
``prsymbol``, for identifiers denoting propositions in a theory or a
task. Notice again that the concrete syntax of Why3 requires these
symbols to be capitalized, but it is not mandatory when using the
library. The second argument of ``add_prop_decl`` is the kind of the
proposition: ``Paxiom``, ``Plemma`` or ``Pgoal``. Notice that lemmas are
not allowed in tasks and can only be used in theories.

Once a task is built, it can be printed.

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{printtask}
   :end-before: END{printtask}

The task for our second formula is a bit more complex to build, because
the variables A and B must be added as abstract (*i.e.*, not defined)
propositional symbols in the task.

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{buildtask2}
   :end-before: END{buildtask2}

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
file :file:`why3.conf`, as it was built using the :why3:tool:`why3 config` command
line tool or the *Detect Provers* menu of the graphical IDE. The following API calls
make it possible to access the content of this configuration file.

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{getconf}
   :end-before: END{getconf}

The type ``'a Whyconf.Mprover.t`` is a map indexed by provers. A prover
is a record with a name, a version, and an alternative description (to
differentiate between various configurations of a given prover). Its
definition is in the module ``Whyconf``:

.. literalinclude:: ../src/driver/whyconf.ml
   :language: ocaml
   :start-after: BEGIN{provertype}
   :end-before: END{provertype}

The map ``provers`` provides
the set of existing provers. In the following, we directly attempt to
access a prover named “Alt-Ergo”, any version.

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{getanyaltergo}
   :end-before: END{getanyaltergo}

We could also get a specific version with

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{getaltergo200}
   :end-before: END{getaltergo200}

The next step is to obtain the driver associated to this prover. A
driver typically depends on the standard theories so these should be
loaded first.

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{getdriver}
   :end-before: END{getdriver}

We are now ready to call the prover on the tasks. This is done by a
function call that launches the external executable and waits for its
termination. Here is a simple way to proceed:

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{callprover}
   :end-before: END{callprover}

This way to call a prover
is in general too naive, since it may never return if the prover runs
without time limit. The function ``prove_task`` has an optional
parameter ``limit``, a record defined in module ``Call_provers``:

.. literalinclude:: ../src/driver/call_provers.ml
   :language: ocaml
   :start-after: BEGIN{resourcelimit}
   :end-before: END{resourcelimit}

where the field ``limit_time`` is the maximum allowed running time in
seconds, and ``limit_mem`` is the maximum allowed memory in megabytes.
The type ``prover_result`` is a record defined in module
``Call_provers``:

.. literalinclude:: ../src/driver/call_provers.ml
   :language: ocaml
   :start-after: BEGIN{proverresult}
   :end-before: END{proverresult}

with in particular the fields:

-  ``pr_answer``: the prover answer, explained below;

-  ``pr_time``: the time taken by the prover, in seconds.

A ``pr_answer`` is the sum type defined in module ``Call_provers``:

.. literalinclude:: ../src/driver/call_provers.ml
   :language: ocaml
   :start-after: BEGIN{proveranswer}
   :end-before: END{proveranswer}

corresponding to these kinds of answers:

-  ``Valid``: the task is valid according to the prover.

-  ``Invalid``: the task is invalid.

-  ``Timeout``: the prover exceeds the time limit.

-  ``OutOfMemory``: the prover exceeds the memory limit.

-  :samp:`Unknown {msg}`: the prover cannot determine if the task is
   valid; the string parameter *msg* indicates some extra
   information.

-  :samp:`Failure {msg}`: the prover reports a failure, it was unable
   to read correctly its input task.

-  ``HighFailure``: an error occurred while trying to call the prover,
   or the prover answer was not understood (none of the given regular
   expressions in the driver file matches the output of the prover).

Here is thus another way of calling the Alt-Ergo prover, on our second
task.

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{calltimelimit}
   :end-before: END{calltimelimit}

The output of our program is now as follows.

::

    On task 1, alt-ergo answers Valid (0.01s)
    On task 2, alt-ergo answers Valid in  0.01 seconds

Building Terms
--------------

An important feature of the functions for building terms and formulas is
that they statically guarantee that only well-typed terms can be
constructed.

Here is the way we build the formula ``2+2=4``. The main difficulty
is to access the internal identifier for addition: it must be retrieved
from the standard theory ``Int`` of the file :file:`int.why`.

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{buildfmla}
   :end-before: END{buildfmla}

An important point to notice as that when building the application
of ``+`` to the arguments, it is checked that the types are correct.
Indeed the constructor ``t_app_infer`` infers the type of the resulting
term. One could also provide the expected type as follows.

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{buildtermalt}
   :end-before: END{buildtermalt}

When building a task with this formula, we need to declare that we use
theory ``Int``:

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{buildtaskimport}
   :end-before: END{buildtaskimport}

Building Quantified Formulas
----------------------------

To illustrate how to build quantified formulas, let us consider the
formula :math:`\forall x:int. x \cdot x \geq 0`. The first step is to obtain
the symbols from ``Int``.

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{quantfmla1}
   :end-before: END{quantfmla1}

The next step is to introduce the variable *x* with the type ``int``.

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{quantfmla2}
   :end-before: END{quantfmla2}

The formula :math:`x \cdot x \geq 0` is obtained as in the previous example.

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{quantfmla3}
   :end-before: END{quantfmla3}

To quantify on *x*, we use the appropriate smart constructor as
follows.

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{quantfmla4}
   :end-before: END{quantfmla4}

Building Theories
-----------------

We illustrate now how one can build theories. Building a theory must be
done by a sequence of calls:

-  creating a theory “under construction”, of type ``Theory.theory_uc``;

-  adding declarations, one at a time;

-  closing the theory under construction, obtaining something of type
   ``Theory.theory``.

Creation of a theory named ``My_theory`` is done by

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{buildth1}
   :end-before: END{buildth1}

First let us add formula 1 above as a goal:

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{buildth1}
   :end-before: END{buildth1}

Note that we reused the goal identifier
``goal_id1`` that we already defined to create task 1 above.

Adding formula 2 needs to add the declarations of predicate variables A
and B first:

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{buildth3}
   :end-before: END{buildth3}

Adding formula 3 is a bit more complex since it uses integers, thus it
requires to “use” the theory ``int.Int``. Using a theory is indeed not a
primitive operation in the API: it must be done by a combination of an
“export” and the creation of a namespace. We provide a helper function
for that:

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{buildth4}
   :end-before: END{buildth4}

Addition of formula 3 is then

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{buildth5}
   :end-before: END{buildth5}

Addition of goal 4 is nothing more complex:

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{buildth6}
   :end-before: END{buildth6}

Finally, we close our theory under construction as follows.

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{buildth7}
   :end-before: END{buildth7}

We can inspect what we did by printing that theory:

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{printtheory}
   :end-before: END{printtheory}

which outputs

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
as follows:

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{splittheory}
   :end-before: END{splittheory}

Note that the tasks are returned in reverse order, so we
reverse the list above.

We can check our generated tasks by printing them:

.. literalinclude:: ../examples/use_api/logic.ml
   :language: ocaml
   :start-after: BEGIN{printalltasks}
   :end-before: END{printalltasks}

One can run provers on those tasks exactly as we did above.

Operations on Terms and Formulas, Transformations
-------------------------------------------------

The following code illustrates a simple recursive functions of formulas.
It explores the formula and when a negation is found, it tries to push
it down below a conjunction, a disjunction or a quantifier.

.. literalinclude:: ../examples/use_api/transform.ml
   :language: ocaml
   :start-after: BEGIN{negate}
   :end-before: END{negate}

The following illustrates how to turn such an OCaml function into a
transformation in the sense of the Why3 API. Moreover, it registers that
transformation to make it available for example in Why3 IDE.

.. literalinclude:: ../examples/use_api/transform.ml
   :language: ocaml
   :start-after: BEGIN{register}
   :end-before: END{register}

The directory :file:`src/transform` contains the code for the many
transformations that are already available in Why3.

Proof Sessions
--------------

See the example :file:`examples/use_api/create_session.ml` of the
distribution for an illustration on how to manipulate proof sessions
from an OCaml program.

ML Programs
-----------

One can build WhyML programs starting at different steps of the WhyML
pipeline (parsing, typing, VC generation). We present here two choices.
The first is to build an untyped syntax trees, and then call the Why3
typing procedure to build typed declarations. The second choice is to
directly build the typed declaration. The first choice use concepts
similar to the WhyML language but errors in the generation are harder to
debug since they are lost inside the typing phase, the second choice use
more internal notions but it is easier to pinpoint the functions wrongly
used.

Untyped syntax tree
~~~~~~~~~~~~~~~~~~~

The examples of this section are available in the file
:file:`examples/use_api/mlw_tree.ml` of the distribution.

The first step is to build an environment as already illustrated in
:numref:`sec.api.callingprovers`, and open the OCaml module ``Ptree`` (“parse tree”)
which contains most of the OCaml functions we need in this section.

.. literalinclude:: ../examples/use_api/mlw_tree.ml
   :language: ocaml
   :start-after: BEGIN{buildenv}
   :end-before: END{buildenv}

Each of our example programs will build a module.
Let us consider the Why3 code.

.. literalinclude:: ../examples/use_api/mlw_tree.ml
   :language: whyml
   :start-after: BEGIN{source1}
   :end-before: END{source1}

The Ocaml code that programmatically builds it is as follows.

.. literalinclude:: ../examples/use_api/mlw_tree.ml
   :language: ocaml
   :start-after: BEGIN{code1}
   :end-before: END{code1}

Most of the code is not using directly the ``Ptree`` constructors but
instead makes uses of the helper functions that are given below. Notice
``mk_ident`` which builds an identifier (``Ptree.ident``) without any
attributes nor any location and ``use_import`` which lets us import some
other modules and in particular the ones from the standard library. At
the end, our module is no more than the identifier and a list of two
declarations (``Ptree.decl list``).

.. literalinclude:: ../examples/use_api/mlw_tree.ml
   :language: ocaml
   :start-after: BEGIN{helper1}
   :end-before: END{helper1}

We want now to build a program equivalent to the following code in
concrete Why3 syntax.

.. literalinclude:: ../examples/use_api/mlw_tree.ml
   :language: whyml
   :start-after: BEGIN{source2}
   :end-before: END{source2}

The OCaml code that programmatically build this Why3 function is as
follows.

.. literalinclude:: ../examples/use_api/mlw_tree.ml
   :language: ocaml
   :start-after: BEGIN{code2}
   :end-before: END{code2}

We want now to build a program equivalent to the following code in
concrete Why3 syntax.

.. literalinclude:: ../examples/use_api/mlw_tree.ml
   :language: whyml
   :start-after: BEGIN{source3}
   :end-before: END{source3}

We need to import the ``ref.Ref`` module first. The rest is similar to
the first example, the code is as follows.

.. literalinclude:: ../examples/use_api/mlw_tree.ml
   :language: ocaml
   :start-after: BEGIN{code3}
   :end-before: END{code3}

The next example makes use of arrays.

.. literalinclude:: ../examples/use_api/mlw_tree.ml
   :language: whyml
   :start-after: BEGIN{source4}
   :end-before: END{source4}

The corresponding OCaml code is as follows.

.. literalinclude:: ../examples/use_api/mlw_tree.ml
   :language: ocaml
   :start-after: BEGIN{code4}
   :end-before: END{code4}

Having declared all the programs we wanted to write, we can now close
the module and the file, and get as a result the set of modules of our
file, under the form of a map of module names to modules.

.. literalinclude:: ../examples/use_api/mlw_tree.ml
   :language: ocaml
   :start-after: BEGIN{getmodules}
   :end-before: END{getmodules}

We can then construct the proofs tasks for our module, and then try to
call the Alt-Ergo prover. The rest of that code is using OCaml functions
that were already introduced before.

.. literalinclude:: ../examples/use_api/mlw_tree.ml
   :language: ocaml
   :start-after: BEGIN{checkingvcs}
   :end-before: END{checkingvcs}

Typed declaration
~~~~~~~~~~~~~~~~~

The examples of this section are available in the file
:file:`examples/use_api/mlw_expr.ml` of the distribution.

The first step to build an environment as already illustrated in
:numref:`sec.api.callingprovers`.

.. literalinclude:: ../examples/use_api/mlw_expr.ml
   :language: ocaml
   :start-after: BEGIN{buildenv}
   :end-before: END{buildenv}

To write our programs, we need to import some other modules from the
standard library integers and references. The only subtleties is to get logic
functions from the logical part of the modules
``mod_theory.Theory.th_export`` and the program functions from ``mod_export``.

.. literalinclude:: ../examples/use_api/mlw_expr.ml
   :language: ocaml
   :start-after: BEGIN{code2_import}
   :end-before: END{code2_import}

We want now to build a program equivalent to the following code in
concrete Why3 syntax.

.. literalinclude:: ../examples/use_api/mlw_expr.ml
   :language: whyml
   :start-after: BEGIN{source2}
   :end-before: END{source2}

The OCaml code that programmatically build this Why3 function is as follows.

.. literalinclude:: ../examples/use_api/mlw_expr.ml
   :language: ocaml
   :start-after: BEGIN{code2}
   :end-before: END{code2}

Having declared all the programs we wanted to write, we can now create the
module and generate the VCs.

.. literalinclude:: ../examples/use_api/mlw_expr.ml
   :language: ocaml
   :start-after: BEGIN{createmodule}
   :end-before: END{createmodule}

We can then construct the proofs tasks for our module, and then try to
call the Alt-Ergo prover. The rest of that code is using OCaml
functions that were already introduced before.

.. literalinclude:: ../examples/use_api/mlw_expr.ml
   :language: ocaml
   :start-after: BEGIN{checkingvcs}
   :end-before: END{checkingvcs}

.. _sec.ce_api:

Generating counterexamples
--------------------------

That feature is presented in details in :numref:`sec.idece`, which should
be read first. The counterexamples can also be generated using the API.
The following explains how to change the source code (mainly adding
attributes) in order to display counterexamples and how to parse the
result given by Why3. To illustrate this, we will adapt the examples
from :numref:`sec.prop_form` to display counterexamples.

Attributes and locations on identifiers
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

For variables to be used for counterexamples they need to contain an
attribute called ``model_trace`` and a location. The ``model_trace`` attribute
states the name the user wants the variable to be named in the output of
the counterexamples pass. Usually, people put a reference to their
program AST node in this attribute; this helps them to parse and display
the results given by Why3. The locations are also necessary as every
counterexamples values with no location will not be displayed. For example,
an assignment of the source language such as the following will probably
trigger the creation of an ident (for the left value) in a user
subsequent tasks:

::

    x := !y + 1

This means that the ident generated for :math:`x` will hold both a
``model_trace`` and a location.

The example becomes the following:

.. literalinclude:: ../examples/use_api/counterexample.ml
   :language: ocaml
   :start-after: BEGIN{ce_declarepropvars}
   :end-before: END{ce_declarepropvars}

In the above, we defined a
proposition ident with a location and a ``model_trace``.

Attributes in formulas
~~~~~~~~~~~~~~~~~~~~~~

Now that variables are tagged, we can define formulas. To define a goal
formula for counterexamples, we need to tag it with the
``vc:annotation`` attribute. This attribute is automatically added when
using the VC generation of Why3, but on a user-built task, this needs to
be added. We also need to add a location for this goal. The following is
obtained for the simple formula linking ``A`` and ``B``:

.. literalinclude:: ../examples/use_api/counterexample.ml
   :language: ocaml
   :start-after: BEGIN{ce_adaptgoals}
   :end-before: END{ce_adaptgoals}

Note: the transformations used for counterexamples will create new
variables for each variable occurring inside the formula tagged by
``vc:annotation``. These variables are duplicates located at the VC
line. They allow giving all counterexample values located at that VC
line.

Counterexamples output formats
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Several output formats are available for counterexamples. For users who
want to pretty-print their counterexamples values, we recommend to use
the JSON output as follows:

.. literalinclude:: ../examples/use_api/counterexample.ml
   :language: ocaml
   :start-after: BEGIN{ce_callprover}
   :end-before: END{ce_callprover}

.. _sec.infer-loop-api:

Infering loop invariants
------------------------

This section describes how to use the Why3 API to infer loop
invaiants. For more information about the inference of loop invariants
refer to :numref:`sec.installinferloop`. The example from this section
can be found in the Why3 source code ``examples/use_api/infer.ml``.

Let us start by defining a environment required to parse and type
check a program, as discussed in the previous sections.

.. literalinclude:: ../examples/use_api/infer.ml
   :language: ocaml
   :start-after: BEGIN{buildenv}
   :end-before: END{buildenv}

Now, we define a function that given a path for a file and an
environment, returns a collection of typed modules corresponding to the
top level modules declared in the file.

.. literalinclude:: ../examples/use_api/infer.ml
   :language: ocaml
   :start-after: BEGIN{parsefile}
   :end-before: END{parsefile}

It is now possible to infer loop invariants using the module
``Infer_ai`` that provides the following interface.

.. code-block:: whyml

    module type Inv_gen = sig
      val infer_loop_invariants:
        ?widening:int -> Env.env -> Pmodule.pmodule -> Pmodule.pmodule
    end

    module Make (D: Domain.DOMAIN) : Inv_gen

    module InvGenPolyhedra : Inv_gen
    module InvGenBox       : Inv_gen
    module InvGenOct       : Inv_gen

The interface provides a module type ``Inv_gen`` containing only a
function that receives a *widening* value (by default it is set to 3),
an environment, and a typed Why3 module, and returns the same Why3
module with the inferred loop invariants. Three instances of
``Inv_gen`` are provided: ``InvGenPolyhedra``, ``InvGenBox``, and
``InvGenOct``. Each one of these instances imposes the obvious
abstract interpretation domain, respectively *Polyhedra*, *Box*, and
*Oct*. Other modules, possibly using other domains can be created
using the ``Make`` functor.

Putting these pieces together, it is now possible to create a function
that parses, type checks and infers invariants for a given Why3
file. The function below receives a widening value, some flag
indicating the desired domain to be used, and a path for a file, and
outputs the result to the standard output.

.. literalinclude:: ../examples/use_api/infer.ml
   :language: ocaml
   :start-after: BEGIN{main}
   :end-before: END{main}

The complete example is in ``examples/use_api/infer.ml``, and it
allows the domain and the widening value to be selected from the
command line arguments.
