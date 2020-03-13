.. _chap.starting:

Getting Started
===============

Hello Proofs
------------

The first step in using Why3 is to write a suitable input file. When one
wants to learn a programming language, one starts by writing a basic
program. Here is our first Why3 file, which is the file
:file:`examples/logic/hello_proof.why` of the distribution. It contains a
small set of goals.

.. literalinclude:: ../examples/logic/hello_proof.why
   :language: whyml

Any declaration must occur inside a theory, which is in that example
called ``HelloProof``. It contains three goals named
``G1``, ``G2``, ``G3``. The first two are basic propositional goals,
whereas the third involves some integer arithmetic, and thus it requires
to import the theory of integer arithmetic from the Why3 standard
library, which is done by the ``use`` declaration above.

We don’t give more details here about the syntax and refer to
:numref:`chap.whyml` for detailed explanations. In the following, we
show how this file is handled in the Why3 GUI (:numref:`sec.gui`) then
in batch mode using the :program:`why3` executable (:numref:`sec.batch`).

.. %EXECUTE rm -rf doc/hello_proof/
.. %EXECUTE cp examples/logic/hello_proof.why doc/

.. _sec.gui:

Getting Started with the GUI
----------------------------

The graphical interface allows to browse into a file or a set of files,
and check the validity of goals with external provers, in a friendly
way. This section presents the basic use of this GUI. Please refer to
:numref:`sec.ideref` for a more complete description.

.. %EXECUTE bin/why3 ide --batch "snap doc/images/gui-1.png" doc/hello_proof.why

.. _fig.gui1:

.. figure:: images/gui-1.png
   :alt: The GUI when started the very first time.

   The GUI when started the very first time.

The GUI is launched on the file above as follows:

::

    why3 ide hello_proof.why

When the GUI is started for the first time, you should get a window that
looks like the screenshot of :numref:`fig.gui1`. The left part is a tree
view that allows to browse inside the theories. In this tree view, we
have a structured view of the file: this file contains one theory,
itself containing three goals.

.. %EXECUTE bin/why3 ide --batch "type next;view task;snap -crop 1024x384+0+0 doc/images/gui-2.png" doc/hello_proof.why

.. _fig.gui2:

.. figure:: images/gui-2.png
   :alt: The GUI with goal ``G1`` selected.

   The GUI with goal ``G1`` selected.

In :numref:`fig.gui2`, we clicked on the row corresponding to goal
``G1``. The *task* associated with this goal is then displayed on
the top-right pane. The corresponding part of the input file is shown
when clicking the rightmost tab of that pane.

Calling provers on goals
~~~~~~~~~~~~~~~~~~~~~~~~

You are now ready to call provers on the goals. (If not done yet, you
must perform prover autodetection using :option:`why3 config --detect-provers`.)
A prover is
selected using the context menu (right-click). This prover is then
called on the goal selected in the tree view. You can select several
goals at a time, either by using multi-selection (typically by clicking
while pressing the :kbd:`Shift` or :kbd:`Control` key) or by selecting the parent theory or the
parent file.

Let us now select the theory “HelloProof” and run the Alt-Ergo prover.
After a short time, you should get the display of :numref:`fig.gui3`.

.. %EXECUTE bin/why3 ide --batch "type alt-ergo;view source;wait 3;type next;snap -crop 1024x384+0+0 doc/images/gui-3.png" doc/hello_proof.why

.. _fig.gui3:

.. figure:: images/gui-3.png
   :alt: The GUI after running the Alt-Ergo prover on each goal.

   The GUI after running the Alt-Ergo prover on each goal.

Goals ``G1`` and ``G3`` are now marked with a green “checked”
icon in the status column. This means that these goals have been proved
by Alt-Ergo. On the contrary, goal ``G2`` is not proved; it remains
marked with a question mark. You could attempt to prove ``G2``
using another prover, though it is obvious here it will not succeed.

Applying transformations
~~~~~~~~~~~~~~~~~~~~~~~~

Instead of calling a prover on a goal, you can apply a transformation to
it. Since ``G2`` is a conjunction, a possibility is to split it into
subgoals. You can do that by selecting :guilabel:`Split VC` in the
context menu. Now you have two subgoals, and you can try again a prover
on them, for example Alt-Ergo. We already have a lot of goals and proof
attempts, so it is a good idea to close the sub-trees which are already
proved. This can be done by the menu :menuselection:`View --> Collapse
proved goals`, or even better by its shortcut :kbd:`!`. You
should see now what is displayed on :numref:`fig.gui4`.

.. %EXECUTE bin/why3 ide --batch "type alt-ergo;wait 3;type next;type split_vc;wait 1;type up;type alt-ergo;wait 3;type next;snap -crop 1024x384+0+0 doc/images/gui-4.png;save;wait 1" doc/hello_proof.why

.. _fig.gui4:

.. figure:: images/gui-4.png
   :alt: The GUI after splitting goal ``G2``.

   The GUI after splitting goal ``G2``.

The first part of goal ``G2`` is still unproved. As a last resort,
we can try to call the Coq proof assistant, by selecting it in the
context menu. A new sub-row appear for Coq, and the Coq proof editor is
launched. (It is ``coqide`` by default; see :numref:`sec.ideref` for
details on how to configure this). You get now a regular Coq file to
fill in, as shown on :numref:`fig.coqide`. Please be mindful of the
comments of this file. They indicate where Why3 expects you to fill the
blanks. Note that the comments themselves should not be removed, as they
are needed to properly regenerate the file when the goal is changed. See
:numref:`sec.coq` for more details.

.. %EXECUTE bin/why3 ide --batch "type next;type coq;wait 1;save;wait 1" doc/hello_proof.why

.. _fig.coqide:

.. figure:: images/coqide.png
   :alt: CoqIDE on subgoal 1 of ``G2``.

   CoqIDE on subgoal 1 of ``G2``.

Of course, in that particular case, the goal cannot be proved since it
is not valid. The only thing to do is to fix the input file, as
explained below.

Modifying the input
~~~~~~~~~~~~~~~~~~~

You can edit the source file, using the corresponding tab in the
top-right window of the GUI. Let us assume we change the goal
``G2`` by replacing the first occurrence of ``true`` by ``false``, e.g.,

.. code-block:: whyml

   goal G2 : (false -> false) /\ (true \/ false)

We can refresh the goals using menu :menuselection:`File --> Save all and
Refresh session`, or the shortcut :kbd:`Control-r`. We get the tree view
shown on :numref:`fig.gui5`.

.. %EXECUTE sed -i -e 's/true -> false/false -> false/' doc/hello_proof.why
.. %EXECUTE bin/why3 ide --batch "type next;type expand;snap -crop 1024x384+0+0 doc/images/gui-5.png" doc/hello_proof.why

.. _fig.gui5:

.. figure:: images/gui-5.png
   :alt: File reloaded after modifying goal ``G2``.

   File reloaded after modifying goal ``G2``.

The important feature to notice first is that all the previous proof
attempts and transformations were saved in a database — an XML file
created when the Why3 file was opened in the GUI for the first time.
Then, for all the goals that remain unchanged, the previous proofs are
shown again. For the parts that changed, the previous proofs attempts
are shown but marked with “(:index:`obsolete`)” so that you know the results are
not accurate. You can now retry to prove all what remains unproved using
any of the provers.

Replaying obsolete proofs
~~~~~~~~~~~~~~~~~~~~~~~~~

Instead of pushing a prover's button to rerun its proofs, you can
*replay* the existing but obsolete proof attempts, using
menu :menuselection:`Tools --> Replay valid obsolete proofs`. Notice that
replaying can be done in batch mode, using the :why3:tool:`why3 replay`
command (see :numref:`sec.why3replay`) For example, running the replayer
on the ``hello_proof`` example is as follows (assuming ``G2`` still is
``(true -> false) /\ (true \/ false)``).

.. code-block:: console

    > why3 replay hello_proof
     2/3 (replay OK)
       +--file ../hello_proof.why: 2/3
          +--theory HelloProof: 2/3
             +--goal G2 not proved

The last line tells us that no differences were detected between the
current run and the run stored in the XML file. The tree above reminds
us that ``G2`` is not proved.

Cleaning
~~~~~~~~

You may want to clean some of the proof attempts, e.g., removing the
unsuccessful ones when a project is finally fully proved. A proof or
a transformation can be removed by selecting it and using
menu :menuselection:`Tools --> Remove node` or the :kbd:`Delete` key.
Menu :menuselection:`Tools --> Clean node` or shortcut :kbd:`C` perform
an automatic removal of all proofs attempts that are unsuccessful, while
there exists a successful proof attempt for the same goal. Beware that
there is no way to undo such a removal.

.. _sec.batch:

Getting Started with the Why3 Command
-------------------------------------

The :why3:tool:`why3 prove` command makes it possible to check the validity of goals
with external provers, in batch mode. This section presents the basic
use of this tool. Refer to :numref:`sec.why3prove` for a more complete
description of this tool and all its command-line options.

The very first time you want to use Why3, you should proceed with
autodetection of external provers. On the command line, this is done as
follows:

::

    why3 config --detect

This prints some information messages on what detections are attempted.
To know which provers have been successfully detected, you can do as
follows.

.. code-block:: console

    > why3 --list-provers
    Known provers:
      Alt-Ergo 1.30
      CVC4 1.5
      Coq 8.6

The first word of each line is a unique identifier for the associated
prover. We thus have now the three provers Alt-Ergo :cite:`ergo`,
CVC4 :cite:`barrett11cade`, and Coq :cite:`CoqArt`.

Let us assume that we want to run Alt-Ergo on the HelloProof example.
The command to type and its output are as follows, where the :option:`why3 prove -P`
option is followed by the unique prover identifier (as shown by
:option:`why3 --list-provers` option).

.. code-block:: console

    > why3 prove -P Alt-Ergo hello_proof.why
    hello_proof.why HelloProof G1: Valid (0.00s, 1 steps)
    hello_proof.why HelloProof G2: Unknown (other) (0.01s)
    hello_proof.why HelloProof G3: Valid (0.00s, 1 steps)

Unlike the Why3 GUI, the command-line tool does not save the proof
attempts or applied transformations in a database.

We can also specify which goal or goals to prove. This is done by giving
first a theory identifier, then goal identifier(s). Here is the way to
call Alt-Ergo on goals ``G2`` and ``G3``.

.. code-block:: console

    > why3 prove -P Alt-Ergo hello_proof.why -T HelloProof -G G2 -G G3
    hello_proof.why HelloProof G2 : Unknown: Unknown (0.01s)
    hello_proof.why HelloProof G3 : Valid (0.01s)

Finally, a transformation to apply to goals before proving them can be
specified. To know the unique identifier associated to a transformation,
do as follows.

.. code-block:: console

    > why3 --list-transforms
    Known non-splitting transformations:
      [...]

    Known splitting transformations:
      [...]
      split_goal_right

Here is how you can split the goal ``G2`` before calling Simplify
on the resulting subgoals.

.. code-block:: console

    > why3 prove -P Alt-Ergo hello_proof.why -a split_goal_right -T HelloProof -G G2
    hello_proof.why HelloProof G2: Unknown (other) (0.01s)
    hello_proof.why HelloProof G2: Valid (0.00s, 1 steps)

:numref:`sec.transformations` gives the description of the various
transformations available.

.. %EXECUTE rm -r doc/hello_proof.why doc/hello_proof/
