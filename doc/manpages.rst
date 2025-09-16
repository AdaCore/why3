.. _chap.manpages:

The Why3 Tools
==============

.. program:: why3

This chapter details the usage of each of the command-line tools
provided by the Why3 environment. The main command is :program:`why3`; it acts
as an entry-point to all the features of Why3. It is invoked as follows:

::

    why3 [general options...] <command> [specific options...]

The following commands are available:

:why3:tool:`config`
    Manage the user's configuration, including the detection of
    installed provers.

:why3:tool:`doc`
    Render a WhyML file as HTML.

:why3:tool:`execute`
    Perform a symbolic execution of a WhyML file.

:why3:tool:`extract`
    Generate an OCaml program corresponding to a WhyML file.

:why3:tool:`ide`
    Provide a graphical interface to display goals and to run provers
    and transformations on them.

:why3:tool:`pp`
    Pretty-print WhyML definitions in various output formats.

:why3:tool:`prove`
    Read a WhyML input file and call provers, on the command-line.

:why3:tool:`realize`
    Generate the skeleton of an interactive proof for a WhyML file.

:why3:tool:`replay`
    Replay the proofs stored in a session, for regression test
    purposes.

:why3:tool:`session`
    Dump various information from a proof session, and possibly
    modify it.

:why3:tool:`show`
    Show all the currently registered formats, printers, transformations, etc.

:why3:tool:`wc`
    Give some token statistics about a WhyML file.

:why3:tool:`bench`
    Run provers on all proof attempts in the given session which have
    not been run yet, or whose result is obsolete. Typically to be
    used after `why3 session create` or `why3 session update`.

The commands accept a common subset of command-line options. In
particular, option :option:`--help` displays the usage and options.

.. option:: -L <dir>, --library=<dir>

   Add ``<dir>`` in the load path, to search for theories.

.. option:: --no-stdlib

   Do not add the standard library to the loadpath.

.. option:: --no-load-default-plugins

   Do not load the plugins from the standard path.

.. option:: -C <file>, --config=<file>

   Read the configuration from the given file. See :numref:`sec.whyconffile`.

.. option:: --extra-config=<file>

   Read additional configuration from the given file. See :numref:`sec.whyconffile`.

.. option:: --list-debug-flags

   List all the known debug flags. Flags marked by a star are those
   enabled by option :option:`--debug-all`.

.. option:: --debug-all

   Enable all the debug flags that do not change the behavior.

.. option:: --debug=<flag>,...

   Set some specific debug flags. See also :numref:`sec.debug` for
   a description of some of those flags.

.. option:: --print-datadir

   Print the location of non-binary data (modules, etc).

.. option:: --print-libdir

   Print the location of binary components (plugins, etc).

.. option:: --help

   Display the usage and the exact list of options for the given tool.

The following environment variables are recognized.

.. envvar:: WHY3CONFIG

   Indicate where to find the :file:`why3.conf` file. Can be overwritten using
   the :option:`--config` option.

.. envvar:: WHY3LIB

   Indicate where to find the Why3 library, which contains the
   dynamically loaded libraries and plugins for Why3. Setting this
   environment variable overrides the default value, or any other
   value set on the :file:`why3.conf` file (field `libdir` of section
   `[main]`). The default value is set at the compilation time of Why3
   (see :file:`src/config.sh.in` in Why3 sources), typically
   :file:`/usr/local/lib/why3` on Unix operating systems, unless Why3
   was compiled in relocatable mode (option `--enable-relocation` of
   script `configure`) when in that case it will be the directory
   where Why3 binary lies, concatenated with `lib/why3`. See also the
   option :option:`--print-libdir`.

.. envvar:: WHY3DATA

   Indicate where to find the Why3 architecture-independent data,
   which contains in particular the standard library. Setting this
   environment variable overrides the default value, or any other
   value set on the :file:`why3.conf` file (field `datadir` of section
   `[main]`). The default value is set at the compilation time of Why3
   (see :file:`src/config.sh.in` in Why3 sources), typically
   :file:`/usr/local/share/why3` on Unix operating systems, unless
   Why3 was compiled in relocatable mode (option `--enable-relocation`
   of script `configure`) when in that case it will be the directory
   where Why3 binary lies, concatenated with `share/why3`. See also the
   option :option:`--print-datadir`.


.. index:: configuration file
.. why3:tool:: config
.. _sec.why3config:

The ``config`` Command
----------------------

.. program:: why3 config

Why3 must be configured to access external provers. Typically, this is
done by running :why3:tool:`why3 config detect`. This command must be run
every time a new prover is installed.

The provers known by Why3 are described in the
configuration file :file:`provers-detection-data.conf` of the Why3 data
directory (e.g., :file:`/usr/local/share/why3`). Advanced users may try to modify
this file to add support for detection of other provers. (In that case,
please consider submitting a new prover configuration on the bug
tracking system.)

The result of prover detection is stored in the user's configuration file
(see :numref:`sec.whyconffile`). Only the version of the provers is
stored; the actual configuration of the provers, shortcuts, strategies,
and editors, are regenerated at each startup of a Why3. This
configuration can be inspected with the command :why3:tool:`why3 config
show`.

If a supported prover is not automatically recognized by
:why3:tool:`why3 config detect`, the command :why3:tool:`why3 config
add-prover` can be used to add it. Advanced users may also manually
insert extra `[prover]` sections in their configuration file. Notice
that in such a case, if a detected prover has exactly the same name,
version and alternative as a user-defined prover, then the
user-defined prover is taken and the detected one is
ignored. Similarly, if a user-defined shortcut clahes with a shortcut
of a detected prover, then the shortcut is chsen to denote the
user-defined prover and not the detect one.

The available subcommands are as follows:

:why3:tool:`config add-prover`
   Manually register a prover.

:why3:tool:`config detect`
   Automatically detect installed provers and register them.

:why3:tool:`config list-provers`
   List the provers registered in :file:`why3.conf`.

:why3:tool:`config list-supported-provers`
   List the names of all supported provers.

:why3:tool:`config show`
   Show the expanded version of the configuration file.

Only the first two commands modify the configuration file.

.. why3:tool:: config add-prover

Command ``add-prover``
~~~~~~~~~~~~~~~~~~~~~~

This commands adds a prover to the configuration. It is invoked as follows.

::

   why3 config add-prover <name> <file> [<shortcut>]

Argument *name* is the name of the prover, as listed by
command :why3:tool:`why3 config list-supported-provers` and as found in
file :file:`provers-detection-data.conf`.

If the argument *shortcut* is present, it is used as the shortcut for
invoking the prover.

For example, to add an Alt-Ergo
executable :file:`/home/me/bin/alt-ergo-trunk` with shortcut ``new-ae``,
one can type

::

   why3 config add-prover Alt-Ergo /home/me/bin/alt-ergo-trunk new-ae

Manually added provers are stored in the configuration file under
``[partial_prover]`` sections with a field ``manual = true``.

.. why3:tool:: config detect

Command ``detect``
~~~~~~~~~~~~~~~~~~

This command automatically detects the installed provers that are
supported by Why3. It also creates a configuration file if none exists.

Automatically detected provers are stored in the configuration file under
``[partial_prover]`` sections.

.. why3:tool:: config list-provers

Command ``list-provers``
~~~~~~~~~~~~~~~~~~~~~~~~

This command lists the names, versions, and alternatives of all the
provers present in :file:`why3.conf`. Those are the values expected by
:option:`why3 prove --prover`.

.. why3:tool:: config list-supported-provers

Command ``list-supported-provers``
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command lists the names of all supported provers, as used for
command :why3:tool:`why3 config add-prover`.

.. why3:tool:: config show

Command ``show``
~~~~~~~~~~~~~~~~

This command shows the expanded version of the configuration file. In
particular, all the ``[partial_prover]`` sections are expanded into
complete ``[prover]`` sections. Automatically generated ``[strategy]``
sections are also shown.

.. why3:tool:: prove
.. _sec.why3prove:

The ``prove`` Command
---------------------

.. program:: why3 prove

Why3 is primarily used to call provers on goals contained in an input
file. By default, such a file must be written in WhyML language
(extension :file:`.mlw`). However, a dynamically loaded plugin can register
a parser for some other format of logical problems, e.g., TPTP or SMT-LIB.

The :why3:tool:`prove` command executes the following steps:

#. Parse the command line and report errors if needed.

#. Read the configuration file using the priority defined in
   :numref:`sec.whyconffile`.

#. Load the plugins mentioned in the configuration. It will not stop if
   some plugin fails to load.

#. Parse and typecheck the given files using the correct parser in order
   to obtain a set of Why3 theories for each file. It uses the filename
   extension or the :option:`--format` option to choose among the
   available parsers. Command :why3:tool:`why3 show formats` lists the
   registered parsers. WhyML modules are turned into theories containing
   verification conditions as goals.

#. Extract the selected goals inside each of the selected theories into
   tasks. The goals and theories are selected using options
   :option:`--goal` and :option:`--theory`. Option :option:`--theory` applies to
   the previous file appearing on the command line. Option :option:`--goal`
   applies to the previous theory appearing on the command line. If no
   theories are selected in a file, then every theory is considered as
   selected. If no goals are selected in a theory, then every goal is
   considered as selected.

#. Apply the transformations requested with :option:`--apply-transform`
   in their order of appearance on the command line.
   Command :why3:tool:`why3 show transformations` lists the known
   transformations; plugins can register more of them.

#. If the option :option:`--sub-goal` is provided, only the sub-goals that
   correspond to the given line number (and explanation) are retained after
   applying the transformations.

#. Apply the driver selected with the :option:`--driver` option, or the
   driver of the prover selected with the :option:`--prover` option.
   Command :why3:tool:`why3 config list-provers` lists the provers
   that appear in the configuration file.

#. If option :option:`--prover` is given, call the selected prover on each
   generated task and print the results. If option :option:`--driver` is
   given, print each generated task using the format specified in the
   selected driver.

#. Derive a validated counterexample using runtime-assertion checking, if option
   :option:`--check-ce` is given and the selected prover generated a
   counterexample.

Prover Results
~~~~~~~~~~~~~~

The provers can give the following output:

Valid
    The goal is proved in the given context.

Unknown
    The prover has stopped its search.

Timeout
    The prover has reached the time limit.

OutOfMemory
    The prover has reached the memory limit.

StepLimitExceeded
    The prover has reached the steps limit.

Failure
    The prover has reported a failure.

HighFailure
    An error occurred during the call to the prover,
    or no other answer match the output of the prover.

Invalid
    The prover knows the goal cannot be proved.

.. _sec.proveoptions:

Options
~~~~~~~

.. option:: -F <format>, --format=<format>

   Select the given input format.

.. option:: -T <theory>, --theory=<theory>

   Focus on the given theory. If the argument is not qualified, the
   theory is searched in the input file.

.. option:: -G <goal>, --goal=<goal>

   Focus on the given goal. The goal is searched in the theory given
   by :option:`--theory`, if any. Otherwise, it is searched in the
   toplevel namespace of the input file.

.. option:: -a <transform>, --apply-transform=<transform>

   Apply the given transformation to the goals.

.. option:: -g [<file>][:<line>][@<expl>], --sub-goal=[<file>][:<line>][@<expl>]

   Retain only sub-goals at the given location (and with the given explanation)
   after applying the transformations. The file can be omitted and defaults to
   the input file. E.g., ``why3 prove --sub-goal=:123@Precondition file.mlw`` to
   prove only the preconditions in line 123 in file ``file.mlw``.The explanation
   of a goal is shown the normal output of ``why3 prove``: ::

       File "file.mlw", line 123, characters 0-1:
       Sub-goal <expl> from goal f'vc.

.. option:: -P <prover>, --prover=<prover>

   Execute the given prover on the goals.

.. option:: -D <driver>, --driver=<driver>

   Output the tasks obtained by applying the given driver to the
   goals. <driver> should be either a file path with extension
   :file:`.drv` or a single name :file:`d` without extension. Names
   without extensions are meant to denote the file :file:`d.drv` from
   the driver directory of Why3. File names with extension are search
   both from the current directory and in the driver directory of
   Why3.  This option conflicts with :option:`--prover`.

.. option:: --extra-expl-prefix=<s>

   Specify *s* as an additional prefix for labels that denotes VC
   explanations. The option can be used several times to specify
   several prefixes.

.. option:: --timelimit=<sec>

   Set the prover's time limit.
   By default, the limit is set to 10 seconds.
   Setting this option to 0 second disables the time limit.

.. option:: --stepslimit=<steps>

   Set the prover's step limit.
   By default, there is no limit.

.. option:: --memlimit=<MiB>

   Set the prover's memory limit, in megabytes
   By default, there is no limit.

.. option:: --meta=<meta>[=<string>]

   Add a meta to every task.

.. option:: --print-theory

   Print selected theories.

.. option:: --print-namespace

   Print namespaces of selected theories.

.. option:: --check-ce

   Validate and categorize the counterexample using runtime-assertion
   checking, as proposed by Becker et al :cite:`becker21fide`. Only
   applicable when the prover selected by :option:`--prover` is
   configured to generate counterexamples.

.. option:: --rac-prover=<p>

   Use prover *p* for the runtime-assertion checking (with
   :option:`--check-ce`) during the validation of counterexamples, as
   described for :why3:tool:`execute`.

.. option:: --rac-timelimit=<sec>

   Time limit in seconds for RAC prover (with :option:`--check-ce`).

.. option:: --rac-steplimit=<steps>

   Step limit for RAC prover (with :option:`--check-ce`).

.. option:: --rac-try-negate

   Same option as for :why3:tool:`execute` (with :option:`--check-ce`)

.. option:: --parse-only

   Stop after parsing (same as ``--debug=parse_only``).

.. option:: --type-only

   Stop after type checking (same as ``--debug=type_only``).

.. option:: --ce-log-verbosity=<lvl>

   Verbosity level for interpretation log of counterexample model
   returned by the prover.
   By default, the level is set to 4.

   - When level = 1, print only imported values.
   - When level = 2, also print log information about execution of function calls.
   - When level = 3, also print log information about execution of loops.
   - When level = 4, also print log information about termination of executions.
   - When level = 5, also print log information about initialization of global variables.

.. option:: --json

   Print output in JSON format.

.. option:: --color

   Print output with colors.

Generating potential counterexamples
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

When the selected prover has alternative `counterexample`, the prover is
instructed to generate a model, and Why3 elaborates the model into a potential
counterexample. The potential counterexample associates source locations and
variables to values. The generation and display of potential counterexamples is
presented in details in :numref:`sec.idece`.

Generating validated and categorized counterexamples
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A validated counterexample can be requested using option :option:`--check-ce`.
The validated counterexample is derived by executing the relevant function using
runtime assertion checking (RAC) [#ce-split]_. The potential counterexample
serves as an oracle for values that are not or cannot be computed in the RAC
execution (e.g., arguments to the relevant function or ``any``-expressions).

The validated counterexample is a trace of the RAC execution, with one of the
following categorizations (see :cite:`becker21fide` for details):

*The program does not comply to the verification goal:*

   The validated counterexample is the trace of an execution that resulted in
   the violation of an assertion.

*The contracts of some function or loop are underspecified:*

   The validated counterexample is the trace of an abstract execution, which
   resulted in the violation of an assertion. In an abstract execution, function
   calls and loops are not executed. Their results and assignments are instead
   chosen according to the contracts (function postcondition or loop invariants)
   by picking them from the potential counterexample.

*The program does not comply to the verification goal, or the contracts of some loop or function are too weak:*

   Either of the above cases.

*Sorry, we don't have a good counterexample for you :(*

   The RAC execution did not violate any assertions. The execution trace does not
   constitute a validated counterexample, and the potential counterexample is invalid, so
   no counterexample is shown.

*The counterexample model could not be verified:*

   The validated counterexample could not be derived because RAC execution was incomplete.
   The potential counterexample is instead shown with a warning.

.. [#ce-split] The relevant function is generally only defined, when the
   counterexample is not generated for the VC of the complete program, for
   example by applying a split transformation using
   ``--apply-transform=split_vc``.

.. why3:tool:: ide
.. _sec.ideref:

The ``ide`` Command
-------------------

.. program:: why3 ide

The basic usage of the GUI is described by the tutorial of
:numref:`sec.gui`. The command-line options are the common options
detailed in introduction to this chapter, plus the specific option
already described for the :why3:tool:`prove` command in
:numref:`sec.proveoptions`.

.. .. option:: --extra-expl-prefix=<s>

At least one anonymous argument must be specified on the command line.
More precisely, the first anonymous argument must be the directory of
the session. If the directory does not exist, it is created. The other
arguments should be existing files that are going to be added to the
session. For convenience, if there is only one anonymous argument, it
can be an existing file and in this case the session directory is
obtained by removing the extension from the file name.

.. _sec.ideref.session:

Session
~~~~~~~

The session stores the transformations you performed on each verification
condition, as well as the provers you ran. Such a proof attempt records the
complete name of a prover (name, version, optional attribute), the time
limit and memory limit given, and the result of the prover. The result
of the prover is the same as when you run the :why3:tool:`prove` command. It
contains the time taken and the state of the proof:

Valid
    The task is valid according to the prover. The goal is considered
    proved.

Invalid
    The task is invalid.

Timeout
    the prover exceeded the time limit.

OufOfMemory
    The prover exceeded the memory limit.

Unknown
    The prover cannot determine if the task is valid. Some additional
    information can be provided.

Failure
    The prover reported a failure.

HighFailure
    An error occurred while trying to call the prover, or the prover
    answer was not understood.

Additionally, a proof attempt can have the following attributes:

:index:`obsolete`
    The prover associated to that proof attempt has not been run on the
    current task, but on an earlier version of that task. You need to
    replay the proof attempt, run the prover with the current task of
    the proof attempt, in order to update the answer of the prover and
    remove this attribute.

:index:`detached`
    The proof attempt is not associated to a proof task anymore. The
    reason might be that a proof goal disappeared, or that there is a
    syntax or typing error in the current file, that makes all nodes
    temporarily detached until the parsing error is fixed. Detached
    nodes of the session tree are kept until they are explicitly
    removed, either using a remove command or the clean command. They
    can be reused, as any other nodes, using the copy/paste operation.

Generally, proof attempts are marked obsolete just after the start of
the user interface. Indeed, when you load a session in order to modify
it (not with :why3:tool:`why3 session info` for instance), Why3 rebuilds the goals
to prove by using the information provided in the session. If you modify
the original file (:file:`.mlw`) or if the transformations have changed (new
version of Why3), Why3 will detect that. Since the provers might answer
differently on these new proof obligations, the corresponding proof
attempts are marked obsolete.

Context Menu
~~~~~~~~~~~~

The left toolbar that was present in former versions of Why3 is now
replaced by a context menu activited by clicking the right mouse button,
while cursor is on a given row of the proof session tree.

*Prover list*
    List the detected provers. Note that you can hide some provers
    of that list using :menuselection:`File --> Preferences`, tab :guilabel:`Provers`.

*Strategy list*
    List the set of known strategies.

:guilabel:`Edit`
    Start an editor on the selected task.

:guilabel:`Replay valid obsolete proofs`
    All proof nodes below the selected nodes that are obsolete but whose
    former status was Valid are replayed.

:guilabel:`Replay all obsolete proofs`
    All proof nodes below the selected nodes that are obsolete are
    replayed.

:guilabel:`Clean node`
    Remove any unsuccessful proof attempt for which there is another
    successful proof attempt for the same goal.

:guilabel:`Remove node`
    Remove a proof attempt or a transformation.

:guilabel:`Interrupt`
    Cancel all the proof attempts currently scheduled or running.

Global Menus
~~~~~~~~~~~~

Menu :menuselection:`File`
    :menuselection:`--> Add File to session`
        Add a file to the current proof session.

    :menuselection:`--> Preferences`
        Open a window for modifying preferred configuration parameters,
        see details below.

    :menuselection:`--> Save session`
        Save current session state on disk. The policy to decide when
        to save the session is configurable, as described in the
        preferences below.

    :menuselection:`--> Save files`
        Save edited source files on disk.

    :menuselection:`--> Save session and files`
        Save both current session state and edited files on disk.

    :menuselection:`--> Save all and Refresh session`
        Save session and edited files, and refresh the current session
        tree.

    :menuselection:`--> Quit`
        Exit the GUI.

Menu :menuselection:`Tools`
    :menuselection:`--> Strategies`
        Provide a set of actions that are performed on the
        selected goals:

        :menuselection:`--> Split VC`
            Split the current goal into subgoals.

        :menuselection:`--> Auto level 0`
            Perform a basic proof search strategy that applies a few provers
            on the goal with a short time limit.

        :menuselection:`--> Auto level 1`
            This is the same as level 0 but with a longer time limit.

        :menuselection:`--> Auto level 2`
            This strategy first applies a few provers on the goal
            with a short time limit, then splits the goal and tries
            again on the subgoals.

        :menuselection:`--> Auto level 3`
            This strategy is more elaborate than level 2. It attempts
            to apply a few transformations that are typically
            useful. It also tries the provers with a larger time
            limit. It also tries more provers.

        A more detailed description of strategies is given in
        :numref:`sec.strategies`, as well as a description on how to
        design strategies of your own.

    :menuselection:`--> Provers`
        Provide a menu item for each detected prover. Clicking on such
        an item starts the corresponding prover on the selected goals.
        To start a prover with a different time limit, you may either
        change the default time limit in the Preferences, or using the
        text command field and type the prover name followed by the time
        limit.

    :menuselection:`--> Transformations`
        Give access to all the known transformations.

    :menuselection:`--> Edit`
        Start an editor on the selected task.

        For automatic provers, this shows the file sent to the
        prover.

        For interactive provers, this also makes it possible to add or modify the
        corresponding proof script. The modifications are saved, and can
        be retrieved later even if the goal was modified.

    :menuselection:`--> Replay valid obsolete proofs`
        Replay all the obsolete proofs below the current node whose
        former state was Valid.

    :menuselection:`--> Replay all obsolete proofs`
        Replay all the obsolete proofs below the current node.

    :menuselection:`--> Clean node`
        Remove any unsuccessful proof attempt for which there is
        another successful proof attempt for the same goal.

    :menuselection:`--> Remove node`
        Remove a proof attempt or a transformation.

    :menuselection:`--> Mark obsolete`
        Mark all the proof as obsolete. This makes it possible to replay every
        proof.

    :menuselection:`--> Interrupt`
        Cancel all the proof attempts currently scheduled or running.

    :menuselection:`--> Bisect`
        Reduce the size of the context for the the selected
        proof attempt, which must be a Valid one.

    :menuselection:`--> Focus`
        Focus the tree session view to the current node.

    :menuselection:`--> Unfocus`
        Undo the Focus action.

    :menuselection:`--> Copy`
        Mark the proof sub-tree for copy/past action.

    :menuselection:`--> Paste`
        Paste the previously selected sub-tree under the current node.

Menu :menuselection:`View`
    :menuselection:`--> Enlarge font`
        Select a large font.

    :menuselection:`--> Reduce font`
        Select a smaller font.

    :menuselection:`--> Collapse proved goals`
        Close all the rows of the tree view that are proved.

    :menuselection:`--> Expand all`
        Expand all the rows of the tree view.

    :menuselection:`--> Collapse under node`
        Close all the rows of the tree view under the given node that
        are proved.

    :menuselection:`--> Expand below node`
        Expand the children below the current node.

    :menuselection:`--> Expand all below node`
        Expand the whole subtree of the current node.

    :menuselection:`--> Go to parent node`
        Move to the parent of the current node.

    :menuselection:`--> Go to first child`
        Move to the first child of the current node.

    :menuselection:`--> Select next unproven goal`
        Move to the next unproven goal after the current node.

Menu :menuselection:`Help`
    :menuselection:`--> Legend`
        Explain the meaning of the various icons.

    :menuselection:`--> About`
        Give some information about this software.

Command-line interface
~~~~~~~~~~~~~~~~~~~~~~

Between the top-right zone containing source files and task, and the
bottom-right zone containing various messages, a text input field allows
the user to invoke commands using a textual interface (see
:numref:`fig.gui1`). The ``help`` command displays a basic list of
available commands. All commands available in the menus are also
available as a textual command. However the textual interface allows for
much more possibilities, including the ability to invoke transformations
with arguments.

Key shortcuts
~~~~~~~~~~~~~

-  Save session and files: :kbd:`Control-s`

-  Save all and refresh session: :kbd:`Control-r`

-  Quit: :kbd:`Control-q`

-  Enlarge font: :kbd:`Control-plus`

-  Reduce font: :kbd:`Control-minus`

-  Collapse proved goals: :kbd:`!`

-  Collapse current node: :kbd:`-`

-  Expand current node: :kbd:`+`

-  Copy: :kbd:`Control-c`

-  Paste: :kbd:`Control-v`

-  Select parent node: :kbd:`Control-up`

-  Select next unproven goal: :kbd:`Control-down`

-  Change focus to command line: :kbd:`Return`

-  Edit: :kbd:`e`

-  Replay: :kbd:`r`

-  Clean: :kbd:`c`

-  Remove: :kbd:`Delete`

-  Mark obsolete : :kbd:`o`

Preferences Dialog
~~~~~~~~~~~~~~~~~~

The preferences dialog allows you to customize various settings. They
are grouped together under several tabs.

Note that there are to different buttons to close that dialog. The
:guilabel:`Close` button will make modifications of any of these settings
effective only for the current run of the GUI. The :guilabel:`Save&Close` button
will save the modified settings in Why3 configuration file, to make them
permanent.

Tab :guilabel:`General`
    allows one to set various general settings.

    -  the limits set on resource usages:

       -  the time limit given to provers, in seconds

       -  the memory given to provers, in megabytes

       -  the maximal number of simultaneous provers allowed to run in
          parallel

    -  option to disallow source editing within the GUI

    -  the policy for saving sessions:

       -  always save on exit (default): the current state of the proof
          session is saving on exit

       -  never save on exit: the current state of the session is never
          saved automatically, you must use menu :menuselection:`File --> Save session`

       -  ask whether to save: on exit, a popup window asks whether you
          want to save or not.

Tab :guilabel:`Appearance`
    -  show full task context: by default, only the local context of
       formulas is shown, that is only the declarations comming from the
       same module

    -  show attributes in formulas

    -  show coercions in formulas

    -  show source locations in formulas

    -  show time and memory limits for each proof

    Finally, it is possible to choose an alternative icon set, provided,
    one is installed first.

Tab :guilabel:`Editors`
    allows one to customize the use of external editors for proof
    scripts.

    -  The default editor to use when the button is pressed.

    -  For each installed prover, a specific editor can be selected to
       override the default. Typically if you install the Coq prover,
       then the editor to use will be set to “CoqIDE” by default, and
       this dialog allows you to select the Emacs editor and its
       `Proof General <http://proofgeneral.inf.ed.ac.uk/>`_  mode
       instead.

Tab :guilabel:`Provers`
    allows to select which of the installed provers one wants to see in
    the context menu.

Tab :guilabel:`Uninstalled provers policies`
    presents all the decision previously taken for missing provers, as
    described in :numref:`sec.uninstalledprovers`. You can remove any
    recorded decision by clicking on it.

.. _sec.idece:

Displaying Counterexamples
~~~~~~~~~~~~~~~~~~~~~~~~~~

Why3 provides some support for extracting a potential counterexample
from failing proof attempts, for provers that are able to produce a
*counter-model* of the proof task. Why3 attempts to turn this
counter-model into values for the free variables of the original Why3
input. Currently, this is supported for CVC4 prover version at least
1.5, CVC5, Z3 prover version at least 4.4.0 and Alt-Ergo version at
least 2.6.0.

The generation of counterexamples is fully integrated in Why3 IDE. The
recommended usage is to first start a prover normally, as shown in
:numref:`fig.ce_example0_p1`, and then click on the status icon for the
corresponding proof attempt in the tree. Alternatively, one can use the
key shortcut :kbd:`G` or type ``get-ce`` in the command entry. The result can
be seen on :numref:`fig.ce_example0_p2`: the same prover but with the
alternative *counterexamples* is run. The resulting counterexample is
displayed in two different ways. First, it is displayed in the :guilabel:`Task` tab of
the top-right window, at the end of the text of the task, under the form
of a list of pairs “variable = value”, ordered by the line number of the
source code in which that variable takes that value. Second, it is
displayed in the *Counterexample* tab of the bottom right window, this time interleaved
with the code, as shown in :numref:`fig.ce_example0_p2`.


.. %EXECUTE bin/why3 ide --batch="down;down;type cvc4;wait 2;down;snap -crop 1024x600+0+0 doc/images/ce_example0_p1.png" doc/cedoc.mlw
.. %EXECUTE bin/why3 ide --batch="down;down;type cvc4;wait 2;down;type get-ce;wait 2;down;faketype get-ce;snap -crop 1024x600+0+0 doc/images/ce_example0_p2.png" doc/cedoc.mlw

.. _fig.ce_example0_p1:

.. figure:: images/ce_example0_p1.png
   :alt: Failing execution of CVC4

   Failing execution of CVC4

.. _fig.ce_example0_p2:

.. figure:: images/ce_example0_p2.png
   :alt: Counterexamples display for CVC4

   Counterexamples display for CVC4

Notes on format of displayed values
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The counterexamples can contain values of various types.

-  Integer or real variables are displayed in decimal.

-  Bitvectors are displayed in decimal and binary notations.

-  Integer range types are displayed in a specific notation showing
   their projection to integers.

-  Floating-point numbers are displayed both under a bitvector
   representation and an hexadecimal value. The special values
   ``+oo``, ``-oo``, and ``NaN`` may occur too.

-  Values from algebraic types and record types are displayed as in the
   Why3 syntax.

-  Map values are displayed in a specific syntax detailed below.

To detail the display of map values, consider the following code with a
trivially false postcondition:

.. code-block:: whyml

    use int.Int
    use map.Map

    let ghost test_map (ghost x : (map int int)) : map int int
      ensures { result[0] <> result[1] }
     =
       Map.set x 0 3

Executing CVC4 with the “counterexamples” alternative on goal will
trigger counterexamples:

.. code-block:: whyml

    let ghost test_map (ghost x : (map int int)) : map int int
    (* x : int -> int = [|1 => 3; _ => 0|]; *)
        ensures { result[0] <> result[1] }
        (* result : int -> int = [|0 => 3; 1 => 3; _ => 0|] *)
       =
         Map.set x 0 3
         (* result : int -> int = [|0 => 3; 1 => 3; _ => 0|];
            result of call at line 7, characters 5-18 :
              int
              ->
              int = [|0 => 3; 1 => 3; _ => 0|] *)

The notation for map is the one for function literals presented in
:numref:`sec.functionliterals`. This shows that setting the
parameter ``x`` to a map that has value 3 for index 1 and zero for all
other indices is a counterexample. We can check that this negates the
``ensures`` clause.

Known limitations
^^^^^^^^^^^^^^^^^

The counterexamples are known not to work on the following
non-exhaustive list (which is undergoing active development):

-  Code containing type polymorphism is often a problem due to the bad
   interaction between monomorphisation techniques and counterexamples.
   This is current an issue in particular for the ``Array`` module of the
   standard library.

.. todo::

   complete this list

More information on the implementation of counterexamples in Why3 can be
found in :cite:`hauzar16sefm` and
in :cite:`dailler18jlamp`. For the producing counterexamples
using the Why3 API, see :numref:`sec.ce_api`.

.. why3:tool:: replay
.. _sec.why3replay:

The ``replay`` Command
----------------------

.. program:: why3 replay

The :program:`why3 replay` command is meant to execute the proofs stored in a Why3
session file, as produced by the IDE. Its main purpose is to play
non-regression tests. For instance, :file:`examples/regtests.sh` is a script
that runs regression tests on all the examples.

The tool is invoked in a terminal or a script using

::

    why3 replay [options] <project directory>

The session file :file:`why3session.xml` stored in the given directory is
loaded and all the proofs it contains are rerun. Then, all the
differences between the information stored in the session file and the
new run are shown.

Nothing is shown when there is no change in the results, whether the
considered goal is proved or not. When all the proof are done, a summary
of what is proved or not is displayed using a tree-shape pretty print,
similar to the IDE tree view after doing :menuselection:`View --> Collapse proved goals`. In
other words, when a goal, a theory, or a file is fully proved, the
subtree is not shown.

Obsolete proofs
~~~~~~~~~~~~~~~

When some proof attempts stored in the session file are :index:`obsolete`, the
replay is run anyway, as with the replay button in the IDE. Then, the
session file will be updated if both

-  all the replayed proof attempts give the same result as what is
   stored in the session,

-  all the goals are proved.

In other cases, you can use the IDE to update the session, or use the
option :option:`--force` described below.

Exit code and options
~~~~~~~~~~~~~~~~~~~~~

The exit code is 0 if no difference was detected, 1 if there was. Other
exit codes mean some failure in running the replay.

Options are:

.. option:: -s

   Suppress the output of the final tree view.

.. option:: -q

   Run quietly (no progress info).

.. option:: --force

   Enforce saving the session, if all proof attempts replayed
   correctly, even if some goals are not proved.

.. option:: --obsolete-only

   Replay the proofs only if the session contains obsolete proof
   attempts.

.. option:: --smoke-detector[=none|top|deep]

   Try to detect if the context is self-contradicting (default: top).

.. option:: --prover=<prover>

   Restrict the replay to the selected provers only.

Smoke detector
~~~~~~~~~~~~~~

The smoke detector tries to detect if the context is self-contradicting
and, thus, that anything can be proved in this context. The smoke
detector can’t be run on an outdated session and does not modify the
session. It has three possible configurations:

``none``
    Do not run the smoke detector.

``top``
    The negation of each proved goal is sent with the same timeout to
    the prover that proved the original goal.

    ::

          Goal G : forall x:int. q x -> (p1 x \/ p2 x)

    becomes

    ::

          Goal G : ~ (forall x:int. q x -> (p1 x \/ p2 x))

    In other words, if the smoke detector is triggered, it means that
    the context of the goal ``G`` is self-contradicting.

``deep``
    This is the same technique as ``top`` but the negation is pushed
    under the universal quantification (without changing them) and under
    the implication. The previous example becomes

    ::

          Goal G : forall x:int. q x /\ ~ (p1 x \/ p2 x)

    In other words, the premises of goal ``G`` are pushed in the
    context, so that if the smoke detector is triggered, it means that
    the context of the goal ``G`` and its premises are
    self-contradicting. It should be clear that detecting smoke in that
    case does not necessarily means that there is a mistake: for
    example, this could occur in the WP of a program with an unfeasible
    path.

At the end of the replay, the name of the goals that triggered the smoke
detector are printed:

::

      goal 'G', prover 'Alt-Ergo 0.93.1': Smoke detected!!!

Moreover ``Smoke detected`` (exit code 1) is printed at the end if the
smoke detector has been triggered, or ``No smoke detected`` (exit code
0) otherwise.

.. why3:tool:: session
.. _sec.why3session:

The ``session`` Command
-----------------------

.. program:: why3 session

The :program:`why3 session` command makes it possible to extract information from
proof sessions on the command line, or even modify them to some extent.
The invocation of this program is done under the form

::

    why3 session <subcommand> [options] <session directories>

The available subcommands are as follows:

:why3:tool:`session info`
    Print information and statistics about sessions.

:why3:tool:`session latex`
    Output session contents in LaTeX format.

:why3:tool:`session html`
    Output session contents in HTML format.

:why3:tool:`session update`
    Update session contents.

:why3:tool:`session create`

    Create a new session containing the set of files given. In this
    particular case, the given arguments must be a set of source files
    and not session directories. The session directory name itself
    must be given with option `-o`.

The first three commands do not modify the sessions, whereas the fourth
on modify them, and the last one creates a new session.

.. why3:tool:: session info

Command ``info``
~~~~~~~~~~~~~~~~

.. program:: why3 session info

The :program:`why3 session info` command reports various informations about the
session, depending on the following specific options.

.. option:: --provers

   Print the provers that appear inside the session, one by line.

.. option:: --edited-files

   Print all the files that appear in the session as edited proofs.

.. option:: --session-stats

   Print proofs statistics for each given session, as detailed below.

.. option:: --provers-stats

   Print proofs statistics for used provers in all given sessions, as detailed below.

.. option:: --print0

   Separate the results of the options :option:`--provers` and
   :option:`--edited-files` by the null character ``\0`` instead of end of line
   ``\n``. That allows you to safely use (even if the filename contains
   space or carriage return) the result with other commands. For
   example you can count the number of proof line in all the coq edited
   files in a session with:

   .. code-block:: shell

        why3 session info --edited-files vstte12_bfs --print0 | xargs -0 coqwc

   or you can add all the edited files in your favorite repository
   with:

   .. code-block:: shell

        why3 session info --edited-files --print0 vstte12_bfs.mlw | \
            xargs -0 git add

.. option:: --graph=[all|hist|scatter]

   Produce Gnuplot files containing graphs with various comparisons of the
   provers in the session, and display them if :command:`gnuplot` is present in the
   system. If no option is specified, `all` is used.

   - ``all``: Output a line graph with each line representing the cumulative
     time taken by a prover on all goals, as function of the number of goals.
     Goals are ordered by shortest to longest relative to the prover.

   - ``hist``: For every pair of provers in the session, output a histogram
     representing the ratio between the time taken by each prover on each goal,
     sorted by ascending ratio. Also display the average ratio and the
     percentage of goals where one prover was faster.

   - ``scatter``: For every pair of provers in the session, output a graph where
     the `x` and `y` coordinates of each goal represent the time the two provers
     needed to prove it. Therefore, goals where the prover in the `x` axis was
     faster appear above the bisecting line of the graph area, and goals where
     the prover in the `y` axis was faster appear below the bisecting line.

Session Statistics
^^^^^^^^^^^^^^^^^^

The proof statistics given by option :option:`--session-stats` are as follows:

-  Number of goals: give both the total number of goals, and the number
   of those that are proved (possibly after a transformation).

-  Goals not proved: list of goals of the session which are not proved
   by any prover, even after a transformation.

-  Goals proved by only one prover: the goals for which there is only
   one successful proof. For each of these, the prover which was
   successful is printed. This also includes the sub-goals generated by
   transformations.

The proof statistics given by option :option:`--provers-stats` are
   statistics per prover, aggregated on all sessions given on the
   command ine. For each of the prover used in any of the sessions,
   the number of proof attempts is given, followed by the number of
   successful ones. This also includes the sub-goals generated by
   transformations. The respective minimum, maximum and average time
   and on average running time is shown. Beware that these time data
   are computed on the proof attempts *where the prover was successful*.

For example, here are the session statistics produced on the “hello
proof” example of :numref:`chap.starting`.

::

    == Number of root goals ==
      total: 3  proved: 2

    == Number of sub goals ==
      total: 2  proved: 1

    == Goals not proved ==
      +-- file [../hello_proof.why]
        +-- theory HelloProof
          +-- goal G2
            +-- transformation split_goal_right
              +-- goal G2.0

    == Goals proved by only one prover ==
      +-- file [../hello_proof.why]
        +-- theory HelloProof
          +-- goal G1: Alt-Ergo 2.1.0
          +-- goal G2
            +-- transformation split_goal_right
              +-- goal G2.1: Alt-Ergo 2.1.0
          +-- goal G3: Alt-Ergo 2.1.0

    == Statistics per prover: number of proof attempts, successful ones, time (minimum/maximum/average) in seconds ==
      Alt-Ergo 2.1.0                :     5     3   0.00   0.00   0.00
      Coq 8.11.2                    :     1     0   0.00   0.00   0.00

.. why3:tool:: session latex

Command ``latex``
~~~~~~~~~~~~~~~~~

.. program:: why3 session latex

The :program:`why3 session latex` command produces a summary of the replay under the form of a
tabular environment in LaTeX, one tabular for each theory, one per file.

The specific options are

.. option:: --style=<n>

   Set output style (1 or 2, default 1). Option ``--style=2`` produces
   an alternate version of LaTeX output, with a different layout of the
   tables.

.. option:: -o <dir>

   Indicate where to produce LaTeX files (default: the session
   directory).

.. option:: --longtable

   Use the ``longtable`` environment instead of ``tabular``.

.. option:: -e <elem>

   Produce a table for the given element, which is either a file, a
   theory or a root goal. The element must be specified using its path
   in dot notation, e.g., ``file.theory.goal``. The file produced is named
   accordingly, e.g., :file:`file.theory.goal.tex`. This option can be given
   several times to produce several tables in one run. When this option
   is given at least once, the default behavior that is to produce one
   table per theory is disabled.

Customizing LaTeX output
^^^^^^^^^^^^^^^^^^^^^^^^

The generated LaTeX files contain some macros that must be defined
externally. Various definitions can be given to them to customize the
output.

``\provername``
    macro with one parameter, a prover name.

``\valid``
    macro with one parameter, used where the corresponding prover
    answers that the goal is valid. The parameter is the time in
    seconds.

``\noresult``
    macro without parameter, used where no result exists for the
    corresponding prover.

``\timeout``
    macro without parameter, used where the corresponding prover reached
    the time limit.

``\explanation``
    macro with one parameter, the goal name or its explanation.

Here are some examples of macro definitions:

.. code-block:: latex

   \usepackage{xcolor}
   \usepackage{colortbl}
   \usepackage{rotating}

   \newcommand{\provername}[1]{\cellcolor{yellow!25}
   \begin{sideways}\textbf{#1}~~\end{sideways}}
   \newcommand{\explanation}[1]{\cellcolor{yellow!13}lemma \texttt{#1}}
   \newcommand{\transformation}[1]{\cellcolor{yellow!13}transformation \texttt{#1}}
   \newcommand{\subgoal}[2]{\cellcolor{yellow!13}subgoal #2}
   \newcommand{\valid}[1]{\cellcolor{green!13}#1}
   \newcommand{\unknown}[1]{\cellcolor{red!20}#1}
   \newcommand{\invalid}[1]{\cellcolor{red!50}#1}
   \newcommand{\timeout}[1]{\cellcolor{red!20}(#1)}
   \newcommand{\outofmemory}[1]{\cellcolor{red!20}(#1)}
   \newcommand{\noresult}{\multicolumn{1}{>{\columncolor[gray]{0.8}}c|}{~}}
   \newcommand{\failure}{\cellcolor{red!20}failure}
   \newcommand{\highfailure}{\cellcolor{red!50}FAILURE}

.. TODO: Restore screenshots of HelloProof.tex (style 1 and style 2)

.. why3:tool:: session html

Command ``html``
~~~~~~~~~~~~~~~~

.. program:: why3 session html

The :program:`why3 session html` command produces a summary of the proof session in HTML syntax.
There are two styles of output: ``table`` and ``simpletree``. The default is
``table``.

The file generated is named :file:`why3session.html` and is written in the
session directory by default (see option :option:`-o` to override this
default).

.. _fig.html:

.. figure:: images/hello_proof.png
   :alt: HTML table produced for the HelloProof example

   HTML table produced for the HelloProof example

The style ``table`` outputs the contents of the session as a table,
similar to the LaTeX output above. :numref:`fig.html` is the HTML table
produced for the ‘HelloProof’ example, as typically shown in a Web
browser. The gray cells filled with ``---`` just mean that the prover was
not run on the corresponding goal. Green background means the result was
“Valid”, other cases are in orange background. The red background for a
goal means that the goal was not proved.

The style ``simpletree`` displays the contents of the session under the
form of tree, similar to the tree view in the IDE. It uses only basic
HTML tags such as ``<ul>`` and ``<li>``.

Specific options for this command are as follows.

.. option:: --style=[simpletree|table]

   Set the style to use, among ``simpletree`` and ``table`` (default:
   ``table``).

.. option:: -o <dir>

   Set the directory where to output the produced files (``-`` for
   stdout). The default is to output in the same directory as the
   session itself.

.. option:: --context

   Add context around the generated code in order to allow direct
   visualization (header, css, etc.). It also adds in the output
   directory all the needed external files. It is incompatible with stdout
   output.

.. option:: --add_pp=<suffix>,<cmd>,<out_suffix>

   Set a specific pretty-printer for files with the given suffix.
   Produced files use *<out_suffix>* as suffix. *<cmd>* must
   contain ``%i`` which will be replaced by the input file and
   ``%o`` which will be replaced by the output file.

.. option:: --coqdoc

   use the :program:`coqdoc` command to display Coq proof scripts. This is
   equivalent to ``--add_pp=.v,coqdoc --no-index --html -o %o %i,.html``

.. why3:tool:: session update

Command ``update``
~~~~~~~~~~~~~~~~~~

.. program:: why3 session update

The :program:`why3 session update` command permits to modify the session
contents, depending on the following specific options.

.. option:: --rename-file=<src>:<dst>

   Rename the file *<src>* to *<dst>* in the session. The file *<src>*
   itself is also renamed to *<dst>* in the filesystem.

.. option:: --mark-obsolete

   Mark as obsolete all the proof attempts of the session. If a filter
   is provided by the options below, then only the proof attempts that
   match the filters are affected.

.. option:: --remove-proofs

   Remove all the proof attempts. If a filter is provided by the
   options below, then only the proof attempts that match the filters
   are affected.

.. option:: --add-provers=<provers>

   For each proof node of the session, add a new proof attempt for the specified provers.

.. option:: --filter-prover=<name>[,<version>[,<alternative>]]

   Select proof attempts with the given provers.

.. option:: --filter-obsolete[=[yes|no]]

   Select only (non-)obsolete proofs.

.. option:: --filter-proved[=[yes|no]]

   Selects only goals that are (not) proved.

.. option:: --filter-is-leaf[=[yes|no]]

   Select only goals that are leaves of the proof tree, i.e., do not
   have transformations, if yes.

.. option:: --filter-status=[valid|invalid|highfailure]

   Select proof attempts with the given status.

.. why3:tool:: session create

Command ``create``
~~~~~~~~~~~~~~~~~~

.. program:: why3 session create

The :program:`why3 session create` command creates a new session containing the
source files specified as arguments. Transformations and proofs attempts can be
added using the options below. No prover is started with this command, and one
should use the `why3 bench` command on the new session instead.

.. option:: -a <transformation>, --apply-transform=<transformation>

   Specify a transformation to be applied before the proof nodes are added (can
   be given several times to nest several transformations).

.. option:: -P <prover1:prover2...>, --prover=<prover1:prover2...>

   Specify provers to use for proof attempts added to the session.

.. option:: -o <output-dir>, --output-dir=<output-dir>

   Specify the session directory for the created session.

.. option:: -t <sec>, --timelimit=<sec>

   Specify the time limit for the added proof attempts.

.. option:: -s <steps>, --stepslimit=<steps>

   Specify the step limit for the added proof attempts.

.. option:: -m <MiB>, --memlimit=<MiB>

   Specify the memory limit, in megabytes, for the added proof attempts.

.. why3:tool:: doc
.. _sec.why3doc:

The ``doc`` Command
-------------------

.. program:: why3 doc

The :program:`why3 doc` command can produce HTML pages from Why3 source code. Why3 code for
theories or modules is output in preformatted HTML code. Comments are
interpreted in three different ways.

-  Comments starting with at least three stars are completed ignored.

-  Comments starting with two stars are interpreted as textual
   documentation. Special constructs are interpreted as described below.
   When the previous line is not empty, the comment is indented to the
   right, so as to be displayed as a description of that line.

-  Comments starting with one star only are interpreted as code
   comments, and are typeset as the code

Additionally, all the Why3 identifiers are typeset with links so that
one can navigate through the HTML documentation, going from some
identifier use to its definition.

Options
~~~~~~~

.. option:: -o <dir>, --output=<dir>

   Define the directory where to output the HTML files.

.. option:: --index

   Generate an index file :file:`index.html`. This is the default behavior
   if more than one file is passed on the command line.

.. option:: --no-index

   Prevent the generation of an index file.

.. option:: --title=<title>

   Set title of the index page.

.. option:: --stdlib-url=<url>

   Set a URL for files found in load path, so that links to
   definitions can be added.

Typesetting textual comments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Some constructs are interpreted:

-  :samp:`\\{{c} {text}}` interprets character *c* as some typesetting command:

   ``1``-``6``
       a heading of level 1 to 6 respectively

   ``h``
       raw HTML

-  :samp:`\`{code}\`` is a code escape: the text *code* is typeset as Why3 code.

A CSS file :file:`style.css` suitable for rendering is generated in the same
directory as output files. This CSS style can be modified manually,
since regenerating the HTML documentation will not overwrite an existing
:file:`style.css` file.

.. why3:tool:: pp
.. _sec.why3pp:

The ``pp`` Command
------------------

.. program:: why3 pp

This tool pretty-prints Why3 declarations into various forms. The kind of output is
specified using the ``--output`` option.

::

    why3 pp [--output=mlw|sexp|latex|dep] [--prefix=<prefix>] \
      <filename> <file>[[.<Module>].<object>] ...

.. option:: --output=<output>

   Set the output format, among the following:

   - ``mlw``: reformat WhyML source code.

   - ``sexp``: print the abstract syntax tree of a WhyML file (data-type from API module
     ``Ptree``) as a S-expression (enabled only when package ``ppx_sexp_conv`` is
     available at configuration time of Why3).

   - ``latex``: can be used to print some fragment of WhyML
     declarations. These include algebraic type definitions,
     direct definitions of logic symbols, and inductive definitions of
     logic predicates. Inductive definitions are formatted under the form of
     deduction rules, using the ``mathpartir`` package.

   - ``dep``: display module dependencies, under the form of a digraph
     using the ``dot`` syntax from the `GraphViz
     <https://www.graphviz.org/>`_ visualisation software.

.. option:: --prefix=<prefix>

   Set the prefix for LaTeX commands when using ``--output=latex``. The
   default prefix is ``WHY``.

For the LaTeX output, the typesetting of variables, record fields, and
functions can be configured by LaTeX commands. Dummy definitions of these
commands are printed in comments and have to be defined by the user.
Trailing digits and quotes are removed from the command names to reduce
the number of commands.

.. why3:tool:: execute
.. _sec.why3execute:

The ``execute`` Command
-----------------------

.. program:: why3 execute

Why3 can execute expressions in the context of a WhyML program (extension
:file:`.mlw`).

::

   why3 execute [options] <file> <expr>


`file` is a WhyML file, and `expr` is a WhyML expression. Using option
``--use=<M>`` the definitions from module `M` are added to the context for
executing `expr`. For example, the following command executes ``Mod1.f 42``
defined in ``myfile.mlw``:

.. code-block:: shell

   why3 execute myfile.mlw --use=Mod1 'f 42'

Upon completion of the execution, the value of the result is displayed
on the standard input. Additionally, values of the global mutable
variables modified by that function are displayed too.

See more details and examples of use in :numref:`sec.execute`.

Runtime assertion checking (RAC)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The execution can be instructed using option :option:`--rac` to check the
validity of the program annotations that are encountered during the execution.
This includes the validation of assertions, function contracts, and loop
invariants [#no-type-invars]_.

There are two strategies to check the validity of an annotation: First, the term
is reduced using the Why3 transformation ``compute_in_goal``. The annotation is
valid when the result of the reduction is `true` and invalid when the result is
`false`. When the transformation cannot reduce the term to a trivial term, and
when a RAC prover is given using option :option:`--rac-prover`, the prover is
used to verify the term.

When a program annotation is found to be wrong during the execution, the
execution stops and reports the contradiction. Normally, the execution continues
when an annotation cannot be checked (when the term can neither be reduced nor
proven), but fails when option `--rac-fail-cannot-check` is given.

Options
~~~~~~~

.. option:: --use=<Mod>

   Add the definitions from `Mod` to the execution context.

.. option:: --real=<emin>,<emax>,<prec>

   The interpreter handles real numbers using interval arithmetic with
   floating-point bounds.  This option sets the precision of those
   bounds using three parameters, respectively the minimal and maximal
   exponent, and the number of bits of mantissa. For example, the
   standard single-precision binary representation (32 bits) is set by
   parameters -148,128,24. The default is using long double-precision
   (128-bits) with parameters -16493,16384,113. Note that this feature
   is only available when Why3 has been compiled with MPFR support.

.. option:: --rac

   Check the validity of program annotations encountered during the execution.

.. option:: --rac-prover=<p>

   Use prover *p* for the checking formulas, when term reduction is
   insufficient (which is always tried first). The prover *p* is the
   name of a prover, with optional, comma-separated version number and
   alternative, e.g. ``Alt-Ergo,2.6.0``.

.. option:: --rac-timelimit=<sec>

   Time limit in seconds for RAC prover.

.. option:: --rac-memlimit=<MiB>

   Memory limit in megabytes for RAC prover.

.. option:: --rac-steplimit=<steps>

   Step limit for RAC prover.

.. option:: --rac-try-negate

   Try to decide the validity of a formula by negating the formula and
   the prover answer (if any), when the RAC prover is unable to decide
   the validity of the un-negated formula (see :cite:`becker21fide`).

.. option:: --rac-fail-cannot-check

   Instruct the RAC execution to fail when an annotation cannot be checked.
   Normally the execution continues normally when an annotation cannot be
   checked.

.. [#no-type-invars] RAC for type invariants aren't supported yet.

.. why3:tool:: extract
.. _sec.why3extract:

The ``extract`` Command
-----------------------

.. program:: why3 extract

The :program:`why3 extract` command can extract programs written using
the WhyML language (extension :file:`.mlw`) to some other programming
language. See also :numref:`sec.extract`.

The command accepts three different targets for extraction: a WhyML file,
a module, or a symbol (function, type, exception). To extract all the
symbols from every module of a file named :file:`f.mlw`, one should write

::

    why3 extract -D <driver> f.mlw

To extract only the symbols from module ``M`` of file :file:`f.mlw` in
directory ``<dir>``, one should write

::

    why3 extract -D <driver> -L <dir> f.M

To extract only the symbol ``s`` (a function, a type, or an exception)
from module ``M`` of file :file:`f.mlw`, one should write

::

    why3 extract -D <driver> -L <dir> f.M.s

Note the use of :option:`why3 -L`, when extracting either a module or a
symbol, in order to state where to look for file :file:`f.mlw`.

.. option:: -o <file|dir>

   Output extracted code to the given file (for :option:`--flat`) or
   directory (for :option:`--modular`).

.. option:: -D <driver>, --driver=<driver>

   Use the given driver.

.. option:: --flat

   Perform a flat extraction, *i.e.*, everything is extracted into
   a single file. This is the default behavior. If option :option:`-o` is
   omitted, the result of extraction is printed to the standard output.

.. option:: --modular

   Extract each module in its own, separate file. Option :option:`-o` is
   mandatory; it should be given the name of an existing directory. This
   directory will be populated with the resulting OCaml files.

.. option:: --recursive

    Recursively extract all the dependencies of the chosen entry point.
    This option is valid for both :option:`--modular` and :option:`--flat` options.

.. why3:tool:: realize
.. _sec.why3realize:

The ``realize`` Command
-----------------------

.. program:: why3 realize

Why3 can produce skeleton files for proof assistants that, once filled,
realize the given theories. If the output files already exist, Why3 tries
to update them instead of overwriting them, so as to preserve existing
realizations. See also :numref:`sec.realizations`.

.. option:: -D <driver>, --driver=<driver>

   Use the given prover driver to produce realizations.

.. option:: -F <format>, --format=<format>

   Select the given input format.

.. option:: -o <dir>, --output=<directory>

   Write the realizations to the given directory.

.. option:: -T <theory>, --theory=<theory>

   Select the given theory in the input file or in the library.

.. why3:tool:: show
.. _sec.why3show:

The ``show`` Command
--------------------

The :program:`why3 show` command can display various information about
Why3. Specific information is selected by the given subcommand:

::

   why3 show <subcommand>

.. why3:tool:: show attributes

Command ``attributes``
~~~~~~~~~~~~~~~~~~~~~~

This command lists the currently registered WhyML attributes. See
also :numref:`sec.attributes`.

.. why3:tool:: show formats

Command ``formats``
~~~~~~~~~~~~~~~~~~~

This command lists the currently registered input formats. See
also :option:`why3 prove --format`.

.. why3:tool:: show metas

Command ``metas``
~~~~~~~~~~~~~~~~~

This command lists the currently registered meta directives. See
also :numref:`sec.metas`.

.. why3:tool:: show printers

Command ``printers``
~~~~~~~~~~~~~~~~~~~~

This command lists the currently registered printers, which can be used
inside prover drivers. See also :numref:`sec.drivers`.

.. why3:tool:: show transformations

Command ``transformations``
~~~~~~~~~~~~~~~~~~~~~~~~~~~

This command lists the currently registered transformations. See
also :option:`why3 prove --apply-transform` and :numref:`sec.transformations`.

.. why3:tool:: wc
.. _sec.why3wc:

The ``wc`` Command
------------------

.. program:: why3 wc

Why3 can give some token statistics about WhyML source files.

.. option:: -l, --lines

   Count lines (default).

.. option:: -t, --tokens

   Count tokens.

.. option:: -f, --factor

   Print ratio of specification over code.

.. option:: -a, --do-not-skip-header

   Count heading comments as well.

.. why3:tool:: bench
.. _sec.why3bench:

The ``bench`` Command
----------------------

.. program:: why3 bench

The :program:`why3 bench` runs all proofs attempts of a session that have not
been tried. It saves the session periodically so that it can be interrupted and
resumed later.

::

    why3 bench [options] <session directory>

The session file :file:`why3session.xml` stored in the given directory is
loaded and all the proof attempt nodes it contains are run.

.. option:: -d <sec>, --delay=<sec>

   Set the delay between temporary session backups, in seconds. Default is 60.

.. option:: -f, --force

   Force to rerun all proof attempt nodes, even the ones that have been run
   before.
