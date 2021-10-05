open Why3

(* This unit serves to
   - store the proof results which should be output at the end;
   - output them in JSON format.

   The output format is:

     file = { "error"        : string,
              "internal"     : bool,
              "session_dir" : string,
              "warnings"     : list string,
              "results"      : list result }

   The "error", "internal", "session_dir" and "warnings" fields are optional.
   If the "error" field is present, the "results" and "warnings" fields will be
   empty; if the "error" field is not present, the "results" field contains the
   list of proof results.

   If the "error" field is present, some error happened and the value of that
   field contains the reason for it. The "internal" field is present and
   meaningful only if the "error" field is present. If the "internal" field is
   present and set to "true", the error is an internal error which exhibits
   some misbehavior of the tool. If the field is absent or set to "false", the
   error should be interpreted as a misuse of the tool (e.g. invalid
   command-line options).

   The "warnings" field is optional. If present, it contains a list of warnings
   that occured during execution of gnatwhy3.

   The "session_dir" field is always present if "error" is not present. It
   contains the session directory information for this run of gnatwhy3.


     result = { "id"             : int,
                "reason"         : string,
                "result"         : bool,
                "extra_info"     : extra_info,
                "vc_file"        : string,
                "editor_cmd"     : string,
                "check_tree"     : list goal,
                "cntexmp"        : cntexmp_rec
                }

   The field "id" contains the id of the VC. The field "reason" identifies the
   kind of the VC, such as "overflow_check" etc. The field "result" tells if
   the VC has been proved or not. The field "extra_info" specifies more
   precisely the part of the VC (see below). The fields "vc_file" and
   "editor_cmd" are both optional and should be present at the same time. If
   present, "vc_file" contains the name of a VC file to be used for manual
   proof, and "editor_cmd" the command to spawn for an external editor for this
   VC.

     extra_info = { "node" : int,
                    "inline" : int }

  The "node" information of the extra_info type contains the node of the Ada
  expression which represents the unproved part of the VC (0 indicates no such
  node could be obtained). If this node was obtained by inlining symbols inside
  why3, the "inline" field is set to a non-zero value, otherwise it is set to
  0. If the "inline" node is positive, it contains the Ada node that
  corresponds to the expression prior to inlining.

  The counter example information is stored in the cntexmp field. At the top
  level, this is a mapping from file names to linesentry record.

     cntexmp_rec = { [filename : linesentry] }

  A linesentry is a mapping from linenumbers to line information. A linenumber
  is always a string. Usually the strings are integer values saved as strings,
  but the special value "vc_line" is also used.

     linesentry = { [ linenumber : list lineentry ] }

     lineentry = { "kind"  : string,
                   "name"  : string,
                   "value" : string }

  Possible values for "kind" are
   - "variable"
   - "error_message"
   - "old"
   - "result"

   The field "proof_attempts" basically contains a copy of the session
   tree in JSON format. It's a tree structure whose nodes are goals,
   transformations and proof attempts:

   goal = { "transformations" : list trans,
            pa : proof_attempt }

   trans = { [transname : goal] }

   proof_attempt = { [prover : infos ] }

   infos = { time : float,
             steps : integer,
             result : string }

   *)

type prover_stat =
  {
    mutable count     : int;
    mutable max_time  : float;
    mutable max_steps : int;
  }

type stats = prover_stat Whyconf.Hprover.t

type result_info =
  | Proved of stats * int * int
  (* extra information about the run. The first integer is the number of
     subgoals proven by transformations (except trivial_true).
     The second integer is the number of subgoals proven by trivial_true. *)
  | Not_Proved of
      Gnat_expl.extra_info *     (* VC Info for the unproved goal *)
      (Model_parser.model * Check_ce.rac_result option) option *
                                 (* counterexample model and result from
                                    giant-step RAC result *)
      (string * string) option   (* for manual provers, pair of
                                    (vc_file, editor_cmd) *)

val register : Gnat_expl.check -> Json_base.json -> result_info -> unit
(* [register check check_tree info] registers a proof result,
   represented by [info] for a given [check]. The [check_tree] is a
   json object encoding the session tree of the check. *)

val print_messages : unit -> unit
(* print all messages that have been registered so far. Also
   print the result file. *)

val add_warning : ?loc:Loc.position -> string -> unit
