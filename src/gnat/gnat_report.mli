open Why3

(* This unit serves to
   - store the proof results which should be output at the end;
   - output them in JSON format.

   The output format is:

     file = { "error"        : string,
              "internal"     : bool,
              "warnings"     : list string,
              "results"      : list result }

   The "error", "internal", "warnings" fields are optional.
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

     result = { "id"               : int,
                "check_kind"       : string,
                "result"           : bool,
                "extra_info"       : extra_info,
                "vc_file"          : string,
                "editor_cmd"       : string,
                "check_tree"       : list goal,
                "cntexmp"          : cntexmp_rec,
                "unproved_status"  : unproved_status
                }

   The field "id" contains the id of the VC. The field "check_kind" identifies the
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
  node could be obtained).
  The node in "node" may have been obtained by inlining symbols inside Why3.
  The "inline" field gives information about this as follows:
    0  - The node was not obtained via inlining
    >0 - The node was obtained by inlining, and the value is the Ada node prior
         to inlining
    -1 - The node was obtained by inlining, but we do not have info about the
         node prior to inlining

  The counter example information is stored in the cntexmp field. At the top
  level, this is a list of file names together with a modelentry record.

     cntexmp_rec  = list fileentry

     fileentry    = { "filename"  : string,
                      "model"     : modelentry }

  A modelentry is a list of lineentry records.
  The field "loc" is the line number. The field "is_vc_line" indicates whether
  the current line corresponds to the source code elements from which the VC
  originates.

     modelentry = list lineentry

     lineentry  = { "loc" : string,
                    "is_vc_line"  : bool,
                    "model_elements"  : elemententry}

     elemententry   = { "attrs" : string,
                        "kind"  : string,
                        "name"  : string,
                        "value" : string }

  Possible values for "kind" are
   - "variable"
   - "error_message"
   - "old"
   - "result"

   The field "check_tree" basically contains a copy of the session
   tree in JSON format. It's a tree structure whose nodes are goals,
   transformations and proof attempts:

   goal = { "transformations" : list trans,
            pa : proof_attempt }

   trans = { [transname : goal] }

   proof_attempt = { [prover : infos ] }

   infos = { time : float,
             steps : integer,
             result : string }

  The "unproved_status" field contains a summary of the reasons why
  the goal could not be proved. It is a record with the following fields:
      unproved_status = { "status" : string,
                          "time"   : bool,
                          "steps"  : bool,
                          "memory" : bool}
  The "status" field contains one of the following strings:
    - "gave_up"  : the prover gave up
    - "limit"    : the prover reached some resource limit
    - "unknown"  : the prover status is unknown (e.g., no proof attempt
                   was made, or the goal was proved)
  The "time", "steps" and "memory" fields are booleans indicating whether
  the corresponding resource limit was reached.
   *)

type prover_stat =
  {
    mutable count     : int;
    mutable max_time  : float;
    mutable max_steps : int;
  }

type stats = prover_stat Whyconf.Hprover.t

type result_info =
  | Proved of stats * int
  (* extra information about the run. The integer is the number of
     subgoals proven by transformations. *)
  | Not_Proved of
      Gnat_expl.extra_info *     (* VC Info for the unproved goal *)
      (Model_parser.model * Check_ce.rac_result option) list *
                                 (* counterexample models and their
                                    giant-step RAC result *)
      (string * string) option *  (* for manual provers, pair of
                                    (vc_file, editor_cmd) *)
      Gnat_expl.unproved_status

val register : Gnat_expl.check -> Json_base.json -> result_info -> unit
(* [register check check_tree info] registers a proof result,
   represented by [info] for a given [check]. The [check_tree] is a
   json object encoding the session tree of the check. *)

val print_messages : unit -> unit
(* print all messages that have been registered so far. Also
   print the result file. *)

val add_warning : ?loc:Loc.position -> string -> unit
