open Why3

(* This unit serves to
   - store the proof results which should be output at the end;
   - output them in JSON fomat.

   The output format is the following:

     file = { "error"    : string,
              "internal" : bool,
              "warnings" : list string,
              "results"  : list result }

   The "error", "internal" and warnings fields are optional.  If the error
   field is present, the "results" and "warnings" field will be empty. If the
   "error" field is not present, the "results" field contains the list of proof
   results.

   If the "error" field is present, some error happened and the value of that
   field contains the reason for it. The "internal" field is present and
   meaningful only of the "error" field ir present. If the "internal" field is
   present and set to "true", the error is an internal error which exhibits
   some misbehavior of the tool. If the field absent or set to "false", the
   error should be interpreted as a misuse of the tool (e.g. invalid command
   line options).

   The "warnings" field is optional. If present, it contains a list of warnings
   that occured during execution of gnatwhy3.


     result = { "id"         : int,
                "reason"     : string,
                "result"     : bool,
                "extra_info" : int,
                "trace_file" : string,
                "vc_file"    : string,
                "editor_cmd" : string
                }

   The field "id" contains the id of the VC. The field "reason" identifies the
   kind of the VC, such as "overflow_check" etc. The field "result" tells if
   the VC has been proved or not. The field "extra_info" specifies more
   precisely the part of the VC, it may be "0" if no extra information is
   availabe. The field "trace_file" is optional and contains the name of a file
   which contains some explanation of the VC. The fields "vc_file" and
   "editor_cmd" are both optional and should be present at the same time. If
   present, "vc_file" contains the name of a VC file to be used for manual
   proof, and "editor_cmd" the command to spawn for an external editor for this
   VC.
   *)

val register :
     Gnat_expl.check
  -> Task.task option                  (* task of the last goal *)
  -> Call_provers.prover_result option (* extra information about the run *)
  -> bool                              (* if the goal was proved or not *)
  -> (string * string) option           (* (for manual provers) *)
                                       (* pair of (vc_file, editor_cmd) *)
  -> string                            (* the name of the trace file *)
    -> unit
(* register a proof result for the given objective, and the given result (the
   boolean). The task may be used to improve the localization of the message.
   Use the empty string for the trace file if there is none.
   *)

val print_messages : unit -> unit
(* print all messages that have been registered so far. Also
   print the result file. The return value describes whether "warning messages"
   have been issued (= unproved checks). *)

val add_warning : ?loc:Loc.position -> string -> unit
