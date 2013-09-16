open Why3

val register :
     Gnat_expl.expl
  -> Task.task option                  (* task of the last goal *)
  -> Call_provers.prover_result option (* extra information about the run *)
  -> bool                              (* if the goal was proved or not *)
  -> string                            (* the name of the trace file *)
    -> unit
(* register a proof result for the given objective, and the given result (the
   boolean). The task may be used to improve the localization of the message.
   Use the empty string for the trace file if there is none.
   *)

val print_messages : unit -> unit
(* print all messages that have been registered so far. Also
   print the result file. *)

