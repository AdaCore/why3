open Why3

val register :
     Gnat_expl.expl
  -> Task.task option
  -> Call_provers.prover_result option
  -> bool
    -> unit
(* register a proof result for the given objective, and the given result (the
   boolean). The task may be used to improve the localization of the message.
   *)

val print_messages_and_clear : unit -> unit
