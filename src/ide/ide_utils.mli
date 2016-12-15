

module History : sig
  type history

  val create_history: unit -> history
  val print_next_command: history -> string option
  val print_prev_command: history -> string option
  val add_command: history -> string -> unit

end
