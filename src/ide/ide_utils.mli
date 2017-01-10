

module History : sig
  type history

  val create_history: unit -> history
  val print_next_command: history -> string option
  val print_prev_command: history -> string option
  val add_command: history -> string -> unit

end

val get_first_unproven_goal_around:
    proved:('a -> bool) ->
      children:('a -> 'a list) ->
        get_parent:('a -> 'a option) ->
          is_goal:('a -> bool) -> 'a -> 'a option
