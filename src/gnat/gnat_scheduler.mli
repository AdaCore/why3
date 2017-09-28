module Gnat_scheduler : sig

    val blocking: bool

    val multiplier: int

    val timeout: ms:int -> (unit -> bool) -> unit
    (** [timeout ~ms f] registers the function [f] as a function to be
        called every [ms] milliseconds.
    *)

    val idle: prio:int -> (unit -> bool) -> unit
    (** [idle prio f] In this particular module the function f is called directly
        (and it should only contains transformations calls).
    *)

    val main_loop: (unit -> unit) -> unit

end
