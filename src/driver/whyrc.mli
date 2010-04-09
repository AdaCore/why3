


(** {2 access to user configuration and drivers} *)

val read_config_file: ?name:string -> unit
  (** reads the config file from file [name]. The
      default rc file name is "$HOME/.why/why3rc" if HOME is set, or
      "$USERPROFILE/.why/why3rc" if USERPROFILE is set, or "./.why/why3rc"
      otherwise *)

val known_provers: unit -> string list
  (** returns the list of known prover ids. *)

val get_driver: string -> Env.env -> Driver.driver
  (** returns the driver associated to the given prover id *)


(** {2 configuration update} *)

val add_driver_config: string -> string -> string -> unit
(** [add_driver_config id file cmd] adds in the current configuration
    a new prover named [id], associated to a new driver description
    file built from the template [file] and the command line [cmd].
    This new setting is recorded in the user's rc file when [save] is called.
    {!add_driver_config} *)

val save : unit -> unit
(** saves the current configuration into the same file as given in
[read_config_file] *)
