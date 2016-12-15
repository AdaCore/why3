exception NotADirectory of string
exception BadFileName of string

(** Controller initialization *)

(* Init the given controller with the session in directory given *)
val cont_from_session_dir: Controller_itp.controller -> string -> unit

(* Init the controller with the session located in a directory with the name of
   the file without extension *)
val cont_from_file: Controller_itp.controller -> string -> unit



(** Simple queries *)

(* The id you are trying to use is undefined *)
exception Undefined_id of string
(* Bad number of arguments *)
exception Number_of_arguments

type query =
  | Qnotask of (Controller_itp.controller -> string list -> string)
  | Qtask of (Controller_itp.controller -> Task.name_tables -> string list -> string)


val print_id: 'a -> Task.name_tables -> string list -> string
val search_id: 'a -> Task.name_tables -> string list -> string

val list_provers: Controller_itp.controller -> _ -> string
val list_transforms: unit -> (string * Pp.formatted) list
val list_transforms_query: _ -> _ -> string
val help_on_queries: Format.formatter -> (string * string * 'a) list -> unit
val strategies: Env.env -> Whyconf.config ->
  (string * string * string * Strategy.instruction array) list ref ->
    (string * string * string * Strategy.instruction array) list

(** Command line parsing tools *)

val return_prover: string -> Whyconf.config -> Whyconf.config_prover option

type command =
  | Transform    of string * Trans.gentrans * string list
  | Prove        of Whyconf.config_prover * Call_provers.resource_limit
  | Strategies   of string
  | Help_message of string
  | Query        of string
  | QError       of string
  | Other        of string * string list

val interp: (string * string * 'a) list ->
  query Stdlib.Hstr.t ->
    Whyconf.config ->
      Controller_itp.controller ->
        Session_itp.proofNodeID option -> string -> command
