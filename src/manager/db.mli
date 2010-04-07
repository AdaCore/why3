

type transaction_mode = | Deferred | Immediate | Exclusive

type handle
  (** Database handle which can be used to create and retrieve objects *)

val create :
  ?busyfn:(Sqlite3.db -> unit) -> ?mode:transaction_mode ->
  string -> handle
  (** [create db_name] opens a Sqlite3 database with filename
      [db_name] and create any tables if they are missing. 
      @return a
      database handle which can be used to create and retrieve objects in
      the database.  @raise Sql_error if a database error is
      encountered *)

(*
val raw: handle -> Sqlite3.db
  (** [raw db] @return the underlying Sqlite3 database for the
      connection, for advanced queries.  *)
*)

module Loc : sig

  type t = {
    mutable id : int64 option;
    mutable file : string;
    mutable line : int64;
    mutable start : int64;
    mutable stop : int64;
  }
      (** A record which can be stored in the database with the [save]
          function, or removed by calling [delete]. Changes are not
          committed to the database until [save] is invoked.  *)

  val save: handle -> t -> int64 

  val delete: handle -> t -> unit


  val create :
    ?id:int64 ->
    file:string ->
    line:int64 ->
    start:int64 ->
    stop:int64 ->
    t
    (** Can be used to construct a new object.  If [id] is not specified, it will be automatically assigned the first time [save] is called on the object.  The object is not committed to the database until [save] is invoked.  The [save] method will also return the [id] assigned to the object.
        @raise Sql_error if a database error is encountered
    *)

  val get :
    ?id:int64 ->
    ?file:string ->
    ?line:int64 ->
    ?start:int64 ->
    ?stop:int64 ->
    ?custom_where:string * Sqlite3.Data.t list -> handle -> t list
  (** Used to retrieve objects from the database.  If an argument is specified, it is included in the search criteria (all fields are ANDed together).
   @raise Sql_error if a database error is encountered
    *)

end

(*
module External_proof : sig
  type t = <
    id : int64 option;
    set_id : int64 option -> unit;
    prover : string;
    set_prover : string -> unit;
    timelimit : int64;
    set_timelimit : int64 -> unit;
    memlimit : int64;
    set_memlimit : int64 -> unit;
    status : int64;
    set_status : int64 -> unit;
    result_time : float;
    set_result_time : float -> unit;
    trace : string;
    set_trace : string -> unit;
    obsolete : int64;
    set_obsolete : int64 -> unit;
    save: int64; delete: unit
  >

  (** An object which can be stored in the database with the [save] method call, or removed by calling [delete].  Fields can be accessed via the approriate named method and set via the [set_] methods.  Changes are not committed to the database until [save] is invoked.
    *)

  val t :
    ?id:int64 option ->
    prover:string ->
    timelimit:int64 ->
    memlimit:int64 ->
    status:int64 ->
    result_time:float ->
    trace:string ->
    obsolete:int64 ->
    Init.t -> t
  (** Can be used to construct a new object.  If [id] is not specified, it will be automatically assigned the first time [save] is called on the object.  The object is not committed to the database until [save] is invoked.  The [save] method will also return the [id] assigned to the object.
   @raise Sql_error if a database error is encountered
    *)

  val get :
    ?id:int64 option ->
    ?prover:string option ->
    ?timelimit:int64 option ->
    ?memlimit:int64 option ->
    ?status:int64 option ->
    ?result_time:float option ->
    ?trace:string option ->
    ?obsolete:int64 option ->
    ?custom_where:string * Sqlite3.Data.t list -> Init.t -> t list
  (** Used to retrieve objects from the database.  If an argument is specified, it is included in the search criteria (all fields are ANDed together).
   @raise Sql_error if a database error is encountered
    *)

end
module Goal : sig
  type t = <
    id : int64 option;
    set_id : int64 option -> unit;
    task_checksum : string;
    set_task_checksum : string -> unit;
    parent : Transf.t;
    set_parent : Transf.t -> unit;
    name : string;
    set_name : string -> unit;
    pos : Loc.t;
    set_pos : Loc.t -> unit;
    external_proofs : External_proof.t list;
    set_external_proofs : External_proof.t list -> unit;
    transformations : Transf.t list;
    set_transformations : Transf.t list -> unit;
    proved : int64;
    set_proved : int64 -> unit;
    save: int64; delete: unit
  >

  (** An object which can be stored in the database with the [save] method call, or removed by calling [delete].  Fields can be accessed via the approriate named method and set via the [set_] methods.  Changes are not committed to the database until [save] is invoked.
    *)

  val t :
    ?id:int64 option ->
    task_checksum:string ->
    parent:Transf.t ->
    name:string ->
    pos:Loc.t ->
    external_proofs:External_proof.t list ->
    transformations:Transf.t list ->
    proved:int64 ->
    Init.t -> t
  (** Can be used to construct a new object.  If [id] is not specified, it will be automatically assigned the first time [save] is called on the object.  The object is not committed to the database until [save] is invoked.  The [save] method will also return the [id] assigned to the object.
   @raise Sql_error if a database error is encountered
    *)

  val get :
    ?id:int64 option ->
    ?task_checksum:string option ->
    ?name:string option ->
    ?proved:int64 option ->
    ?custom_where:string * Sqlite3.Data.t list -> Init.t -> t list
  (** Used to retrieve objects from the database.  If an argument is specified, it is included in the search criteria (all fields are ANDed together).
   @raise Sql_error if a database error is encountered
    *)

end
module Transf : sig
  type t = <
    id : int64 option;
    set_id : int64 option -> unit;
    name : string;
    set_name : string -> unit;
    obsolete : int64;
    set_obsolete : int64 -> unit;
    subgoals : Goal.t list;
    set_subgoals : Goal.t list -> unit;
    save: int64; delete: unit
  >

  (** An object which can be stored in the database with the [save] method call, or removed by calling [delete].  Fields can be accessed via the approriate named method and set via the [set_] methods.  Changes are not committed to the database until [save] is invoked.
    *)

  val t :
    ?id:int64 option ->
    name:string ->
    obsolete:int64 ->
    subgoals:Goal.t list ->
    Init.t -> t
  (** Can be used to construct a new object.  If [id] is not specified, it will be automatically assigned the first time [save] is called on the object.  The object is not committed to the database until [save] is invoked.  The [save] method will also return the [id] assigned to the object.
   @raise Sql_error if a database error is encountered
    *)

  val get :
    ?id:int64 option ->
    ?name:string option ->
    ?obsolete:int64 option ->
    ?custom_where:string * Sqlite3.Data.t list -> Init.t -> t list
  (** Used to retrieve objects from the database.  If an argument is specified, it is included in the search criteria (all fields are ANDed together).
   @raise Sql_error if a database error is encountered
    *)

end
*)
