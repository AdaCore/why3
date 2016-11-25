open Call_provers

type prover
type transformation
type strategy

type node_ID
val root_node : node_ID

(* --------------------------- types to be expanded on call by need --------------------------------- *)

type node_type = File | Theory | Transformation | Goal | ProofAttempt

type node_info = { proved   : bool; (* TODO: add more *)
                   obsolete : bool }

type session_tree = Node of node_ID * node_type * node_info * session_tree list

type error_notification =
  | Proof_error  of node_ID * string
  | Transf_error of node_ID * string

type notification =
  | Node_change    of node_ID * node_info
  | Subtree_change of node_ID * session_tree
  | Remove         of node_ID
  | Initialized    of prover list * transformation list * strategy list
  | Session_Tree   of session_tree
  | Error          of error_notification

type request_type =
  | Command   of string
  | Prove     of prover * resource_limit
  | Transform of transformation * string list
  | Strategy  of strategy
  | Open      of string
  | Get_Session_Tree
  | Save
  | Reload
  | Replay

type ide_request = request_type * node_ID

module type Protocol = sig

  val get_requests : unit -> request_type list
  val send_notifications : notification list -> unit

end

module Make (P:Protocol) : sig end
