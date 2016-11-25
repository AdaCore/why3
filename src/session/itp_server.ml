open Call_provers

type prover = string
type transformation = string
type strategy = string

type node_ID = int
let root_node = 0

type node_type = File | Theory | Transformation | Goal | ProofAttempt of string

type node_info = { proved   : bool;
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
  | Command of string
  | Prove of prover * resource_limit
  | Transform of transformation * string list
  | Strategy of strategy
  | Open of string
  | Get_Session_Tree
  | Save
  | Reload
  | Replay

type ide_request = request_type * node_ID

open Unix_scheduler
open Session_itp
open Controller_itp

module C = Why3.Controller_itp.Make(Unix_Scheduler)

module type Protocol = sig
  val get_requests : unit -> request_type list
  val notify : notification list -> unit
end

module Make (P:Protocol) = struct

  let the_tree : session_tree ref = Obj.magic "tree"

  (* create a new node in the_tree and send a notification about it *)
  let new_node ~parent:node_ID node_type node_info : unit
    = ()
(*    ...
        P.notify (Subtree_change (nodeID,  )) *)

  let node_ID_from_pan pan = 0
  let node_ID_from_pn  pn  = 0

  (* ----------------- Schedule proof attempt -------------------- *)

  (* Callback of a proof_attempt *)
  let callback_update_tree_proof cont panid pa_status =
    let ses = cont.controller_session in
    let pa = get_proof_attempt_node ses panid in
    let prover = pa.prover in
    let name = Pp.string_of Whyconf.print_prover prover in
    let obsolete = pa.proof_obsolete in
    let r = match pa_status with
      | Scheduled ->
        begin
          try
            ignore (node_ID_from_pan panid)
            (* TODO: do we notify here ? *)
          with Not_found ->
            let parent_id = get_proof_attempt_parent ses panid in
            let parent = node_ID_from_pn parent_id in
            new_node ~parent (ProofAttempt name) { proved=false; obsolete=false }
        end
      | Done _ ->
        P.notify (Node_change (node_ID_from_pan panid,
                               { proved=false; obsolete=false }))
        let ppn = get_proof_attempt_parent cont.controller_session panid in
        let piter = (node_ID_from_pn ppn)#iter in
        update_status_column_from_iter cont piter;
        (* move focus an collapse if the goal was proven and
           the current index still corresponds to the goal *)
        begin match !current_selected_index with
          | IproofNode pn when pn = ppn ->
            if pn_proved cont pn then
              go_to_nearest_unproven_goal_and_collapse pn
          | _ -> ()
        end;
        row_from_pan panid
      | _  -> row_from_pan panid (* TODO ? *)
    in
    goals_model#set ~row:r#iter ~column:status_column
      (image_of_pa_status ~obsolete pa_status)

  let test_schedule_proof_attempt cont (p: Whyconf.config_prover) limit =
    let prover = p.Whyconf.prover in
    let callback = callback_update_tree_proof cont in
    let rec get_goals () =
      match !current_selected_index with
      | IproofNode id -> [id]
      | IproofAttempt _ ->
        move_current_row_selection_up ();
        get_goals ()
      | Itransformation tn ->
        List.rev (unproven_goals_below_tn cont [] tn)
      | Ifile file ->
        List.rev (unproven_goals_below_file cont file)
      | Itheory th ->
        List.rev (unproven_goals_below_th cont [] th)
      | Inone -> []
    in
    List.iter (fun id -> C.schedule_proof_attempt cont id prover ~limit ~callback)
      (get_goals ())


  let treat_request r = match r with
    | Prove (p,limit) -> schedule_proof_attempt p limit


  let treat_requests () : bool =
    List.iter treat_request (P.get_requests ());
    true

  let _ = Unix_Scheduler.idle ~prio:1 treat_requests


end
