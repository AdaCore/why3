open Call_provers

type prover = string
type transformation = string
type strategy = string

type node_ID = int
let root_node = 0

type node_type = File | Theory | Transformation | Goal | ProofAttempt of bool

type node_info = { proved : bool;
                   name   : string }

type session_tree = Node of node_ID * node_type * node_info * session_tree list

type error_notification =
  | Proof_error  of node_ID * string
  | Transf_error of node_ID * string
  | Strat_error  of node_ID * string

type notification =
  | Node_change    of node_ID * node_info
  | New_Subtree    of node_ID * session_tree
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

let get_prover (p:prover) : Whyconf.config_prover = Obj.magic 1 (* TODO: do me ! *)

open Unix_scheduler
open Session_itp
open Controller_itp
open Session_user_interface
open Stdlib

module C = Controller_itp.Make(Unix_Scheduler)

module type Protocol = sig
  val get_requests : unit -> ide_request list
  val notify : notification -> unit
end

module Make (P:Protocol) = struct

  let debug = Debug.lookup_flag "itp_server"

  (************************)
  (* parsing command line *)
  (************************)

  let files = Queue.create ()
  let opt_parser = ref None

  let spec = Arg.align [
      "-F", Arg.String (fun s -> opt_parser := Some s),
      "<format> select input format (default: \"why\")";
      "--format", Arg.String (fun s -> opt_parser := Some s),
      " same as -F";
(*
  "-f",
   Arg.String (fun s -> input_files := s :: !input_files),
   "<file> add file to the project (ignored if it is already there)";
*)
      Termcode.arg_extra_expl_prefix
    ]

  let usage_str = Format.sprintf
      "Usage: %s [options] [<file.why>|<project directory>]..."
      (Filename.basename Sys.argv.(0))

  let config, base_config, env =
    let c, b, e =
      Whyconf.Args.initialize spec (fun f -> Queue.add f files) usage_str
    in
    if Queue.is_empty files then Whyconf.Args.exit_with_usage spec usage_str;
    c, b, e

  let task_driver =
    let main = Whyconf.get_main config in
    let d = Filename.concat (Whyconf.datadir main)
        (Filename.concat "drivers" "why3_itp.drv")
    in
    Driver.load_driver env d []

  let provers : Whyconf.config_prover Whyconf.Mprover.t =
    Whyconf.get_provers config

  (* ------------ init controller ------------ *)

  (* TODO: find a way to init cont only when requested (Open file request is send) *)
  let cont =
    try
      Session_user_interface.cont_from_files spec usage_str env files provers
    with e ->
      Format.eprintf "%a@." Exn_printer.exn_printer e;
      exit 1

  (* -----------------------------------   ------------------------------------- *)

  let the_tree : session_tree ref = Obj.magic "tree"

  type any =
    | AFile of file
    | ATh of theory
    | ATn of transID
    | APn of proofNodeID
    | APa of proofAttemptID

  let model_any : any Hint.t = Hint.create 17

  let any_from_node_ID (nid:node_ID) : any = Hint.find model_any nid

  let pan_to_node_ID  : node_ID Hpan.t = Hpan.create 17
  let pn_to_node_ID   : node_ID Hpn.t = Hpn.create 17
  let tn_to_node_ID   : node_ID Htn.t = Htn.create 17
  let th_to_node_ID   : node_ID Ident.Hid.t = Ident.Hid.create 7
  let file_to_node_ID : node_ID Hstr.t = Hstr.create 3

  let node_ID_from_pan  pan  = Hpan.find pan_to_node_ID pan
  let node_ID_from_pn   pn   = Hpn.find pn_to_node_ID pn
  let node_ID_from_tn   tn   = Htn.find tn_to_node_ID tn
  let node_ID_from_th   th   = Ident.Hid.find th_to_node_ID (theory_name th)
  let node_ID_from_file file = Hstr.find file_to_node_ID (file.file_name)

  (* TODO: /!\ /!\ /!\ README /!\ /!\ /!\

     The question of maintaining the session tree (for the server and
     the ide) is not clear: if we use "random" indices it will be
     difficult to update a specific node.

     A possible strategy would be to have indices be strings instead
     of ints and use a naming convention of the form index "c.b.an"
     for the node [an] child of [b] child of [c] child of [] the
     session. We can then easily go to a specific node given its
     index, it is stable under adding/moving/removing of subtree,
     there is no restriction on the number of nodes, and it is easily
     sendable through any protocol.

     any thought ? alternative ? *)

  (* create a new node in the_tree, update the tables and send a
     notification about it *)
  let new_node : parent:node_ID -> any -> node_ID =
    let cpt = ref 0 in          (* 0 is the root_node, the parent of the files *)
    fun ~parent node ->
      incr cpt;
      let new_id = !cpt in
      Hint.add model_any new_id node;
      let ses = cont.controller_session in
      let typ, info =
        match node with
        | AFile file -> Hstr.add file_to_node_ID file.file_name new_id;
          let name = file.file_name in
          let proved = file_proved cont file in
          File, {name; proved}
        | ATh th     -> Ident.Hid.add th_to_node_ID (theory_name th) new_id;
          let name = (theory_name th).Ident.id_string in
          let proved = th_proved cont th in
          Theory, {name; proved}
        | ATn tn     -> Htn.add tn_to_node_ID tn new_id;
          let name = get_transf_name ses tn in
          let proved = tn_proved cont tn in
          Transformation, {name; proved}
        | APn pn     -> Hpn.add pn_to_node_ID pn new_id;
          let name = (get_proof_name ses pn).Ident.id_string in
          let proved = pn_proved cont pn in
          Goal, {name; proved}
        | APa pan    -> Hpan.add pan_to_node_ID pan new_id;
          let pa = get_proof_attempt_node ses pan in
          let name = Pp.string_of Whyconf.print_prover pa.prover in
          let proved = match pa.proof_state with
            | Some pr -> pr.pr_answer = Valid
            | None -> false
          in
          (ProofAttempt pa.proof_obsolete), {name; proved}
      in
      (* TODO: update the_tree or don't have it and rebuild it on
         demand ? *)
      let subtree = Node (new_id, typ, info, []) in
      P.notify (New_Subtree (parent, subtree));
      new_id

  (* ----------------- init the tree --------------------------- *)

  let build_subtree_proof_attempt_from_goal parent id =
    Whyconf.Hprover.iter
      (fun _pa panid -> ignore (new_node ~parent (APa panid)))
      (get_proof_attempt_ids cont.controller_session id)

  let rec build_subtree_from_goal parent id =
    let ses = cont.controller_session in
    let nid = new_node ~parent (APn id) in
    List.iter
      (fun trans_id -> build_subtree_from_trans nid trans_id)
      (get_transformations ses id);
    build_subtree_proof_attempt_from_goal nid id

  and build_subtree_from_trans parent trans_id =
    let ses = cont.controller_session in
    let nid = new_node ~parent (ATn trans_id) in
    List.iter
      (fun goal_id -> (build_subtree_from_goal nid goal_id))
      (get_sub_tasks ses trans_id);

  (*  this does not actually compute the tree but generate its node_IDs *)
  let init_the_tree () : unit =
    let ses = cont.controller_session in
    let files = get_files ses in
    Stdlib.Hstr.iter
      (fun _ file ->
         let file_node_ID = new_node root_node (AFile file) in
         List.iter (fun th ->
             let th_node_ID = new_node ~parent:file_node_ID (ATh th) in
             List.iter (build_subtree_from_goal th_node_ID)
               (theory_goals th))
           file.file_theories)
      files in
  ()

  (* ----------------- Schedule proof attempt -------------------- *)

  (* Callback of a proof_attempt *)
  let callback_update_tree_proof cont panid pa_status =
    let ses = cont.controller_session in
    match pa_status with
    | Scheduled ->
      begin
        try
          ignore (node_ID_from_pan panid)
        (* TODO: do we notify here ? *)
        with Not_found ->
          let parent_id = get_proof_attempt_parent ses panid in
          let parent = node_ID_from_pn parent_id in
          ignore (new_node ~parent (APa panid))
      end
    | Done pr ->
      P.notify (Node_change (node_ID_from_pan panid,
                             {proved=(pr.pr_answer=Valid); name=""}));
      (* we don't want to resend the name every time, separate
         updatable from the rest *)
    | _  -> () (* TODO ? *)

  let schedule_proof_attempt nid (p: Whyconf.config_prover) limit =
    let prover = p.Whyconf.prover in
    let callback = callback_update_tree_proof cont in
    let goals =
      match any_from_node_ID nid with
      | APn pnid   -> [pnid]
      | APa panid  ->
          let ses = cont.controller_session in
          [get_proof_attempt_parent ses panid]
      | ATn tn     ->
        List.rev (unproven_goals_below_tn cont [] tn)
      | AFile file ->
        List.rev (unproven_goals_below_file cont file)
      | ATh th     ->
        List.rev (unproven_goals_below_th cont [] th)
    in
    List.iter (fun id -> C.schedule_proof_attempt cont id prover ~limit ~callback)
      goals

  (* ----------------- Schedule transformation -------------------- *)

  (* Callback of a transformation *)
  let callback_update_tree_transform status =
    match status with
    | TSdone trans_id ->
      let ses = cont.controller_session in
      let id = get_trans_parent ses trans_id in
      let nid = node_ID_from_pn id in
      build_subtree_from_trans nid trans_id
    | TSfailed (id, e) ->
      let msg =
        Pp.sprintf "%a" (get_exception_message cont.controller_session id) e
      in
      P.notify (Error (Strat_error(node_ID_from_pn id, msg)))
    | _ -> ()

  let rec apply_transform nid t args =
    match any_from_node_ID nid with
    | APn id ->
      let callback = callback_update_tree_transform in
      C.schedule_transformation cont id t args ~callback
    | APa panid ->
      let parent_id = get_proof_attempt_parent cont.controller_session panid in
      let parent = node_ID_from_pn parent_id in
      apply_transform parent t args
    | ATn _ | AFile _ | ATh _ ->
      (* TODO: propagate trans to all subgoals, just the first one, do nothing ... ?  *)
      ()

  (* ----------------- run strategy -------------------- *)

  let run_strategy_on_task nid s =
    match any_from_node_ID nid with
    | APn id ->
      let l = Session_user_interface.strategies
          cont.controller_env config
      in
      let st = List.filter (fun (_,c,_,_) -> c=s) l in
      begin
        match st with
        | [(n,_,_,st)] ->
          Format.printf "running strategy '%s'@." n;
          let callback sts =
            Format.printf "Strategy status: %a@." print_strategy_status sts
          in
          let callback_pa = callback_update_tree_proof cont in
          let callback_tr st = callback_update_tree_transform st in
          C.run_strategy_on_goal cont id st ~callback_pa ~callback_tr ~callback
        | _ -> Format.printf "Strategy '%s' not found@." s
      end
    | _ -> ()

  (* ----------------- treat_request -------------------- *)

  let treat_request (r,nid) = match r with
    | (Prove (p,limit))   -> schedule_proof_attempt nid (get_prover p) limit
    | Transform (t, args) -> apply_transform nid t args
    | _ -> assert false
(*    | Command cmd         ->
      | Transform (t, args) ->
      | Strategy st         ->
      | Open file_name      ->
      | Get_Session_Tree    ->
      | Save                ->
      | Reload              ->
      | Replay              -> *)


  let treat_requests () : bool =
    List.iter treat_request (P.get_requests ());
    true

  let _ = Unix_Scheduler.idle ~prio:1 treat_requests


end
