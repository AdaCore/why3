open Call_provers
open Format

(* Information that the IDE may want to have *)
type prover = string
type transformation = string
type strategy = string


type node_ID = int
let root_node : node_ID = 0

type node_type =
  | NRoot
  | NFile
  | NTheory
  | NTransformation
  | NGoal
  | NProofAttempt of Call_provers.prover_answer option * bool

type node_info =
    {
     proved : bool;
     name   : string;
    }

type global_information =
    {
     provers         : prover list;
     transformations : transformation list;
     strategies      : strategy list;
     commands        : string list;
     (* hidden_provers       : string list; *)
     (* session_time_limit   : int; *)
     (* session_mem_limit    : int; *)
     (* session_nb_processes : int; *)
     (* session_cntexample   : bool; *)
     (* main_dir             : string *)
    }

type message_notification =
  | Proof_error  of node_ID * string
  | Transf_error of node_ID * string
  | Strat_error  of node_ID * string
  | Replay_Info  of string
  | Query_Info   of node_ID * string
  | Query_Error  of node_ID * string
  | Help         of string
  | Information  of string
  | Task_Monitor of int * int * int
  | Error        of string

type notification =
  | Node_change  of node_ID * node_info
  | New_node     of node_ID * node_ID * node_type * node_info
  | Remove       of node_ID
  | Initialized  of global_information
  | Saved
  | Message      of message_notification
  | Dead         of string
  | Proof_update of node_ID * Controller_itp.proof_attempt_status
  | Task         of node_ID * string

type request_type =
  | Command_req       of string
  | Prove_req         of prover * resource_limit
  | Transform_req     of transformation * string list
  | Strategy_req      of strategy
  | Open_req          of string
  | Set_max_tasks_req of int
  | Get_task
  | Get_Session_Tree_req
  | Save_req
  | Reload_req
  | Replay_req
  | Exit_req

type ide_request = request_type * node_ID

(* Debugging functions *)
let print_request fmt r =
  match r with
  | Command_req s             -> fprintf fmt "command \"%s\"" s
  | Prove_req (prover, _rl)   -> fprintf fmt "prove with %s" prover
  | Transform_req (tr, _args) -> fprintf fmt "transformation :%s" tr
  | Strategy_req st           -> fprintf fmt "strategy %s" st
  | Open_req f                -> fprintf fmt "open file %s" f
  | Set_max_tasks_req i       -> fprintf fmt "set max tasks %i" i
  | Get_task                  -> fprintf fmt "get task"
  | Get_Session_Tree_req      -> fprintf fmt "get session tree"
  | Save_req                  -> fprintf fmt "save"
  | Reload_req                -> fprintf fmt "reload"
  | Replay_req                -> fprintf fmt "replay"
  | Exit_req                  -> fprintf fmt "exit"

let print_msg fmt m =
  match m with
  | Proof_error (_ids, s)  -> fprintf fmt "proof error %s" s
  | Transf_error (_ids, s) -> fprintf fmt "transf error %s" s
  | Strat_error (_ids, s)  -> fprintf fmt "start error %s" s
  | Replay_Info s          -> fprintf fmt "replay info %s" s
  | Query_Info (_ids, s)   -> fprintf fmt "query info %s" s
  | Query_Error (_ids, s)  -> fprintf fmt "query error %s" s
  | Help _s                -> fprintf fmt "help"
  | Information s          -> fprintf fmt "info %s" s
  | Task_Monitor _         -> fprintf fmt "task montor"
  | Error s                -> fprintf fmt "%s" s

let print_notify fmt n =
  match n with
  | Node_change (_ni, _nf)          -> fprintf fmt "node change"
  | New_node (_ni, _pni, _nt,  _nf) -> fprintf fmt "new node"
  | Remove _ni                      -> fprintf fmt "remove"
  | Initialized _gi                 -> fprintf fmt "initialized"
  | Saved                           -> fprintf fmt "saved"
  | Message msg                     ->
      print_msg fmt msg
  | Dead s                          -> fprintf fmt "dead :%s" s
  | Proof_update (_ni, _pas)        -> fprintf fmt "proof update"
  | Task (_ni, _s)                  -> fprintf fmt "task"

open Session_itp
open Controller_itp
open Session_user_interface
open Stdlib

module type Protocol = sig
  val get_requests : unit -> ide_request list
  val notify : notification -> unit
end

module Make (S:Controller_itp.Scheduler) (P:Protocol) = struct

  module C = Controller_itp.Make(S)

  let _debug = Debug.register_flag "itp_server"

  (************************)
  (* parsing command line *)
  (************************)

  let files = Queue.create ()
  (* TODO never used let _opt_parser = ref None *)

  (* Files are passed with request Open *)
  let config, base_config, env =
    let c, b, e = Whyconf.Args.init () in
    c, b, e

  let get_configs () = config, base_config

  let task_driver =
    let main = Whyconf.get_main config in
    let d = Filename.concat (Whyconf.datadir main)
        (Filename.concat "drivers" "why3_itp.drv")
    in
    Driver.load_driver env d []

  let provers : Whyconf.config_prover Whyconf.Mprover.t =
    Whyconf.get_provers config

  let get_prover_list (config: Whyconf.config) =
    Mstr.fold (fun x _ acc -> x :: acc) (Whyconf.get_prover_shortcuts config) []

  let prover_list: prover list = get_prover_list config
  let transformation_list: transformation list =
    List.map fst (Session_user_interface.list_transforms ())
  let strategies_list: strategy list = []

(* TODO write this *)
  let infos =
    {
     provers = prover_list;
     transformations = transformation_list;
     strategies = strategies_list;
     commands =
       List.map (fun (c,_,_) -> c) Session_user_interface.commands
   }

  (* Controller is not initialized: we cannot process any request *)
  let init_controller = ref false

  (* Create_controller creates a dummy controller *)
  let cont =
    init_controller := false;
    create_controller env

  (* ------------ init controller ------------ *)

  (* Init cont is called only when an Open is requested *)
  let init_cont f =
    Queue.add f files;
    try
      (Session_user_interface.cont_from_files cont [] "" env files provers;
       init_controller := true;
       P.notify (Initialized infos))
    with e ->
      Format.eprintf "%a@." Exn_printer.exn_printer e;
      P.notify (Dead (Pp.string_of Exn_printer.exn_printer e));
      exit 1

  (* -----------------------------------   ------------------------------------- *)

  let get_info_and_type ses (node: any) =
    match node with
    | AFile file ->
        let name = file.file_name in
        let proved = file_proved cont file in
        NFile, {name; proved}
    | ATh th     ->
        let name = (theory_name th).Ident.id_string in
        let proved = th_proved cont th in
        NTheory, {name; proved}
    | ATn tn     ->
        let name = get_transf_name ses tn in
        let proved = tn_proved cont tn in
        NTransformation, {name; proved}
    | APn pn     ->
        let name = (get_proof_name ses pn).Ident.id_string in
        let proved = pn_proved cont pn in
          NGoal, {name; proved}
    | APa pan    ->
        let pa = get_proof_attempt_node ses pan in
        let name = Pp.string_of Whyconf.print_prover pa.prover in
        let pr, proved = match pa.Session_itp.proof_state with
        | Some pr -> Some pr.pr_answer, pr.pr_answer = Valid
        | None -> None, false
        in
        (NProofAttempt (pr, pa.proof_obsolete)),
        {name; proved}

(* fresh gives new fresh "names" for node_ID using a counter.
   reset resets the counter so that we can regenerate node_IDs as if session
   was fresh *)
  let reset, fresh =
    let count = ref 0 in
    (fun () ->
      count := 0),
    fun () ->
      count := !count + 1;
      !count

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

  let node_ID_from_any  any  =
    match any with
    | AFile file -> node_ID_from_file file
    | ATh th     -> node_ID_from_th th
    | ATn tn     -> node_ID_from_tn tn
    | APn pn     -> node_ID_from_pn pn
    | APa pan    -> node_ID_from_pan pan

(* TODO match this *)
exception Bad_prover_name of prover

  let get_prover p =
    match return_prover p config with
    | None -> raise (Bad_prover_name p)
    | Some c -> c

  let add_node_to_table node new_id =
    match node with
    | AFile file -> Hstr.add file_to_node_ID file.file_name new_id
    | ATh th     -> Ident.Hid.add th_to_node_ID (theory_name th) new_id
    | ATn tn     -> Htn.add tn_to_node_ID tn new_id
    | APn pn     -> Hpn.add pn_to_node_ID pn new_id
    | APa pan    -> Hpan.add pan_to_node_ID pan new_id

  (* create a new node in the_tree, update the tables and send a
     notification about it *)
  let new_node ~parent node : node_ID =
    let new_id = fresh () in
      Hint.add model_any new_id node;
      let ses = cont.controller_session in
      let typ, info = get_info_and_type ses node in
      add_node_to_table node new_id;
      P.notify (New_node (new_id, parent, typ, info));
      new_id

  (* TODO this is a dummy constant for root content *)
  let root_info = { proved = false; name = ""}
  let root = 0

  (* ----------------- build tree from tables ----------------- *)

  (*
     build_the_tree() returns the whole session tree as notifications beginning
     with the notification corresponding to a "root node" creation (root of the
     files)
  *)
(* TODO remove this unnecessary
  let build_the_tree () : unit =
    let ses = cont.controller_session in
    let files = get_files ses in
    P.notify (New_node (0, 0, Root, root_info));
    let l = Stdlib.Hstr.fold
      (fun _file_key file acc ->
         let file_node_ID = node_ID_from_file file in
         let pos_ID = pos_from_node file_node_ID in
         let node_type, node_info = get_info_and_type ses (AFile file) in
         let l = List.fold_left (fun acc th ->
               build_subtree_from_theory ses th :: acc) [] file.file_theories in
         Node (file_node_ID, pos_ID, node_type, node_info, l) :: acc
      ) files [] in
*)

  (* ----------------- init the tree --------------------------- *)
  (* Iter on the session tree with a function [f parent current] with type
     node_ID -> any -> unit *)
  let iter_subtree_proof_attempt_from_goal
    (f: parent:node_ID -> any -> unit) parent id =
    Whyconf.Hprover.iter
      (fun _pa panid -> f ~parent (APa panid))
      (get_proof_attempt_ids cont.controller_session id)

  let rec iter_subtree_from_goal
    (f: parent:node_ID -> any -> unit) parent id =
    let ses = cont.controller_session in
    f ~parent (APn id);
    let nid = node_ID_from_pn id in
    List.iter
      (fun trans_id -> iter_subtree_from_trans f nid trans_id)
      (get_transformations ses id);
    iter_subtree_proof_attempt_from_goal f nid id

  and iter_subtree_from_trans
    (f: parent:node_ID -> any -> unit) parent trans_id =
    let ses = cont.controller_session in
    f ~parent (ATn trans_id);
    let nid = node_ID_from_tn trans_id in
    List.iter
      (fun goal_id -> (iter_subtree_from_goal f nid goal_id))
      (get_sub_tasks ses trans_id)

  let iter_subtree_from_theory
    (f: parent:node_ID -> any -> unit) parent theory_id =
    f ~parent (ATh theory_id);
    let nid = node_ID_from_th theory_id in
    List.iter (iter_subtree_from_goal f nid)
               (theory_goals theory_id)

  let iter_subtree_from_file
    (f: parent:node_ID -> any -> unit) parent file =
    f ~parent (AFile file);
    let nid = node_ID_from_file file in
    List.iter (iter_subtree_from_theory f nid)
      file.file_theories

  let iter_the_files (f: parent:node_ID -> any -> unit) parent : unit =
    let ses = cont.controller_session in
    let files = get_files ses in
    Stdlib.Hstr.iter
      (fun _ file ->
        iter_subtree_from_file f parent file)
      files

  let _init_the_tree (): unit =
    let f ~parent node_id = ignore (new_node ~parent node_id) in
    iter_the_files f root

  let init_and_send_subtree_from_trans parent trans_id : unit =
    iter_subtree_from_trans
      (fun ~parent id -> ignore (new_node ~parent id)) parent trans_id

  let init_and_send_the_tree (): unit =
    iter_the_files (fun ~parent id -> ignore (new_node ~parent id)) root

  let resend_the_tree (): unit =
    let ses = cont.controller_session in
    let send_node ~parent any =
      let node_id = node_ID_from_any any in
      let node_type, node_info = get_info_and_type ses any in
      P.notify (New_node (node_id, parent, node_type, node_info)) in
    P.notify (New_node (0, 0, NRoot, root_info));
    iter_the_files send_node root

  (* -- send the task -- *)

  let send_task nid =
    match any_from_node_ID nid with
    | APn id ->
      let task = get_task cont.controller_session id in
      let tables = get_tables cont.controller_session id in
      let s = Pp.string_of
          (fun fmt -> Driver.print_task ~cntexample:false task_driver fmt tables)
          task in
      P.notify (Task (nid,s))
    | _ ->
      P.notify (Task (nid, "can not associate a task to a node that is not a goal."))

  (* ----------------- Schedule proof attempt -------------------- *)

  (* Callback of a proof_attempt *)
  let callback_update_tree_proof cont panid pa_status =
    let ses = cont.controller_session in
    begin match pa_status with
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
(*    | Done pr ->
      P.notify (Node_change (node_ID_from_pan panid,
                             {proved=(pr.pr_answer=Valid); name=""})); *)
      (* TODO: we don't want to resend the name every time, separate
         updatable from the rest *)
    | _  -> () (* TODO ? *)
    end;
    P.notify (Proof_update (node_ID_from_pan panid, pa_status))

  let notify_change x b =
    try (
      let node_ID = node_ID_from_any x in
      let _, node_info = get_info_and_type cont.controller_session x in
      P.notify (Node_change (node_ID, {name = node_info.name; proved = b}))
     )
    with Not_found -> ()

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
    List.iter (fun id -> C.schedule_proof_attempt cont id prover ~limit ~callback ~notification:notify_change)
      goals

  (* ----------------- Schedule transformation -------------------- *)

  (* Callback of a transformation *)
  let callback_update_tree_transform status =
    match status with
    | TSdone trans_id ->
      let ses = cont.controller_session in
      let id = get_trans_parent ses trans_id in
      let nid = node_ID_from_pn id in
      init_and_send_subtree_from_trans nid trans_id
    | TSfailed (id, e) ->
      let msg =
        Pp.sprintf "%a" (get_exception_message cont.controller_session id) e
      in
      P.notify (Message (Strat_error(node_ID_from_pn id, msg)))
    | _ -> ()

  let rec apply_transform nid t args =
    match any_from_node_ID nid with
    | APn id ->
      (* let node_ID = node_ID_from_any x in *)
      (* let _, node_info = get_info_and_type cont.controller_session x in *)
      (* P.notify (Node_change (node_ID, {name = node_info.name; proved = b})) in *)
      let callback = callback_update_tree_transform in
      C.schedule_transformation cont id t args ~callback ~notification:notify_change
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
          C.run_strategy_on_goal cont id st ~callback_pa ~callback_tr ~callback ~notification:notify_change
        | _ -> Format.printf "Strategy '%s' not found@." s
      end
    | _ -> ()

  (* ----------------- Save session --------------------- *)
  let save_session () =
    Session_itp.save_session cont.controller_session;
    P.notify Saved

  (* ----------------- Reload session ------------------- *)
  let clear_tables () : unit =
    reset ();
    Hint.clear model_any;
    Hpan.clear pan_to_node_ID;
    Hpn.clear pn_to_node_ID;
    Htn.clear tn_to_node_ID;
    Ident.Hid.clear th_to_node_ID;
    Hstr.clear file_to_node_ID

  let reload_session () : unit =
    clear_tables ();
    reload_files cont env ~use_shapes:true;
    init_and_send_the_tree ()

  let replay_session () : unit =
    clear_tables ();
    let callback = fun lr ->
      P.notify (Message (Replay_Info (Pp.string_of C.replay_print lr))) in
    (* TODO make replay print *)
    C.replay ~use_steps:false cont ~callback:callback ~remove_obsolete:false

  (* ----------------- treat_request -------------------- *)

  let get_proof_node_id nid =
    try
      match any_from_node_ID nid with
      | APn pn_id -> Some pn_id
      | _ -> None
    with
      Not_found -> None

  let rec treat_request (r,nid) =
    try (
    match r with
    | Prove_req (p,limit)     -> schedule_proof_attempt nid (get_prover p) limit
    | Transform_req (t, args) -> apply_transform nid t args
    | Strategy_req st         -> run_strategy_on_task nid st
    | Save_req                -> save_session ()
    | Reload_req              -> reload_session ();
    | Get_Session_Tree_req    -> resend_the_tree ()
    | Get_task                -> send_task nid
    | Replay_req              -> replay_session (); resend_the_tree ()
    | Command_req cmd         ->
      begin
        let snid = get_proof_node_id nid in
        match (interp config cont snid cmd) with
        | Transform (s, _t, args) -> treat_request (Transform_req (s, args), nid)
        | Query s                 -> P.notify (Message (Query_Info (nid, s)))
        | Prove (p, limit)        -> schedule_proof_attempt nid p limit
        | Strategies st           -> run_strategy_on_task nid st
        | Help_message s          -> P.notify (Message (Help s))
        | QError s                -> P.notify (Message (Query_Error (nid, s)))
        | Other (s, _args)        ->
            P.notify (Message (Information ("Unknown command"^s)))
      end
    | Open_req file_name      ->
        if !init_controller then
          Controller_itp.add_file cont file_name
        else begin
          init_cont file_name;
          init_and_send_the_tree ()
        end
    | Set_max_tasks_req i     -> C.set_max_tasks i
    | Exit_req                -> exit 0 (* TODO *)
     )
    with e -> P.notify (Message (Error (Pp.string_of
      (fun fmt (r,nid,e) -> Format.fprintf fmt
          "There was an unrecoverable error during treatment of request:\n %a\non node: %d\nwith exception: %a"
    print_request r nid Exn_printer.exn_printer e ) (r, nid, e))))

  let treat_requests () : bool =
    List.iter treat_request (P.get_requests ());
    true

  let update_monitor =
    let tr = ref 0 in
    let sr = ref 0 in
    let rr = ref 0 in
    fun t s r ->
      if (not (t = !tr && s = !sr && r = !rr)) then
        begin
          P.notify (Message (Task_Monitor (t,s,r)));
          tr := t;
          sr := s;
          rr := r
        end

  let _ =
    S.timeout ~ms:100 treat_requests;
    (* S.idle ~prio:1 treat_requests; *)
    C.register_observer update_monitor

end
