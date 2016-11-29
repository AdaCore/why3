open Call_provers

(* Information that the IDE may want to have *)
type prover = string
type transformation = string
type strategy = string
type infos =
    {hidden_provers : string list;
     session_time_limit : int;
     session_mem_limit : int;
     session_nb_processes : int;
     session_cntexample : bool;
     main_dir : string}

(*
     The question of maintaining the session tree (for the server and
     the ide) is not clear: if we use "random" indices it will be
     difficult to update a specific node.

     The strategy we use is to have indices as strings instead of
     ints and use a naming convention of the form index "0.0.n"
     for the node ["0.0.n"] child of ["0.0"] child of ["0"]
     child of "" the session.
     We can then easily go to a specific node given its
     index, it is stable under adding/moving/removing of subtree,
     there is no restriction on the number of nodes, and it is easily
     sendable through any protocol.

*)
type node_ID = string
type pos_ID = string
let root_node = ""

type node_type = Root | File | Theory | Transformation | Goal | ProofAttempt of bool

type node_info = { proved : bool;
                   name   : string }

type session_tree =
    Node of node_ID * pos_ID * node_type * node_info * session_tree list

type error_notification =
  | Proof_error  of node_ID * string
  | Transf_error of node_ID * string
  | Strat_error  of node_ID * string

type notification =
  | Node_change    of node_ID * node_info
  | New_subtree    of node_ID * session_tree
  | Remove         of node_ID
(* TODO Implement informations *)
  | Initialized    of infos * prover list * transformation list * strategy list
  | Saved
  | Session_Tree   of session_tree
  | Error          of error_notification
  | Message        of string

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
  | Exit

type ide_request = request_type * node_ID

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

  let debug = Debug.lookup_flag "ide_info" (* TODO register itp_server *)

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

(* TODO to be done. *)
  let get_prover_list () =
    []

  let get_transformation_list () =
    []

  let get_strategies_list () =
    []

  let prover_list: prover list = get_prover_list ()
  let transformation_list: transformation list = get_transformation_list ()
  let strategies_list: strategy list = get_strategies_list ()

(* TODO write this *)
  let get_info_from_main () = Obj.magic "TODO"

  let infos = get_info_from_main ()

  (* ------------ init controller ------------ *)

  (* TODO: find a way to init cont only when requested (Open file request is send) *)
  let cont =
    try
      (let cont =
        Session_user_interface.cont_from_files spec usage_str env files provers in
      P.notify (Initialized (infos, prover_list, transformation_list, strategies_list));
      cont)
    with e ->
      Format.eprintf "%a@." Exn_printer.exn_printer e;
      exit 1

  let () =
    let n = infos.session_nb_processes in
    Debug.dprintf debug "[IDE] setting max proof tasks to %d@." n;
    C.set_max_tasks n;
(* TODO no monitor    C.register_observer update_monitor *)

  (* -----------------------------------   ------------------------------------- *)

  type any =
    | AFile of file
    | ATh of theory
    | ATn of transID
    | APn of proofNodeID
    | APa of proofAttemptID

  let get_info_and_type ses (node: any) =
    match node with
    | AFile file ->
        let name = file.file_name in
        let proved = file_proved cont file in
        File, {name; proved}
    | ATh th     ->
        let name = (theory_name th).Ident.id_string in
        let proved = th_proved cont th in
        Theory, {name; proved}
    | ATn tn     ->
        let name = get_transf_name ses tn in
        let proved = tn_proved cont tn in
        Transformation, {name; proved}
    | APn pn     ->
        let name = (get_proof_name ses pn).Ident.id_string in
        let proved = pn_proved cont pn in
          Goal, {name; proved}
    | APa pan    ->
        let pa = get_proof_attempt_node ses pan in
        let name = Pp.string_of Whyconf.print_prover pa.prover in
        let proved = match pa.proof_state with
        | Some pr -> pr.pr_answer = Valid
        | None -> false
        in
        (ProofAttempt pa.proof_obsolete), {name; proved}

  let fresh_names = Hstr.create 17

  let fresh (parent: node_ID) =
    let s = try (Hstr.find fresh_names parent) with | _ -> 0 in
    let v = string_of_int s in
    Hstr.add fresh_names parent (s + 1);
    v

  let model_any : any Hstr.t = Hstr.create 17

  let any_from_node_ID (nid:node_ID) : any = Hstr.find model_any nid

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
    let pos_id = fresh parent in (* 0 is the root_node, the parent of the files *)
    let new_id = parent ^ "." ^ pos_id in
      Hstr.add model_any new_id node;
      let ses = cont.controller_session in
      let typ, info = get_info_and_type ses node in
      add_node_to_table node new_id;
      let subtree = Node (new_id, pos_id, typ, info, []) in
      P.notify (New_subtree (parent, subtree));
      new_id

  let pos_from_node (n: node_ID): pos_ID =
    let l = Str.split (Str.regexp ".") n in
    List.hd (List.rev l)

  (* ----------------- build tree from tables ----------------- *)
  (* This returns the actual algebraic type we defined from the
     hashtables containing node_ids. This suppose that init was
     done before it *)
(* TODO STACKOVERFLOW *)
  let build_subtree_proof_attempt_from_goal ses id =
    Whyconf.Hprover.fold
      (fun _pa panid acc ->
         let node_id = node_ID_from_pan panid in
         let pos_id = pos_from_node node_id in
         let node_type, node_info = get_info_and_type ses (APa panid) in
         Node (node_id, pos_id, node_type, node_info, []):: acc)
      (get_proof_attempt_ids cont.controller_session id) []

  let rec build_subtree_from_goal ses id =
    let nid = node_ID_from_pn id in
    let pos_ID = pos_from_node nid in
    let node_type, node_info = get_info_and_type ses (APn id) in
    let l =
      List.fold_left
        (fun acc trans_id -> build_subtree_from_trans ses trans_id :: acc)
        [] (get_transformations ses id) in
    let l' = build_subtree_proof_attempt_from_goal ses id in
    Node (nid, pos_ID, node_type, node_info, l @ l')

  and build_subtree_from_trans ses trans_id =
    let nid = node_ID_from_tn trans_id in
    let pos_ID = pos_from_node nid in
    let node_type, node_info = get_info_and_type ses (ATn trans_id) in
    let l = List.fold_left
      (fun acc goal_id -> build_subtree_from_goal ses goal_id :: acc)
      [] (get_sub_tasks ses trans_id) in
    Node (nid, pos_ID, node_type, node_info, l)

  let build_subtree_from_theory ses th_id =
    let nid = node_ID_from_th th_id in
    let pos_ID = pos_from_node nid in
    let node_type, node_info = get_info_and_type ses (ATh th_id) in
    let l = List.fold_left (fun acc id -> build_subtree_from_goal ses id :: acc)
      [] (theory_goals th_id) in
    Node (nid, pos_ID, node_type, node_info, l)

  (*  this does not actually compute the tree but generate its node_IDs *)
  let build_the_tree () : session_tree =
    let ses = cont.controller_session in
    let files = get_files ses in
    let l = Stdlib.Hstr.fold
      (fun _file_key file acc ->
         let file_node_ID = node_ID_from_file file in
         let pos_ID = pos_from_node file_node_ID in
         let node_type, node_info = get_info_and_type ses (AFile file) in
         let l = List.fold_left (fun acc th ->
               build_subtree_from_theory ses th :: acc) [] file.file_theories in
         Node (file_node_ID, pos_ID, node_type, node_info, l) :: acc
      ) files [] in
    Node ("", "", Root, Obj.magic 1, l)


  (* ----------------- init the tree --------------------------- *)

  let init_subtree_proof_attempt_from_goal parent id =
    Whyconf.Hprover.iter
      (fun _pa panid -> ignore (new_node ~parent (APa panid)))
      (get_proof_attempt_ids cont.controller_session id)

  let rec init_subtree_from_goal parent id =
    let ses = cont.controller_session in
    let nid = new_node ~parent (APn id) in
    List.iter
      (fun trans_id -> init_subtree_from_trans nid trans_id)
      (get_transformations ses id);
    init_subtree_proof_attempt_from_goal nid id

  and init_subtree_from_trans parent trans_id =
    let ses = cont.controller_session in
    let nid = new_node ~parent (ATn trans_id) in
    List.iter
      (fun goal_id -> (init_subtree_from_goal nid goal_id))
      (get_sub_tasks ses trans_id)

  (*  this does not actually compute the tree but generate its node_IDs *)
  let init_the_tree () : unit =
    let ses = cont.controller_session in
    let files = get_files ses in
    Stdlib.Hstr.iter
      (fun _ file ->
         let file_node_ID = new_node root_node (AFile file) in
         List.iter (fun th ->
             let th_node_ID = new_node ~parent:file_node_ID (ATh th) in
             List.iter (init_subtree_from_goal th_node_ID)
               (theory_goals th))
           file.file_theories)
      files

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
      init_subtree_from_trans nid trans_id
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

  (* ----------------- Save session --------------------- *)
  let save_session () =
    Session_itp.save_session cont.controller_session;
    P.notify Saved

  (* ----------------- Reload session ------------------- *)
  let clear_tables () : unit =
    Hstr.clear model_any;
    Hpan.clear pan_to_node_ID;
    Hpn.clear pn_to_node_ID;
    Htn.clear tn_to_node_ID;
    Ident.Hid.clear th_to_node_ID;
    Hstr.clear file_to_node_ID

  let reload_session () : unit =
    clear_tables ();
    reload_files cont env ~use_shapes:true;
    init_the_tree ()

  let replay_session () : unit =
    clear_tables ();
    (* TODO make replay print *)
    C.replay ~use_steps:false cont ~callback:C.replay_print ~remove_obsolete:false

  (* ----------------- treat_request -------------------- *)

  let rec treat_request (r,nid) = match r with
    | Prove (p,limit)   -> schedule_proof_attempt nid (get_prover p) limit
    | Transform (t, args) -> apply_transform nid t args
    | Strategy st -> run_strategy_on_task nid st
    | Save -> save_session ()
    | Reload ->
      begin
        reload_session ();
        P.notify (Session_Tree (build_the_tree ()))
      end
    | Get_Session_Tree -> P.notify (Session_Tree (build_the_tree ()))
    | Replay -> replay_session (); P.notify (Session_Tree (build_the_tree ()))
    | Command cmd ->
      begin
        match any_from_node_ID nid with
        | APn pn_id ->
          begin
            match (interp cont (Some pn_id) cmd) with
            | Transform (s,_t, args) -> treat_request (Transform (s, args), nid)
            | Query s -> P.notify (Message s)
            | Other (s, args) -> P.notify (Message "") (* TODO to be implemented *)
          end
        | _ -> P.notify (Message "Should be on a proof node") (* TODO make it an error *)
      end
    | _ -> assert false
(*    | Command cmd         ->
      | Open file_name      ->
      | Replay              -> *)


  let treat_requests () : bool =
    List.iter treat_request (P.get_requests ());
    true

  let _ = Unix_Scheduler.idle ~prio:1 treat_requests


end
