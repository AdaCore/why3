(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Wstdlib

module Hprover = Whyconf.Hprover

let debug = Debug.register_info_flag "session_itp"
    ~desc:"Pring@ debugging@ messages@ about@ Why3@ session@ \
           creation,@ reading@ and@ writing."

let debug_merge = Debug.lookup_flag "session_pairing"

let debug_stack_trace = Debug.lookup_flag "stack_trace"

type transID = int
type proofNodeID = int
type proofAttemptID = int
type fileID = int

let print_proofNodeID fmt id =
  Format.fprintf fmt "proofNodeID<%d>" id

let print_proofAttemptID fmt id =
  Format.fprintf fmt "proofAttemptID<%d>" id

type theory = {
  theory_name                   : Ident.ident;
  mutable theory_goals          : proofNodeID list;
  mutable theory_parent_name    : fileID;
  mutable theory_is_detached    : bool;
}

let theory_name t = t.theory_name
let theory_goals t = t.theory_goals

type proof_parent = Trans of transID | Theory of theory

type proof_attempt_node = {
  parent                 : proofNodeID;
  mutable prover         : Whyconf.prover;
  limit                  : Call_provers.resource_limit;
  mutable proof_state    : Call_provers.prover_result option;
  (* None means that the call was not done or never returned *)
  mutable proof_obsolete : bool;
  mutable proof_script   : string option;  (* non empty for external ITP *)
}

let set_proof_script pa file =
  assert (pa.proof_script = None);
  pa.proof_script <- Some file

type proof_node = {
  proofn_name                    : Ident.ident;
  proofn_expl                    : string;
  proofn_parent                  : proof_parent;
  proofn_attempts                : proofAttemptID Hprover.t;
  mutable proofn_transformations : transID list;
}

type transformation_node = {
  transf_name                      : string;
  transf_args                      : string list;
  mutable transf_subtasks          : proofNodeID list;
  transf_parent                    : proofNodeID;
  transf_is_detached               : bool;
}

type file_path = string list
let string_of_file_path p = String.concat "/" p

type file = {
  file_id                : int;
  mutable file_path      : file_path;
  (* access path to the source, in the normal order
  i.e. ["..";"foo.mlw"] *)
  file_format            : string option;
  file_is_detached       : bool;
  mutable file_theories  : theory list;
}

let file_id f = f.file_id
let file_path f = f.file_path
let file_format f = f.file_format
let file_theories f = f.file_theories

type any =
  | AFile of file
  | ATh of theory
  | ATn of transID
  | APn of proofNodeID
  | APa of proofAttemptID

let rec basename p =
  match p with
  | [] -> raise Not_found
  | [f] -> f
  | _ :: tl -> basename tl

let print_file_path fmt p = Format.fprintf fmt "%a" (Pp.print_list Pp.slash Pp.string) p

let fprintf_any fmt a =
  match a with
  | AFile f -> Format.fprintf fmt "<AFile [%a]>" print_file_path f.file_path
  | ATh th ->  Format.fprintf fmt "<ATh %s>" th.theory_name.Ident.id_string
  | ATn trid -> Format.fprintf fmt "<ATn %d>" trid
  | APn pnid -> Format.fprintf fmt "<APn %d>" pnid
  | APa paid -> Format.fprintf fmt "<APa %d>" paid

module Hpn = Hint
module Htn = Hint
module Hpan = Hint
module Hfile = Hint

type session = {
  proofAttempt_table            : proof_attempt_node Hint.t;
  mutable next_proofAttemptID   : int;
  proofNode_table               : proof_node Hint.t;
  mutable next_proofNodeID      : int;
  trans_table                   : transformation_node Hint.t;
  mutable next_transID          : int;
  mutable next_fileID           : int;
  session_dir                   : string; (** Absolute path *)
  session_files                 : file Hfile.t;
  session_sum_shape_table       : (Termcode.checksum * Termcode.shape) Hpn.t;
  session_prover_ids            : int Hprover.t;
  (* tasks *)
  session_raw_tasks : Task.task Hpn.t;
  session_task_tables : Trans.naming_table Hpn.t;
  (* proved status *)
  file_state: bool Hfile.t;
  th_state: bool Ident.Hid.t;
  tn_state: bool Htn.t;
  pn_state : bool Hpn.t;
}

let system_path s f =
  Sysutil.system_dependent_absolute_path s.session_dir f.file_path

let theory_parent s th =
  Debug.dprintf debug "[Session_itp.theory_parent] th.parent_name = %d@."
                th.theory_parent_name;
  Hfile.find s.session_files th.theory_parent_name

let session_iter_proof_attempt f s =
  Hint.iter f s.proofAttempt_table

(* This is not needed. Keeping it as information on the structure
type tree = {
    tree_node_id : proofNodeID;
    tree_goal_name : string;
    tree_proof_attempts : proof_attempt list; (* proof attempts on this node *)
    tree_transformations : (transID * string * tree list) list;
                                (* transformations on this node *)
  }
*)

(*
let rec get_tree s id : tree =
  let t = Hint.find s.proofNode_table id in
  let pal =
    Hprover.fold (fun _ pa acc -> pa.proofa_attempt::acc) t.proofn_attempts []
  in
  let trl = List.map (get_trans s) t.proofn_transformations in
  { tree_node_id = id;
    tree_goal_name = t.proofn_name.Ident.id_string;
    tree_proof_attempts = pal;
    tree_transformations = trl;
  }

and get_trans s id =
  let tr = Hint.find s.trans_table id in
  (id, tr.transf_name, List.map (get_tree s) tr.transf_subtasks)
*)

(*
let get_theories s =
  Hstr.fold
    (fun _fn f acc ->
     let c =
       List.map
         (fun th -> (th.theory_name.Ident.id_string, th.theory_goals))
         f.file_theories
     in
     (f,c) :: acc)
    s.session_files []
 *)

let get_files s = s.session_files
(* let get_file s name = Hstr.find s.session_files name *)
let get_dir s = s.session_dir

(*
let get_node (s : session) (n : int) =
  let _ = Hint.find s.proofNode_table n in n

let get_trans (s : session) (n : int) =
  let _ = Hint.find s.trans_table n in n
*)

(* Generation of new IDs *)
let gen_transID (s : session) =
  let id = s.next_transID in
  s.next_transID <- id + 1;
  id

let gen_proofNodeID (s : session) =
  let id = s.next_proofNodeID in
  s.next_proofNodeID <- id + 1;
  id

let gen_proofAttemptID (s : session) =
  let id = s.next_proofAttemptID in
  s.next_proofAttemptID <- id + 1;
  id

let gen_fileID (s : session) =
  let id = s.next_fileID in
  s.next_fileID <- id + 1;
  id

(* Get elements of the session tree *)

exception BadID

let get_proof_attempt_node (s : session) (id : proofAttemptID) =
  try
    Hint.find s.proofAttempt_table id
  with Not_found -> raise BadID

let get_proofNode (s : session) (id : proofNodeID) =
  try
    Hint.find s.proofNode_table id
  with Not_found -> raise BadID

let get_task s id =
  Hpn.find s.session_raw_tasks id

let get_task_name_table s n =
  let t = get_task s n in
  let table = try
    Hpn.find s.session_task_tables n
  with Not_found ->
    let ta = Args_wrapper.build_naming_tables t in
    Hpn.add s.session_task_tables n ta;
    ta
  in
  t,table

let get_transfNode (s : session) (id : transID) =
  try
    Hint.find s.trans_table id
  with Not_found -> raise BadID

let get_transformations (s : session) (id : proofNodeID) =
  (get_proofNode s id).proofn_transformations

let get_proof_attempt_ids (s : session) (id : proofNodeID) =
  (get_proofNode s id).proofn_attempts

let get_proof_attempt_parent (s : session) (a : proofAttemptID) =
  (get_proof_attempt_node s a).parent

let get_proof_attempts (s : session) (id : proofNodeID) =
  Hprover.fold (fun _ a l ->
                let pa = get_proof_attempt_node s a in
                pa :: l)
               (get_proofNode s id).proofn_attempts []

let get_sub_tasks (s : session) (id : transID) =
  (get_transfNode s id).transf_subtasks

let get_transf_args (s : session) (id : transID) =
  (get_transfNode s id).transf_args

let get_transf_name (s : session) (id : transID) =
  (get_transfNode s id).transf_name

let get_proof_name (s : session) (id : proofNodeID) =
  (get_proofNode s id).proofn_name

let get_proof_expl (s : session) (id : proofNodeID) =
  (get_proofNode s id).proofn_expl

let get_proof_parent (s : session) (id : proofNodeID) =
  (get_proofNode s id).proofn_parent

let get_trans_parent (s : session) (id : transID) =
  (get_transfNode s id).transf_parent

let goal_is_detached s pn =
  try let (_:Task.task) = get_task s pn in false
  with Not_found -> true

let transf_is_detached s tn =
  (get_transfNode s tn).transf_is_detached

let proof_attempt_is_detached s pa =
  let pa = get_proof_attempt_node s pa in
  goal_is_detached s pa.parent

let is_detached (s: session) (a: any) =
  match a with
  | AFile file -> file.file_is_detached
  | ATh th     -> th.theory_is_detached
  | ATn tn     -> transf_is_detached s tn
  | APn pn     -> goal_is_detached s pn
  | APa pa     -> proof_attempt_is_detached s pa

let rec get_encapsulating_theory s any =
  match any with
  | AFile _f -> assert (false)
  | ATh th -> th
  | ATn tn ->
      let pn_id = get_trans_parent s tn in
      get_encapsulating_theory s (APn pn_id)
  | APn pn ->
      (match get_proof_parent s pn with
      | Theory th -> th
      | Trans tn -> get_encapsulating_theory s (ATn tn)
      )
  | APa pa ->
      let pn = get_proof_attempt_parent s pa in
      get_encapsulating_theory s (APn pn)

let get_encapsulating_file s any =
  match any with
  | AFile f -> f
  | ATh th -> theory_parent s th
  | _ ->
      let th = get_encapsulating_theory s any in
      theory_parent s th

(*
let set_obsolete s paid b =
  let pa = get_proof_attempt_node s paid in
  pa.proof_obsolete <- b
 *)

let check_if_already_exists s pid t args =
    let sub_transfs = get_transformations s pid in
    List.exists (fun tr_id ->
      get_transf_name s tr_id = t && get_transf_args s tr_id = args &&
      not (is_detached s (ATn tr_id))) sub_transfs

(* Iterations functions on the session tree *)

let rec fold_all_any_of_transn s f acc trid =
  let tr = get_transfNode s trid in
  let acc =
    List.fold_left
      (fold_all_any_of_proofn s f)
      acc tr.transf_subtasks
  in
  f acc (ATn trid)

and fold_all_any_of_proofn s f acc pnid =
  let pn = get_proofNode s pnid in
  let acc =
    List.fold_left
      (fun acc trid ->
        fold_all_any_of_transn s f acc trid)
      acc pn.proofn_transformations
  in
  let acc =
    Hprover.fold
      (fun _p paid acc ->
        f acc (APa paid))
      pn.proofn_attempts acc
  in
  f acc (APn pnid)

let fold_all_any_of_theory s f acc th =
  let acc = List.fold_left (fold_all_any_of_proofn s f) acc th.theory_goals in
  f acc (ATh th)

let fold_all_any_of_file s f acc file =
  let acc =
    List.fold_left (fold_all_any_of_theory s f) acc file.file_theories in
  f acc (AFile file)

let fold_all_any s f acc any =
  match any with
  | AFile file -> fold_all_any_of_file s f acc file
  | ATh th -> fold_all_any_of_theory s f acc th
  | APn pn -> fold_all_any_of_proofn s f acc pn
  | ATn tn -> fold_all_any_of_transn s f acc tn
  | APa _ -> f acc any

let fold_all_session s f acc =
  let files = get_files s in
  Hfile.fold (fun _key file acc -> fold_all_any s f acc (AFile file)) files acc


let rec fold_all_sub_goals_of_proofn s f acc pnid =
  let pn = get_proofNode s pnid in
  let acc =
    List.fold_left
      (fun acc trid ->
         let tr = get_transfNode s trid in
         List.fold_left
           (fold_all_sub_goals_of_proofn s f)
           acc tr.transf_subtasks)
      acc pn.proofn_transformations
  in
  f acc pn

let goal_iter_proof_attempt s f g =
  fold_all_sub_goals_of_proofn
    s
    (fun _ pn -> Hprover.iter
                 (fun _ pa ->
                  let pan = get_proof_attempt_node s pa in
                  f pa pan)
                 pn.proofn_attempts) () g

let fold_all_sub_goals_of_theory s f acc th =
  List.fold_left (fold_all_sub_goals_of_proofn s f) acc th.theory_goals

(*
let theory_iter_proofn s f th =
  fold_all_sub_goals_of_theory s (fun _ -> f) () th
*)

let theory_iter_proof_attempt s f th =
  fold_all_sub_goals_of_theory s
    (fun _ pn -> Hprover.iter (fun _ pa ->
                             let pan = get_proof_attempt_node s pa in
                             f pa pan)
         pn.proofn_attempts) () th

let file_iter_proof_attempt s f file =
  List.iter
    (theory_iter_proof_attempt s f)
    (file_theories file)

let any_iter_proof_attempt s f any =
  match any with
  | AFile file -> file_iter_proof_attempt s f file
  | ATh th -> theory_iter_proof_attempt s f th
  | ATn tr ->
      let subgoals = get_sub_tasks s tr in
      List.iter (fun g -> goal_iter_proof_attempt s f g) subgoals
  | APn pn -> goal_iter_proof_attempt s f pn
  | APa pa -> f pa (get_proof_attempt_node s pa)



(**************)
(* Copy/Paste *)
(**************)

let get_any_parent s a =
  match a with
  | AFile _f -> None
  | ATh th  -> Some (AFile (theory_parent s th))
  | ATn tr  -> Some (APn (get_trans_parent s tr))
  | APn pn  ->
      (match (get_proofNode s pn).proofn_parent with
      | Theory th -> Some (ATh th)
      | Trans tr -> Some (ATn tr))
  | APa pa  ->
      Some (APn (get_proof_attempt_node s pa).parent)

(* True if bid is an ancestor of aid, false if not *)
let rec is_below s (aid: any) (bid: any) =
  aid = bid ||
  match (get_any_parent s aid) with
  | None     -> false
  | Some pid -> is_below s pid bid

open Format
open Ident

let print_proof_attempt fmt pa =
  fprintf fmt "%a tl=%d %a"
          Whyconf.print_prover pa.prover
          pa.limit.Call_provers.limit_time
          (Pp.print_option Call_provers.print_prover_result) pa.proof_state

let rec print_proof_node s (fmt: Format.formatter) p =
  let pn = get_proofNode s p in
  let sum,_ = Hpn.find s.session_sum_shape_table p in
  let parent = match pn.proofn_parent with
  | Theory t -> t.theory_name.id_string
  | Trans id -> (get_transfNode s id).transf_name
  in
  fprintf fmt
    "@[<hv 1> Goal %s;@ parent %s;@ sum %s;@ @[<hv 1>[%a]@]@ @[<hv 1>[%a]@]@]"
    pn.proofn_name.id_string parent
    (Termcode.string_of_checksum sum)
    (Pp.print_list Pp.semi print_proof_attempt)
      (Hprover.fold (fun _key e l ->
                     let e = get_proof_attempt_node s e in
                     e :: l)
        pn.proofn_attempts [])
      (Pp.print_list Pp.semi (print_trans_node s)) pn.proofn_transformations

and print_trans_node s fmt id =
  let tn = get_transfNode s id in
  let args = get_transf_args s id in
  let name = tn.transf_name in
  let l = tn.transf_subtasks in
  let parent = (get_proofNode s tn.transf_parent).proofn_name.id_string in
  fprintf fmt "@[<hv 1> Trans %s;@ args %a;@ parent %s;@ [%a]@]"
    name (Pp.print_list Pp.colon pp_print_string) args parent
    (Pp.print_list Pp.semi (print_proof_node s)) l

let print_theory s fmt th : unit =
  fprintf fmt "@[<hv 2> Theory %s;@ [%a]@]" th.theory_name.Ident.id_string
    (Pp.print_list Pp.semi (fun fmt a -> print_proof_node s fmt a)) th.theory_goals

let print_file s fmt (file, thl) =
  fprintf fmt "@[<hv 2> File [%a];@ [%a]@]" print_file_path file.file_path
    (Pp.print_list Pp.semi (print_theory s)) thl

let print_s s fmt =
  fprintf fmt "@[%a@]" (Pp.print_list Pp.semi (print_file s))

let _print_session fmt s =
  let l = Hfile.fold (fun _ f acc -> (f,f.file_theories) :: acc) (get_files s) [] in
  fprintf fmt "%a@." (print_s s) l;;


let empty_session ?from dir =
  let prover_ids =
    match from with
    | Some v -> v.session_prover_ids
    | None -> Hprover.create 7
  in
  { proofAttempt_table = Hint.create 97;
    next_proofAttemptID = 0;
    proofNode_table = Hint.create 97;
    next_proofNodeID = 0;
    trans_table = Hint.create 97;
    next_transID = 0;
    next_fileID = 0;
    session_dir = dir;
    session_files = Hfile.create 3;
    session_prover_ids = prover_ids;
    session_raw_tasks = Hpn.create 97;
    session_task_tables = Hpn.create 97;
    session_sum_shape_table = Hpn.create 97;
    file_state = Hfile.create 3;
    th_state = Ident.Hid.create 7;
    tn_state = Htn.create 97;
    pn_state = Hpn.create 97;
  }

(**************************************************)
(* proof node/attempt/transformation manipulation *)
(**************************************************)

exception AlreadyExist

let add_proof_attempt session prover limit state ~obsolete edit parentID =
  let pn = get_proofNode session parentID in
  try
    let _ = Hprover.find pn.proofn_attempts prover in
    raise AlreadyExist
  with Not_found ->
    let id = gen_proofAttemptID session in
    let pa = { parent = parentID;
               prover = prover;
               limit = limit;
               proof_state = state;
               proof_obsolete = obsolete;
               proof_script = edit } in
    Hprover.add pn.proofn_attempts prover id;
    Hint.replace session.proofAttempt_table id pa;
    id

let graft_proof_attempt ?file (s : session) (id : proofNodeID) (pr : Whyconf.prover)
    ~limit =
  let pn = get_proofNode s id in
  try
    let id = Hprover.find pn.proofn_attempts pr in
    let pa = Hint.find s.proofAttempt_table id in
    let pa = { pa with limit = limit;
               proof_state = None;
               proof_obsolete = false} in
    (* Hprover.replace pn.proofn_attempts pr id; useless *)
    Hint.replace s.proofAttempt_table id pa;
    id
  with Not_found ->
    add_proof_attempt s pr limit None ~obsolete:false file id


(* [mk_proof_node s n t p id] register in the session [s] a proof node
   of proofNodeID [id] of parent [p] of task [t] *)
let mk_proof_node ~shape_version ~expl (s : session) (n : Ident.ident) (t : Task.task)
    (parent : proof_parent) (node_id : proofNodeID) =
  let pn = { proofn_name = n;
             proofn_expl = expl;
             proofn_parent = parent;
             proofn_attempts = Hprover.create 7;
             proofn_transformations = [] } in
  Hint.add s.proofNode_table node_id pn;
  Hpn.add s.session_raw_tasks node_id t;
  let sum = Termcode.task_checksum ~version:shape_version t in
  let shape = Termcode.t_shape_task ~version:shape_version ~expl t in
  Hpn.add s.session_sum_shape_table node_id (sum,shape)

let mk_new_proof_node = mk_proof_node ~shape_version:Termcode.current_shape_version

let mk_proof_node_no_task (s : session) (n : Ident.ident)
    (parent : proof_parent) (node_id : proofNodeID) sum shape expl proved =
  let pn = { proofn_name = n;
             proofn_expl = expl;
             proofn_parent = parent;
             proofn_attempts = Hprover.create 7;
             proofn_transformations = [] } in
  Hint.add s.proofNode_table node_id pn;
  Hpn.add s.session_sum_shape_table node_id (sum,shape);
  Hint.add s.pn_state node_id proved

let mk_new_transf_proof_node (s : session) (parent_name : string)
    (tid : transID) (index : int) (t : Task.task) =
  let id = gen_proofNodeID s in
  let gid,expl,_ = Termcode.goal_expl_task ~root:false t in
  let goal_name = parent_name ^ "." ^ string_of_int index in
  let goal_name = Ident.id_register (Ident.id_derive goal_name gid) in
  mk_new_proof_node ~expl s goal_name t (Trans tid) id;
  id

let mk_transf_node (s : session) (id : proofNodeID) (node_id : transID)
                   (name : string) (args : string list) ~(proved:bool) ~(detached:bool)
                   (pnl : proofNodeID list) =
  let pn = get_proofNode s id in
  let tn = { transf_name = name;
             transf_args = args;
             transf_subtasks = pnl;
             transf_parent = id;
             transf_is_detached  = detached;
           }
  in
  Hint.add s.trans_table node_id tn;
  Htn.add s.tn_state node_id proved;
  pn.proofn_transformations <- node_id::pn.proofn_transformations


let graft_transf  (s : session) (id : proofNodeID) (name : string)
    (args : string list) (tl : Task.task list) =
  let tid = gen_transID s in
  let parent_name = (get_proofNode s id).proofn_name.Ident.id_string in
  let sub_tasks = List.mapi (mk_new_transf_proof_node s parent_name tid) tl in
  let proved = sub_tasks = [] in
  mk_transf_node s id tid name args ~proved sub_tasks ~detached:false;
  tid


let update_proof_attempt ?(obsolete=false) notifier s id pr st =
  try
    let n = get_proofNode s id in
    let paid = Hprover.find n.proofn_attempts pr in
    let pa = get_proof_attempt_node s paid in
    pa.proof_state <- Some st;
    pa.proof_obsolete <- obsolete;
    notifier (APa paid)
  with
  | BadID when not (Debug.test_flag debug_stack_trace) -> assert false


(* proved status *)


let tn_proved s tid = Htn.find_def s.tn_state false tid
let pn_proved s pid = Hpn.find_def s.pn_state false pid
let th_proved s th  =
  try Hid.find s.th_state th.theory_name
  with Not_found ->
    let b = theory_goals th = [] in
    Hid.add s.th_state th.theory_name b;
    b

let file_proved s f =
  try Hfile.find s.file_state f.file_id
  with Not_found ->
    let b = f.file_theories = [] in
    Hfile.add s.file_state f.file_id b;
    b

let pa_proved s paid =
  let pa = get_proof_attempt_node s paid in
  match pa.proof_state with
  | None -> false
  | Some pa ->
     begin
       match pa.Call_provers.pr_answer with
       | Call_provers.Valid -> true
       | _ -> false
     end

let any_proved s any : bool =
  match any with
  | AFile file -> file_proved s file
  | ATh th -> th_proved s th
  | ATn tn -> tn_proved s tn
  | APn pn -> pn_proved s pn
  | APa pa -> pa_proved s pa




(* status update *)


type notifier = any -> unit

let pa_ok pa =
  not pa.proof_obsolete &&
    match pa.proof_state
    with
    | Some { Call_provers.pr_answer = Call_provers.Valid} -> true
    | _ -> false

(* [update_goal_node c id] update the proof status of node id
   update is propagated to parents when required. *)

let update_file_node notification s f =
  let ths = f.file_theories in
  if ths = [] then
    (* No updates if ths is empty *)
    ()
  else
    let proved =
      List.for_all (fun th -> th.theory_is_detached || th_proved s th) ths
    in
    if proved <> file_proved s f then
      begin
        Hfile.replace s.file_state f.file_id proved;
        notification (AFile f);
      end

let update_theory_node notification s th =
  let goals = theory_goals th in
  let proved =
    List.for_all (fun pn -> goal_is_detached s pn || pn_proved s pn) goals
  in
  if proved <> th_proved s th then
    begin
      Debug.dprintf debug "[Session] setting theory %s to status proved=%b@."
                    th.theory_name.Ident.id_string proved;
      Hid.replace s.th_state (theory_name th) proved;
      notification (ATh th);
      try let p = theory_parent s th in
          update_file_node notification s p
      with Not_found when not (Debug.test_flag Debug.stack_trace) ->
        Format.eprintf "[Fatal] Session_itp.update_theory_node: parent missing@.";
        assert false
    end

let rec update_goal_node notification s id =
  let tr_list = get_transformations s id in
  let pa_list = get_proof_attempts s id in
  let proved =
    List.exists
      (fun tr -> not (transf_is_detached s tr) &&
                   tn_proved s tr) tr_list
    ||
      List.exists
        (fun pa -> not (goal_is_detached s pa.parent) &&
                     pa_ok pa) pa_list
  in
  if proved <> pn_proved s id then
    begin
      (* too noisy, uncomment if you really need it
      Debug.dprintf debug "[Session] setting goal node %a to status proved=%b@."
                    print_proofNodeID id proved;
       *)
      Hpn.replace s.pn_state id proved;
      notification (APn id);
      match get_proof_parent s id with
      | Trans trans_id -> update_trans_node notification s trans_id
      | Theory th -> update_theory_node notification s th
      | exception Not_found when not (Debug.test_flag Debug.stack_trace) ->
                  Format.eprintf "Session_itp.update_goal_node: parent missing@.";
                  Printexc.print_backtrace stderr;
                  assert false
    end

and update_trans_node notification s trid =
  let proof_list = get_sub_tasks s trid in
  let proved = List.for_all (fun pn -> goal_is_detached s pn || pn_proved s pn) proof_list in
  if proved <> tn_proved s trid then
    begin
      Htn.replace s.tn_state trid proved;
      notification (ATn trid);
      update_goal_node notification s (get_trans_parent s trid)
    end;
  (* Specific case in which we *always* need to call notification because
     transformation are created with proved=true when they don't have subtasks.
     This means they won't be updated in the next if so the parent goal will
     never get updated. *)
  if proof_list = [] then
    update_goal_node notification s (get_trans_parent s trid)


let update_any_node s notification a =
  match a with
  | APn id -> update_goal_node notification s id
  | ATn id -> update_trans_node notification s id
  | APa _ -> assert false
  | AFile f -> update_file_node notification s f
  | ATh th -> update_theory_node notification s th


let change_prover notification s id opr npr =
  try
    let n = get_proofNode s id in
    let paid = Hprover.find n.proofn_attempts opr in
    let pa = get_proof_attempt_node s paid in
    Hprover.remove n.proofn_attempts opr;
    pa.prover <- npr;
    pa.proof_obsolete <- true;
    Hprover.add n.proofn_attempts npr paid;
    update_goal_node notification s id
  with
  | Not_found -> ()
  | BadID when not (Debug.test_flag debug_stack_trace) -> assert false



(* Remove elements of the session tree *)

let remove_transformation (s : session) (id : transID) =
  let nt = get_transfNode s id in
  Hint.remove s.trans_table id;
  let pn = get_proofNode s nt.transf_parent in
  let trans_up = List.filter (fun tid -> tid != id) pn.proofn_transformations in
  pn.proofn_transformations <- trans_up

let remove_proof_attempt (s : session) (id : proofNodeID)
    (prover : Whyconf.prover) =
  let pn = get_proofNode s id in
  let pa = Hprover.find pn.proofn_attempts prover in
  Hprover.remove pn.proofn_attempts prover;
  Hint.remove s.proofAttempt_table pa

let remove_proof_attempt_pa s (id: proofAttemptID) =
  let pa = get_proof_attempt_node s id in
  let pn = pa.parent in
  let prover = pa.prover in
  remove_proof_attempt s pn prover

let mark_obsolete s (id: proofAttemptID) =
  let pa = get_proof_attempt_node s id in
  pa.proof_obsolete <- true


exception RemoveError

let remove_subtree ~(notification:notifier) ~(removed:notifier) s (n: any) =
  let remove (n: any) =
    match n with
    | ATn tn -> remove_transformation s tn
    | APa pa -> remove_proof_attempt_pa s pa
    | AFile f -> Hfile.remove s.session_files f.file_id
    | APn pn ->
       let node = Hint.find s.proofNode_table pn in
       Hint.remove s.proofNode_table pn;
       begin
         match node.proofn_parent with
         | Theory th ->
            th.theory_goals <- List.filter ((<>) pn) th.theory_goals
         | Trans tr ->
            let nt = get_transfNode s tr in
            nt.transf_subtasks <- List.filter ((<>) pn) nt.transf_subtasks
       end
    | ATh th ->
       let f = theory_parent s th in
       f.file_theories <- List.filter ((!=) th) f.file_theories
  in
  match n with
  | (AFile _ | APn _ | ATh _) when not (is_detached s n) ->
               raise RemoveError
  | _ ->
     let p = get_any_parent s n in
     fold_all_any s (fun _ x -> remove x; removed x) () n;
     Opt.iter (update_any_node s notification) p

(****************************)
(*     session opening      *)
(****************************)

let db_filename = "why3session.xml"
let shape_filename = "why3shapes"
let compressed_shape_filename = "why3shapes.gz"
let session_dir_for_save = ref "."

exception LoadError of Xml.element * string
exception SessionFileError of string

let bool_attribute field r def =
  try
    match List.assoc field r.Xml.attributes with
    | "true" -> true
    | "false" -> false
    | _ -> assert false
  with Not_found -> def

let int_attribute_def field r def =
  try
    int_of_string (List.assoc field r.Xml.attributes)
  with Not_found | Invalid_argument _ -> def

let string_attribute_def field r def=
  try
    List.assoc field r.Xml.attributes
  with Not_found -> def

let string_attribute_opt field r =
  try
    Some (List.assoc field r.Xml.attributes)
  with Not_found -> None

let string_attribute field r =
  try
    List.assoc field r.Xml.attributes
  with Not_found ->
    eprintf "[Error] missing required attribute '%s' from element '%s'@."
      field r.Xml.name;
    assert false

let default_unknown_result =
     {
       Call_provers.pr_answer = Call_provers.Failure "";
       Call_provers.pr_time = 0.0;
       Call_provers.pr_output = "";
       Call_provers.pr_status = Unix.WEXITED 0;
       Call_provers.pr_steps = -1;
       Call_provers.pr_model = Model_parser.default_model;
     }

let load_result r =
  match r.Xml.name with
  | "result" ->
     let status = string_attribute "status" r in
     let answer =
       match status with
       | "valid" -> Call_provers.Valid
       | "invalid" -> Call_provers.Invalid
       | "unknown" -> Call_provers.Unknown ""
       | "timeout" -> Call_provers.Timeout
       | "outofmemory" -> Call_provers.OutOfMemory
       | "failure" -> Call_provers.Failure ""
       | "highfailure" -> Call_provers.HighFailure
       | "steplimitexceeded" -> Call_provers.StepLimitExceeded
       | "stepslimitexceeded" -> Call_provers.StepLimitExceeded
       | s ->
          Warning.emit
            "[Warning] Session.load_result: unexpected status '%s'@." s;
          Call_provers.HighFailure
     in
     let time =
       try float_of_string (List.assoc "time" r.Xml.attributes)
       with Not_found -> 0.0
     in
     let steps =
       try int_of_string (List.assoc "steps" r.Xml.attributes)
       with Not_found -> -1
     in
     {
       Call_provers.pr_answer = answer;
       Call_provers.pr_time = time;
       Call_provers.pr_output = "";
       Call_provers.pr_status = Unix.WEXITED 0;
       Call_provers.pr_steps = steps;
       Call_provers.pr_model = Model_parser.default_model;
     }
  | "undone" | "unedited" -> default_unknown_result
  | s ->
    Warning.emit "[Warning] Session.load_result: unexpected element '%s'@."
      s;
    default_unknown_result

let load_option attr g =
  try Some (List.assoc attr g.Xml.attributes)
  with Not_found -> None

let load_ident elt =
  let name = string_attribute "name" elt in
  let attrs = List.fold_left
      (fun acc label ->
         match label with
         | {Xml.name = "label"} ->
           let name = string_attribute "name" label in
           Ident.Sattr.add (Ident.create_attribute name) acc
         | _ -> acc
      ) Ident.Sattr.empty elt.Xml.elements in
  let preid =
    try
      let load_exn attr g = List.assoc attr g.Xml.attributes in
      let file = load_exn "locfile" elt in
      let lnum =  int_of_string (load_exn "loclnum" elt) in
      let cnumb = int_of_string (load_exn "loccnumb" elt) in
      let cnume = int_of_string (load_exn "loccnume" elt) in
      let pos = Loc.user_position file lnum cnumb cnume in
      Ident.id_user ~attrs name pos
    with Not_found | Invalid_argument _ ->
      Ident.id_fresh ~attrs name in
  Ident.id_register preid

(* [load_goal s op p g id] loads the goal of parent [p] from the xml
   [g] of nodeID [id] into the session [s] *)
let rec load_goal session old_provers parent g id =
  match g.Xml.name with
  | "goal" ->
    let gname = load_ident g in
    (* even if sum and shape are not in the XML file but in the shape
  file, these attributes are there thanks to ~fixattr on
  Xml.from_file *)
    let csum = string_attribute_def "sum" g "" in
    let sum = Termcode.checksum_of_string csum in
    let shape =
      try Termcode.shape_of_string (List.assoc "shape" g.Xml.attributes)
      with Not_found -> Termcode.shape_of_string ""
    in
    let expl = string_attribute_def "expl" g "" in
    let proved = bool_attribute "proved" g false in
    mk_proof_node_no_task session gname parent id sum shape expl proved;
    List.iter (load_proof_or_transf session old_provers id) g.Xml.elements;
  | "label" -> ()
  | s ->
    Warning.emit "[Warning] Session.load_goal: unexpected element '%s'@." s

(* [load_proof_or_transf s op pid a] load either a proof attempt or a
   transformation of parent id [pid] from the xml [a] into the session
   [s] *)
and load_proof_or_transf session old_provers pid a =
  match a.Xml.name with
    | "proof" ->
      begin
        let prover = string_attribute "prover" a in
        try
          let prover = int_of_string prover in
          let (p,timelimit,steplimit,memlimit) = Mint.find prover old_provers in
          let res = match a.Xml.elements with
            | [r] -> load_result r
            | [] -> default_unknown_result
            | _ ->
              Warning.emit "[Error] Too many result elements@.";
              raise (LoadError (a,"too many result elements"))
          in
          let edit = load_option "edited" a in
          let edit = match edit with None | Some "" -> None | _ -> edit in
          let obsolete = bool_attribute "obsolete" a false in
          let timelimit = int_attribute_def "timelimit" a timelimit in
	  let steplimit = int_attribute_def "steplimit" a steplimit in
          let memlimit = int_attribute_def "memlimit" a memlimit in
          let limit = { Call_provers.limit_time  = timelimit;
                        Call_provers.limit_mem   = memlimit;
                        Call_provers.limit_steps = steplimit; }
          in
          ignore(add_proof_attempt session p limit (Some res) ~obsolete edit pid)
        with Failure _ | Not_found ->
          Warning.emit "[Error] prover id not listed in header '%s'@." prover;
          raise (LoadError (a,"prover not listing in header"))
      end
    | "transf" ->
      let trname = string_attribute "name" a in
      let rec get_args id =
        match string_attribute_opt ("arg"^(string_of_int id)) a with
        | Some arg -> arg :: (get_args (id+1))
        | None -> []
      in
      let args = get_args 1 in
      let tid = gen_transID session in
      let proved = bool_attribute "proved" a false in
      let subtasks_ids =
        List.rev (List.fold_left
                    (fun goals th ->
                       match th.Xml.name with
                       | "goal" -> (gen_proofNodeID session) :: goals
                       | _ -> goals) [] a.Xml.elements)
      in
      mk_transf_node session pid tid trname args ~proved subtasks_ids ~detached:true;
      List.iter2
        (load_goal session old_provers (Trans tid))
        a.Xml.elements subtasks_ids;
    | "metas" -> ()
    | "label" -> ()
    | s ->
      Warning.emit
        "[Warning] Session.load_proof_or_transf: unexpected element '%s'@."
        s

let load_theory session parent_name old_provers (path,acc) th =
  match th.Xml.name with
  | "theory" ->
    let thname = load_ident th in
    let goals = List.rev (List.fold_left (fun goals th -> match th.Xml.name with
        | "goal" -> (gen_proofNodeID session) :: goals
        | _ -> goals) [] th.Xml.elements) in
    let mth = { theory_name = thname;
                theory_is_detached = true;
                theory_goals = goals;
                theory_parent_name = parent_name;
              } in
    List.iter2
      (load_goal session old_provers (Theory mth))
      th.Xml.elements goals;
    let proved = bool_attribute "proved" th false in
    Hid.add session.th_state thname proved;
    (path,mth::acc)
  | "path" ->
     let fn = string_attribute "name" th in
     (fn::path,acc)
  | s ->
    Warning.emit "[Warning] Session.load_theory: unexpected element '%s'@."
      s;
    (path,acc)

let load_file session old_provers f =
  match f.Xml.name with
  | "file" ->
    let fn = string_attribute_opt "name" f in
    let fmt = load_option "format" f in
    let fid = gen_fileID session in
    let path,ft =
      List.fold_left
        (load_theory session fid old_provers) ([],[]) f.Xml.elements
    in
    let path = match path,fn with
      | [], Some fn ->
         let l = Sysutil.system_independent_path_of_file fn in
         Debug.dprintf debug "Loaded path from concrete file name: %a@." print_file_path l;
         l
      | [],None -> assert false
      | p,_ -> List.rev p
    in
    let mf = { file_id = fid;
               file_path = path;
               file_format = fmt;
               file_is_detached = true;
               file_theories = List.rev ft;
             } in
    Hfile.add session.session_files fid mf;
    old_provers
  | "prover" ->
    (* The id is just for the session file *)
    let id = string_attribute "id" f in
    begin
      try
        let id = int_of_string id in
        let name = string_attribute "name" f in
        let version = string_attribute "version" f in
        let altern = string_attribute_def "alternative" f "" in
        let timelimit = int_attribute_def "timelimit" f 5 in
        let steplimit = int_attribute_def "steplimit" f 1 in
        let memlimit = int_attribute_def "memlimit" f 1000 in
        let p = {Whyconf.prover_name = name;
                 prover_version = version;
                 prover_altern = altern} in
        Mint.add id (p,timelimit,steplimit,memlimit) old_provers
      with Failure _ ->
        Warning.emit "[Warning] Session.load_file: unexpected non-numeric prover id '%s'@." id;
        old_provers
    end
  | s ->
    Warning.emit "[Warning] Session.load_file: unexpected element '%s'@." s;
    old_provers

let build_session (s : session) xml =
  match xml.Xml.name with
  | "why3session" ->
    let shape_version = int_attribute_def "shape_version" xml 1 in
    Debug.dprintf debug "[Info] load_session: shape version is %d@\n" shape_version;
    (* just to keep the old_provers somewhere *)
    let old_provers =
      List.fold_left (load_file s) Mint.empty xml.Xml.elements
    in
    Mint.iter
      (fun id (p,_,_,_) ->
         Debug.dprintf debug "prover %d: %a@." id Whyconf.print_prover p;
         Hprover.replace s.session_prover_ids p id)
      old_provers;
    Debug.dprintf debug "[Info] load_session: done@\n";
    shape_version
  | s ->
    Warning.emit "[Warning] Session.load_session: unexpected element '%s'@."
                 s;
    Termcode.current_shape_version

exception ShapesFileError of string

module ReadShapes (C:Compress.S) = struct

let shape = Buffer.create 97

let read_sum_and_shape ch =
  let sum = Bytes.create 32 in
  let nsum = C.input ch sum 0 32 in
  if nsum = 0 then raise End_of_file;
  if nsum <> 32 then
    begin
      try
        C.really_input ch sum nsum (32-nsum)
      with End_of_file ->
        raise
          (ShapesFileError
             ("shapes files corrupted (checksum '" ^
                 (Bytes.sub_string sum 0 nsum) ^
                 "' too short), ignored"))
    end;
  if try C.input_char ch <> ' ' with End_of_file -> true then
      raise (ShapesFileError "shapes files corrupted (space missing), ignored");
    Buffer.clear shape;
    try
      while true do
        let c = C.input_char ch in
        if c = '\n' then raise Exit;
        Buffer.add_char shape c
      done;
      assert false
    with
      | End_of_file ->
        raise (ShapesFileError "shapes files corrupted (premature end of file), ignored");
      | Exit -> Bytes.unsafe_to_string sum, Buffer.contents shape


  let has_shapes = ref true

  let fix_attributes ch name attrs =
    if name = "goal" then
      try
        let sum,shape = read_sum_and_shape ch in
        let attrs =
          try
            let old_sum = List.assoc "sum" attrs in
            if sum <> old_sum then
              begin
                Format.eprintf "old sum = %s ; new sum = %s@." old_sum sum;
                raise
                  (ShapesFileError
                     "shapes files corrupted (sums do not correspond)")
              end;
            attrs
          with Not_found -> ("sum", sum) :: attrs
        in
        ("shape",shape) :: attrs
      with _ -> has_shapes := false; attrs
    else attrs

let read_xml_and_shapes xml_fn compressed_fn =
  has_shapes := true;
  try
    let ch = C.open_in compressed_fn in
    let xml = Xml.from_file ~fixattrs:(fix_attributes ch) xml_fn in
    C.close_in ch;
    xml, !has_shapes
  with Sys_error msg ->
    raise (ShapesFileError ("cannot open shapes file for reading: " ^ msg))
end

module ReadShapesNoCompress = ReadShapes(Compress.Compress_none)
module ReadShapesCompress = ReadShapes(Compress.Compress_z)

let read_file_session_and_shapes dir xml_filename =
  try
  let compressed_shape_filename =
    Filename.concat dir compressed_shape_filename
  in
  if Sys.file_exists compressed_shape_filename then
    if Compress.compression_supported then
     ReadShapesCompress.read_xml_and_shapes
       xml_filename compressed_shape_filename
    else
      begin
        Warning.emit "[Warning] could not read goal shapes because \
                                Why3 was not compiled with compress support@.";
        Xml.from_file xml_filename, false
      end
  else
    let shape_filename = Filename.concat dir shape_filename in
    if Sys.file_exists shape_filename then
      ReadShapesNoCompress.read_xml_and_shapes xml_filename shape_filename
    else
      begin
        Xml.from_file xml_filename, false
      end
with e ->
  Warning.emit "[Warning] failed to read goal shapes: %s@."
    (Printexc.to_string e);
  Xml.from_file xml_filename, false

let load_session (dir : string) =
  let session = empty_session dir in
  let file = Filename.concat dir db_filename in
  let shape_version =
    (* If the xml is present we read it, otherwise we consider it empty *)
    if Sys.file_exists file then
      try
(*
        Termcode.reset_dict ();
*)
        let xml,has_shapes =
          read_file_session_and_shapes dir file in
        try
          let shape_version = build_session session xml.Xml.content in
          if has_shapes then Some shape_version else None
        with Sys_error msg ->
          failwith ("Open session: sys error " ^ msg)
      with
      | Sys_error msg ->
        (* xml does not exist yet *)
        raise (SessionFileError msg)
      | Xml.Parse_error s ->
        Warning.emit "XML database corrupted, ignored (%s)@." s;
        raise (SessionFileError "XML corrupted")
    else None
  in
    session, shape_version

(* -------------------- merge/update session --------------------------- *)

(** Pairing *)

module Goal = struct
  type 'a t = proofNodeID * session
  let checksum (id,s) = Some (fst (Hpn.find s.session_sum_shape_table id))
  let shape (id,s)    = snd (Hpn.find s.session_sum_shape_table id)
  let name (id,s)     = (get_proofNode s id).proofn_name
end

module AssoGoals = Termcode.Pairing(Goal)(Goal)

let found_obsolete = ref false
let found_detached = ref false
(* FIXME: distinguish found_new_goals and found_detached *)

let save_detached_proof s parent old_pa_n =
  let old_pa = old_pa_n in
  ignore (add_proof_attempt s old_pa.prover old_pa.limit
                            old_pa.proof_state ~obsolete:old_pa.proof_obsolete old_pa.proof_script
                            parent)

let rec save_detached_goal old_s s parent detached_goal_id id =
  let detached_goal = get_proofNode old_s detached_goal_id in
  let (sum,shape) = Hpn.find old_s.session_sum_shape_table detached_goal_id in
  mk_proof_node_no_task s detached_goal.proofn_name parent id sum shape
                        detached_goal.proofn_expl false;
  Hprover.iter (fun _ pa ->
                let pa = get_proof_attempt_node old_s pa in
                save_detached_proof s id pa) detached_goal.proofn_attempts;
  List.iter (save_detached_trans old_s s id) detached_goal.proofn_transformations;
  let new_trans = (get_proofNode s id) in
  new_trans.proofn_transformations <- List.rev new_trans.proofn_transformations


and save_detached_goals old_s detached_goals_id s parent =
  List.map
    (fun detached_goal ->
     let id = gen_proofNodeID s in
     save_detached_goal old_s s parent detached_goal id;
     id)
    detached_goals_id

and save_detached_trans old_s s parent_id old_id =
    let old_tr = get_transfNode old_s old_id in
    let name = old_tr.transf_name in
    let args = old_tr.transf_args in
    let id = gen_transID s in
    let subtasks_id = List.map (fun _ -> gen_proofNodeID s) old_tr.transf_subtasks in
    let proved = subtasks_id = [] in
    mk_transf_node s parent_id id name args ~proved subtasks_id ~detached:true;
    List.iter2 (fun pn_id -> save_detached_goal old_s s (Trans id) pn_id)
      old_tr.transf_subtasks subtasks_id

let save_detached_theory parent_name old_s detached_theory s =
  let goalsID =
    save_detached_goals old_s detached_theory.theory_goals s (Theory detached_theory)
  in
  assert (detached_theory.theory_parent_name = parent_name);
  detached_theory.theory_goals <- goalsID;
  detached_theory.theory_is_detached <- true;
  detached_theory

let merge_proof new_s ~goal_obsolete new_goal _ old_pa_n =
  let old_pa = old_pa_n in
  let obsolete = goal_obsolete || old_pa.proof_obsolete in
  found_obsolete := obsolete || !found_obsolete;
  ignore (add_proof_attempt new_s old_pa.prover old_pa.limit
    old_pa.proof_state ~obsolete old_pa.proof_script
    new_goal)

exception NoProgress

let () = Exn_printer.register
    (fun fmt e ->
      match e with
      | NoProgress ->
          Format.fprintf fmt "The transformation made no progress.\n"
      | _ -> raise e)

let apply_trans_to_goal ~allow_no_effect s env name args id =
  let task,table = get_task_name_table s id in
  let subtasks = Trans.apply_transform_args name env args table task in
  (* If any generated task is equal to the former task, then we made no
     progress because we need to prove more lemmas than before *)
  match subtasks with
  | [t'] when Task.task_equal t' task && not allow_no_effect ->
     Debug.dprintf debug "[apply_trans_to_goal] apply_transform made no progress@.";
     raise NoProgress
  | _ -> subtasks


let add_registered_transformation s env old_tr goal_id =
  let goal = get_proofNode s goal_id in
  try
    (* check if transformation already present with the same parameters.
       this should always fail and raise Not_found *)
    let _tr = List.find (fun transID -> (get_transfNode s transID).transf_name = old_tr.transf_name &&
                        List.fold_left2 (fun b new_arg old_arg -> new_arg = old_arg && b) true
                                        (get_transfNode s transID).transf_args
                                        old_tr.transf_args)
        goal.proofn_transformations in
    Printexc.print_backtrace stderr;
    Format.eprintf "[add_registered_transformation] FATAL transformation already present@.";
    exit 2
  with Not_found ->
    let subgoals =
      apply_trans_to_goal ~allow_no_effect:true s env old_tr.transf_name old_tr.transf_args goal_id
    in
    graft_transf s goal_id old_tr.transf_name old_tr.transf_args subgoals

let rec merge_goal ~shape_version env new_s old_s ~goal_obsolete old_goal new_goal_id =
  Hprover.iter (fun k pa ->
                let pa = get_proof_attempt_node old_s pa in
                merge_proof new_s ~goal_obsolete new_goal_id k pa)
               old_goal.proofn_attempts;
  List.iter
    (merge_trans ~shape_version env old_s new_s new_goal_id)
    old_goal.proofn_transformations;
  let new_goal_node = get_proofNode new_s new_goal_id in
  new_goal_node.proofn_transformations <- List.rev new_goal_node.proofn_transformations;
  update_goal_node (fun _ -> ()) new_s new_goal_id

and merge_trans ~shape_version env old_s new_s new_goal_id old_tr_id =
  let old_tr = get_transfNode old_s old_tr_id in
  let old_subtasks = List.map (fun id -> id,old_s)
      old_tr.transf_subtasks in
  try
    match
    (* add_registered_transformation actually apply the transformation. It can fail *)
    try Some (add_registered_transformation new_s env old_tr new_goal_id)
    with _ -> None
  with
  | Some new_tr_id ->
    let new_tr = get_transfNode new_s new_tr_id in
    (* attach the session to the subtasks to be able to instantiate Pairing *)
    let new_subtasks = List.map (fun id -> id,new_s)
                                new_tr.transf_subtasks in
    let associated,detached =
      AssoGoals.associate ~use_shapes:(shape_version <> None)
                          old_subtasks new_subtasks
    in
    List.iter
      (function
        | ((new_goal_id,_), Some ((old_goal_id,_), goal_obsolete)) ->
           merge_goal ~shape_version env new_s old_s ~goal_obsolete
                      (get_proofNode old_s old_goal_id) new_goal_id
        | ((id,s), None) ->
           Debug.dprintf debug "[merge_trans] missed new subgoal: %s@."
                         (get_proofNode s id).proofn_name.Ident.id_string;
           found_detached := true)
      associated;
    (* save the detached goals *)
    let detached = List.map (fun (id,_) ->
                Debug.dprintf debug "[merge_trans] detached subgoal: %s@."
                              (get_proofNode old_s id).proofn_name.Ident.id_string;
                found_detached := true;
                id) detached in
    new_tr.transf_subtasks <-
      new_tr.transf_subtasks @
        save_detached_goals old_s detached new_s (Trans new_tr_id)
  | None ->
     Debug.dprintf debug
                   "[Session_itp.merge_trans] transformation failed: %s@."
                   old_tr.transf_name;
     save_detached_trans old_s new_s new_goal_id old_tr_id;
     found_detached := true
  with e when not (Debug.test_flag debug_stack_trace) ->
    Printexc.print_backtrace stderr;
    Format.eprintf "[Session_itp.merge_trans] FATAL unexpected exception: %a@." Exn_printer.exn_printer e;
    exit 2


let merge_theory ~shape_version env old_s old_th s th : unit =
  let get_goal_name goal_node =
    let name = goal_node.proofn_name in
    try
      let (_,_,l) = Theory.restore_path name in
      String.concat "." l
    with Not_found -> name.Ident.id_string in
  let old_goals_table = Hstr.create 7 in
  (* populate old_goals_table *)
  List.iter
    (fun id ->
       let pn = get_proofNode old_s id in
       Hstr.add old_goals_table (get_goal_name pn) id)
    old_th.theory_goals;
  let new_goals = ref [] in
  (* merge goals *)
  List.iter
    (fun ng_id ->
       try
         let new_goal = get_proofNode s ng_id in
         (* look for old_goal with matching name *)
         let new_goal_name = get_goal_name new_goal in
         let old_id = Hstr.find old_goals_table new_goal_name in
         let old_goal = get_proofNode old_s old_id in
         Hstr.remove old_goals_table new_goal_name;
         let goal_obsolete =
             let s1 = fst (Hpn.find s.session_sum_shape_table ng_id) in
             let s2 = fst (Hpn.find old_s.session_sum_shape_table old_id) in
             Debug.dprintf debug "[merge_theory] goal has checksum@.";
             not (Termcode.equal_checksum s1 s2)
         in
         if goal_obsolete then
           found_obsolete := true;
         merge_goal ~shape_version env s old_s ~goal_obsolete old_goal ng_id
       with
       | Not_found ->
         (* if no goal of matching name is found store it to look for
            matching shape *)
         new_goals := (ng_id,s) :: !new_goals)
    th.theory_goals;
  (* check shapes if no old_goal is found with matching name *)
  (* attach the session to the subtasks to be able to instantiate Pairing *)
  let detached_goals = Hstr.fold (fun _key g tl -> (g,old_s) :: tl) old_goals_table [] in
  let associated,detached =
    AssoGoals.associate ~use_shapes:(shape_version <> None)
                        detached_goals !new_goals
  in
  List.iter (function
      | ((new_goal_id,_), Some ((old_goal_id,_), goal_obsolete)) ->
        Debug.dprintf debug "[merge_theory] pairing paired one goal, yeah !@.";
        merge_goal ~shape_version env s old_s ~goal_obsolete
                   (get_proofNode old_s old_goal_id) new_goal_id
      | ((id,_), None) ->
         Debug.dprintf debug "[merge_theory] pairing found missed sub goal: %s@."
                       (get_proofNode s id).proofn_name.Ident.id_string;
        found_detached := true)
    associated;
  (* store the detached goals *)
  let detached = List.map (fun (a,_) -> a) detached in
  th.theory_goals <- th.theory_goals @ save_detached_goals old_s detached s (Theory th)

(* add a theory and its goals to a session. if a previous theory is
   provided in merge try to merge the new theory with the previous one *)
let make_theory_section ?merge ~detached (s:session) parent_name (th:Theory.theory)
  : theory =
  let add_goal =
    match merge with
    | Some(_,_,_,Some v) ->
       fun parent goal id ->
       let name,expl,task = Termcode.goal_expl_task ~root:true goal in
       mk_proof_node ~shape_version:v ~expl s name task parent id
    | _ ->
       fun parent goal id ->
       let name,expl,task = Termcode.goal_expl_task ~root:true goal in
       mk_new_proof_node ~expl s name task parent id
  in
  let tasks = Task.split_theory th None None in
  let goalsID = List.map (fun _ -> gen_proofNodeID s) tasks in
  let theory = { theory_name = th.Theory.th_name;
                 theory_is_detached = detached;
                 theory_goals = goalsID;
                 theory_parent_name = parent_name;
               } in
  let parent = Theory theory in
  List.iter2 (add_goal parent) tasks goalsID;
  begin
    match merge with
    | Some (old_s, old_th, env, shape_version) ->
       merge_theory ~shape_version env old_s old_th s theory
    | _ -> if tasks <> [] then found_detached := true (* should be found_new_goals instead of found_detached *)
  end;
  theory

(* add a why file to a session *)
let add_file_section (s:session) (fn:string) ~file_is_detached
    (theories:Theory.theory list) format : file =
  let fn = Sysutil.relativize_filename s.session_dir fn in
  Debug.dprintf debug "[Session_itp.add_file_section] fn = %a@." print_file_path fn;
(*
  if Hfile.mem s.session_files fn then
    begin
      Printexc.print_backtrace stderr;
      Format.eprintf "[session] FATAL: file %s already in database@." fn;
      exit 2
    end
  else
*)
  let fid = gen_fileID s in
    let f = { file_id = fid;
              file_path = fn;
              file_format = format;
              file_is_detached = file_is_detached;
              file_theories = [] }
    in
    Hfile.add s.session_files fid f;
    let theories = List.map (make_theory_section ~detached:false s fid) theories in
    f.file_theories <- theories;
    f

(* add a why file to a session and try to merge its theories with the
   provided ones with matching names *)
let merge_file_section ~shape_version ~old_ses ~old_theories ~file_is_detached ~env
    (s:session) (fn:string) (theories:Theory.theory list) format
    : unit =
  Debug.dprintf debug_merge "[Session_itp.merge_file_section] fn = %s@." fn;
  let f = add_file_section s fn ~file_is_detached [] format in
  let fid = f.file_id in
  let theories,detached =
    let old_th_table = Hstr.create 7 in
    List.iter
      (fun th -> Hstr.add old_th_table th.theory_name.Ident.id_string th)
      old_theories;
    let add_theory (th: Theory.theory) =
      (* look for a theory with same name *)
      let theory_name = th.Theory.th_name.Ident.id_string in
      try
        (* if we found one, we remove it from the table and merge it *)
        let old_th = Hstr.find old_th_table theory_name in
        Debug.dprintf debug_merge "[Session_itp.merge_file_section] theory found: %s@." theory_name;
        Hstr.remove old_th_table theory_name;
        make_theory_section ~detached:false
                            ~merge:(old_ses,old_th,env,shape_version) s fid th
      with Not_found ->
        (* if no theory was found we make a new theory section *)
        Debug.dprintf debug_merge "[Session_itp.merge_file_section] theory NOT FOUND in old session: %s@." theory_name;
        make_theory_section ~detached:false s fid th
    in
    let theories = List.map add_theory theories in
    (* we save the remaining, detached *)
    let detached = Hstr.fold
                     (fun _key th tl ->
                      (save_detached_theory fid old_ses th s) :: tl)
                     old_th_table [] in
    theories, List.rev detached
  in
  f.file_theories <- theories @ detached;
  update_file_node (fun _ -> ()) s f

let read_file env ?format fn =
  let theories = Env.read_file Env.base_language env ?format fn in
  let ltheories =
    Mstr.fold
      (fun name th acc ->
        (* Hack : with WP [name] and [th.Theory.th_name.Ident.id_string] *)
        let th_name =
          Ident.id_register (Ident.id_derive name th.Theory.th_name) in
         match th.Theory.th_name.Ident.id_loc with
           | Some l -> (l,th_name,th)::acc
           | None   -> (Loc.dummy_position,th_name,th)::acc)
      theories []
  in
  let th =  List.sort
      (fun (l1,_,_) (l2,_,_) -> Loc.compare l1 l2)
      ltheories
  in
  List.map (fun (_,_,a) -> a) th

let merge_file  ~shape_version env (ses : session) (old_ses : session) file =
  let format = file_format file in
  let old_theories = file_theories file in
  let file_name = Sysutil.system_dependent_absolute_path (get_dir old_ses) (file_path file) in
  Debug.dprintf debug "merging file %s@." file_name;
  try
    let new_theories = read_file env file_name ?format in
    merge_file_section
      ses ~shape_version ~old_ses ~old_theories ~file_is_detached:false
      ~env file_name new_theories format;
    None
  with e -> (* TODO: capture only parsing and typing errors *)
    merge_file_section
      ses ~shape_version ~old_ses ~old_theories ~file_is_detached:true
      ~env file_name [] format;
    Some e

let merge_files ~shape_version env (ses:session)  (old_ses : session) =
  Debug.dprintf debug "merging files from old session@.";
  let errors =
    Hfile.fold
      (fun _ f acc ->
       match merge_file ~shape_version env ses old_ses f with
       | None -> acc
       | Some e -> e :: acc)
      (get_files old_ses) []
  in
  (* recompute shapes if absent or obsolete *)
  if shape_version <> Some Termcode.current_shape_version then
    begin
      Hpn.clear ses.session_sum_shape_table;
      let version = Termcode.current_shape_version in
      fold_all_session
        ses
        (fun () n ->
         match n with
         | APn id ->
            let sum,shape =
              try
                let t = get_task ses id in
                let _,expl,_ = Termcode.goal_expl_task ~root:false t in
                let sum = Termcode.task_checksum ~version t in
                let shape = Termcode.t_shape_task ~version ~expl t in
                sum, shape
              with Not_found -> (* detached goal *)
                Termcode.dumb_checksum, Termcode.shape_of_string ""
            in
            Hpn.add ses.session_sum_shape_table id (sum,shape)
         | _ -> ()
        )
        ()
    end;
  (errors,!found_obsolete,!found_detached)


(************************)
(* saving state on disk *)
(************************)

module Mprover = Whyconf.Mprover
module PHprover = Whyconf.Hprover

open Format

let save_string = Pp.html_string

type save_ctxt = {
  prover_ids : int PHprover.t;
  provers : (int * int * int * int) Mprover.t;
  ch_shapes : Compress.Compress_z.out_channel;
}

let get_used_provers_with_stats session =
  let prover_table = PHprover.create 5 in
  session_iter_proof_attempt
    (fun _ pa ->
      (* record mostly used pa.proof_timelimit pa.proof_memlimit *)
      let prover = pa.prover in
      let timelimits,steplimits,memlimits =
        try PHprover.find prover_table prover
        with Not_found ->
          let x = (Hashtbl.create 5,Hashtbl.create 5,Hashtbl.create 5) in
          PHprover.add prover_table prover x;
          x
      in
      let lim_time = pa.limit.Call_provers.limit_time in
      let lim_mem = pa.limit.Call_provers.limit_mem in
      let lim_steps = pa.limit.Call_provers.limit_steps in
      let tf = try Hashtbl.find timelimits lim_time with Not_found -> 0 in
      let sf = try Hashtbl.find steplimits lim_steps with Not_found -> 0 in
      let mf = try Hashtbl.find memlimits lim_mem with Not_found -> 0 in
      Hashtbl.replace timelimits lim_time (tf+1);
      Hashtbl.replace steplimits lim_steps (sf+1);
      Hashtbl.replace memlimits lim_mem (mf+1))
    session;
  prover_table

let get_prover_to_save prover_ids p (timelimits,steplimits,memlimits) provers =
  let mostfrequent_timelimit,_ =
    Hashtbl.fold
      (fun t f ((_,f') as t') -> if f > f' then (t,f) else t')
      timelimits
      (0,0)
  in
  let mostfrequent_steplimit,_ =
    Hashtbl.fold
      (fun s f ((_,f') as s') -> if f > f' then (s,f) else s')
      steplimits
      (0,0)
  in
  let mostfrequent_memlimit,_ =
    Hashtbl.fold
      (fun m f ((_,f') as m') -> if f > f' then (m,f) else m')
      memlimits
      (0,0)
  in
  let id =
    try
      PHprover.find prover_ids p
    with Not_found ->
      (* we need to find an unused prover id *)
      let occurs = Hashtbl.create 7 in
      PHprover.iter (fun _ n -> Hashtbl.add occurs n ()) prover_ids;
      let id = ref 0 in
      try
        while true do
          try
            let _ = Hashtbl.find occurs !id in incr id
          with Not_found -> raise Exit
        done;
        assert false
      with Exit ->
        PHprover.add prover_ids p !id;
        !id
  in
  Mprover.add p (id,mostfrequent_timelimit,mostfrequent_steplimit,mostfrequent_memlimit) provers

let opt pr lab fmt = function
  | None -> ()
  | Some s -> fprintf fmt "@ %s=\"%a\"" lab pr s

let opt_string = opt save_string

let save_prover fmt id (p,mostfrequent_timelimit,mostfrequent_steplimit,mostfrequent_memlimit) =
  let steplimit =
    if mostfrequent_steplimit < 0 then None else Some mostfrequent_steplimit
  in
  fprintf fmt "@\n@[<h><prover@ id=\"%i\"@ name=\"%a\"@ \
               version=\"%a\"%a@ timelimit=\"%d\"%a@ memlimit=\"%d\"/>@]"
    id save_string p.Whyconf.prover_name save_string p.Whyconf.prover_version
    (fun fmt s -> if s <> "" then fprintf fmt "@ alternative=\"%a\""
        save_string s)
    p.Whyconf.prover_altern
    mostfrequent_timelimit
    (opt pp_print_int "steplimit") steplimit
    mostfrequent_memlimit

let save_string_attrib name fmt s =
  if s <> "" then fprintf fmt "@ %s=\"%a\"" name save_string s

let save_option_def name fmt opt =
  match opt with
  | None -> ()
  | Some s -> save_string_attrib name fmt s

let save_bool_def name def fmt b =
  if b <> def then fprintf fmt "@ %s=\"%b\"" name b

let save_int_def name def fmt n =
  if n <> def then fprintf fmt "@ %s=\"%d\"" name n

let save_result fmt r =
  let steps = if  r.Call_provers.pr_steps >= 0 then
                Some  r.Call_provers.pr_steps
              else
                None
  in
  fprintf fmt "<result@ status=\"%s\"%a/>"
    (match r.Call_provers.pr_answer with
       | Call_provers.Valid -> "valid"
       | Call_provers.Failure _ -> "failure"
       | Call_provers.Unknown _ -> "unknown"
       | Call_provers.HighFailure -> "highfailure"
       | Call_provers.Timeout -> "timeout"
       | Call_provers.OutOfMemory -> "outofmemory"
       | Call_provers.StepLimitExceeded -> "steplimitexceeded"
       | Call_provers.Invalid -> "invalid")
    (opt pp_print_int "steps") steps

let save_status fmt s =
  match s with
  | Some result -> save_result fmt result
  | None -> fprintf fmt "<undone/>"

let save_proof_attempt fmt ((id,tl,sl,ml),a) =
  fprintf fmt
    "@\n@[<h><proof@ prover=\"%i\"%a%a%a%a%a>"
    id
    (save_int_def "timelimit" tl) (a.limit.Call_provers.limit_time)
    (save_int_def "steplimit" sl) (a.limit.Call_provers.limit_steps)
    (save_int_def "memlimit" ml) (a.limit.Call_provers.limit_mem)
    (save_bool_def "obsolete" false) a.proof_obsolete
    (save_option_def "edited") a.proof_script;
  save_status fmt a.proof_state;
  fprintf fmt "</proof>@]"

let save_ident fmt id =
  let n =
    try
      let (_,_,l) = Theory.restore_path id in
      if l = [] then raise Not_found;
      String.concat "." l
    with Not_found -> id.Ident.id_string
  in
  fprintf fmt "name=\"%a\"" save_string n

let rec save_goal s ctxt fmt pnid =
  let pn = get_proofNode s pnid in
  fprintf fmt
    "@\n@[<v 0>@[<h><goal@ %a%a%a>@]"
    save_ident pn.proofn_name
    (save_string_attrib "expl") pn.proofn_expl
    (save_bool_def "proved" false) (pn_proved s pnid);
  let (sum,shape) = Hpn.find s.session_sum_shape_table pnid in
  Compress.Compress_z.output_string ctxt.ch_shapes (Termcode.string_of_checksum sum);
  Compress.Compress_z.output_char ctxt.ch_shapes ' ';
  Compress.Compress_z.output_string ctxt.ch_shapes (Termcode.string_of_shape shape);
  Compress.Compress_z.output_char ctxt.ch_shapes '\n';
  let l = Hprover.fold
      (fun _ a acc ->
       let a = get_proof_attempt_node s a in
       (Mprover.find a.prover ctxt.provers, a) :: acc)
      pn.proofn_attempts [] in
  let l = List.sort (fun ((i1,_,_,_),_) ((i2,_,_,_),_) -> compare i1 i2) l in
  List.iter (save_proof_attempt fmt) l;
  let l =
    List.fold_left (fun acc t -> (t,get_transfNode s t) :: acc) [] pn.proofn_transformations
  in
  let l = List.sort (fun (_,t1) (_,t2) ->
                     compare t1.transf_name t2.transf_name) l in
  List.iter (save_trans s ctxt fmt) l;
  fprintf fmt "@]@\n</goal>";

and save_trans s ctxt fmt (tid,t) =
  let arg_id = ref 0 in
  let save_arg fmt s =
    arg_id := !arg_id + 1;
    fprintf fmt "arg%i=\"%a\"" !arg_id save_string s
  in
  fprintf fmt "@\n@[<hov 1>@[<h><transf@ name=\"%a\"%a %a>@]"
    save_string t.transf_name
    (save_bool_def "proved" false) (tn_proved s tid)
    (Pp.print_list Pp.space save_arg) t.transf_args;
  List.iter (save_goal s ctxt fmt) t.transf_subtasks;
  fprintf fmt "@]@\n</transf>"

let save_theory s ctxt fmt t =
  (* Saving empty theories takes space in session files. Not saving them should
     be harmless. *)
  if t.theory_goals <> [] then
  begin
    fprintf fmt
      "@\n@[<v 1>@[<h><theory@ %a%a>@]"
      save_ident t.theory_name
      (save_bool_def "proved" false) (th_proved s t);
    List.iter (save_goal s ctxt fmt) t.theory_goals;
    fprintf fmt "@]@\n</theory>"
  end

let save_file s ctxt fmt _ f =
  fprintf fmt
    "@\n@[<v 0>@[<h><file%a%a>@]"
    (opt_string "format") f.file_format
    (save_bool_def "proved" false) (file_proved s f);
  List.iter (fun s -> fprintf fmt "@\n@[<hov 1><path@ name=\"%s\"/>@]" s) f.file_path;
  List.iter (save_theory s ctxt fmt) f.file_theories;
  fprintf fmt "@]@\n</file>"

let save fname shfname session =
  let ch = open_out fname in
  let chsh = Compress.Compress_z.open_out shfname in
  let fmt = formatter_of_out_channel ch in
  fprintf fmt "<?xml version=\"1.0\" encoding=\"UTF-8\"?>@\n";
  fprintf fmt "<!DOCTYPE why3session PUBLIC \"-//Why3//proof session v5//EN\"@ \"http://why3.lri.fr/why3session.dtd\">@\n";
  fprintf fmt "@[<v 0><why3session shape_version=\"%d\">"
    Termcode.current_shape_version;
  let prover_ids = session.session_prover_ids in
  let provers =
    PHprover.fold (get_prover_to_save prover_ids)
      (get_used_provers_with_stats session) Mprover.empty
  in
  let provers_to_save =
    Mprover.fold
      (fun p (id,mostfrequent_timelimit,mostfrequent_steplimit,mostfrequent_memlimit) acc ->
        Mint.add id (p,mostfrequent_timelimit,mostfrequent_steplimit,mostfrequent_memlimit) acc)
      provers Mint.empty
  in
  Mint.iter (save_prover fmt) provers_to_save;
  let ctxt = { prover_ids = prover_ids; provers = provers; ch_shapes = chsh } in
  Hfile.iter (save_file session ctxt fmt) session.session_files;
  fprintf fmt "@]@\n</why3session>";
  fprintf fmt "@.";
  close_out ch;
  Compress.Compress_z.close_out chsh


let save_session (s : session) =
  let f = Filename.concat s.session_dir db_filename in
  Sysutil.backup_file f;
  let fs = Filename.concat s.session_dir shape_filename in
  Sysutil.backup_file fs;
  let fz = Filename.concat s.session_dir compressed_shape_filename in
  Sysutil.backup_file fz;
  session_dir_for_save := s.session_dir;
  let fs = if Compress.compression_supported then fz else fs in
  save f fs s

(**********************)
(* Edition of session *)
(**********************)

let find_file_from_path s path =
  let files = get_files s in
  let file =
    Hfile.fold
      (fun _ f acc -> if f.file_path = path then Some f else acc) files None
  in
  match file with
  | None -> raise Not_found
  | Some file -> file

let rename_file s from_file to_file =
  let src = Sysutil.relativize_filename s.session_dir from_file in
  let dst = Sysutil.relativize_filename s.session_dir to_file in
  let file = find_file_from_path s src in
  file.file_path <- dst;
  src,dst
