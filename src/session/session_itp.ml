(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
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
  mutable proof_script   : Sysutil.file_path option;  (* non empty for external ITP *)
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

type file = {
  file_id                : int;
  mutable file_path      : Sysutil.file_path;
  file_format            : Env.fformat;
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

let fprintf_any fmt a =
  match a with
  | AFile f -> Format.fprintf fmt "<AFile [%a]>" Sysutil.print_file_path f.file_path
  | ATh th ->  Format.fprintf fmt "<ATh %s>" th.theory_name.Ident.id_string
  | ATn trid -> Format.fprintf fmt "<ATn %d>" trid
  | APn pnid -> Format.fprintf fmt "<APn %d>" pnid
  | APa paid -> Format.fprintf fmt "<APa %d>" paid

module Hpn = Hint
module Htn = Hint
module Hpan = Hint
module Hfile = Hint

type sshape = {
  mutable shape_version     : Termcode.sum_shape_version option;
  (* New shapes handling *)
  (* Global shape declarations *)
  session_global_shapes     : Termcode.Gshape.gshape;
  (* New shapes *)
  session_bound_shape_table : (Termcode.bound_shape) Hpn.t;
  (* Old shapes (mutually exclusive with session_global_shapes and
     session_sum_shape_table_new *)
  session_shape_table       : Termcode.shape Hpn.t;
  session_sum_table         : Termcode.checksum Hpn.t;
}

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
  session_prover_ids            : int Hprover.t;
  shapes                        : sshape;
  (* tasks *)
  session_raw_tasks : Task.task Hpn.t;
  session_task_tables : Trans.naming_table Hpn.t;
  (* proved status *)
  file_state: bool Hfile.t;
  th_state: bool Ident.Hid.t;
  tn_state: bool Htn.t;
  pn_state : bool Hpn.t;
}

(* This module handles all session-internal shape/checksum operations *)
module Sshape = struct

  open Termcode

  let add_shape s goal_id shape =
    let sshape = s.shapes in
    match shape with
    | Old_shape shape ->
        Hpn.add sshape.session_shape_table goal_id shape
    | Bound_shape shape ->
        Hpn.add sshape.session_bound_shape_table goal_id shape

  let add_empty_shape s goal_id =
    match s.shapes.shape_version with
    | None -> ()
    | Some v ->
       if is_bound_sum_shape_version v then
         Hpn.add s.shapes.session_bound_shape_table goal_id empty_bound_shape
       else
         Hpn.add s.shapes.session_shape_table goal_id empty_shape

  let get_shape s goal_id =
    match s.shapes.shape_version with
    | None -> assert false
    | Some v ->
       if is_bound_sum_shape_version v then
         let shape = try Hpn.find s.shapes.session_bound_shape_table goal_id with
                     | Not_found -> empty_bound_shape in
         Bound_shape shape
       else
         let shape = try Hpn.find s.shapes.session_shape_table goal_id with
                     | Not_found -> empty_shape in
         Old_shape shape

  let compute_and_add_shape s ~expl goal_id t =
    let sshapes = s.shapes in
    match sshapes.shape_version with
    | None -> ()
    | Some version ->
       if is_bound_sum_shape_version version then
         let gs = sshapes.session_global_shapes in
         let shape = Gshape.t_bound_shape_task gs ~version ~expl t in
         Hpn.add sshapes.session_bound_shape_table goal_id shape
       else
         let shape = t_shape_task ~version ~expl t in
         Hpn.add sshapes.session_shape_table goal_id shape

  let find_sum s goal_id =
    try Hpn.find s.shapes.session_sum_table goal_id with
    | Not_found -> Termcode.dumb_checksum

  let add_sum s goal_id sum =
    Hpn.add s.shapes.session_sum_table goal_id sum

  let clear s =
    Gshape.clear_gs s.shapes.session_global_shapes;
    Hpn.clear s.shapes.session_bound_shape_table;
    Hpn.clear s.shapes.session_shape_table;
    Hpn.clear s.shapes.session_sum_table

  let clear_only_shape s =
    Gshape.clear_gs s.shapes.session_global_shapes;
    Hpn.clear s.shapes.session_bound_shape_table;
    Hpn.clear s.shapes.session_shape_table

  let copy_global_shape from_s to_s =
    Termcode.Gshape.copy from_s.session_global_shapes to_s.session_global_shapes

end

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
          (Pp.print_option (Call_provers.print_prover_result ~json_model:false))
          pa.proof_state

let rec print_proof_node s (fmt: Format.formatter) p =
  let pn = get_proofNode s p in
  let sum = Sshape.find_sum s p in
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
  fprintf fmt "@[<hv 2> File [%a];@ [%a]@]" Sysutil.print_file_path file.file_path
    (Pp.print_list Pp.semi (print_theory s)) thl

let print_s s fmt =
  fprintf fmt "@[%a@]" (Pp.print_list Pp.semi (print_file s))

let _print_session fmt s =
  let l = Hfile.fold (fun _ f acc -> (f,f.file_theories) :: acc) (get_files s) [] in
  fprintf fmt "%a@." (print_s s) l;;


let empty_session ?sum_shape_version ?from dir =
  let prover_ids =
    match from with
    | Some s -> s.session_prover_ids
    | None -> Hprover.create 7
  in
  let version = match sum_shape_version,from with
    | None, None -> Some Termcode.current_sum_shape_version
    | Some v, None -> Some v
    | None, Some s -> s.shapes.shape_version
    | Some _, Some _ ->
       failwith "Session_itp.empty_session: cannot use both optional arguments at the same time"
  in
  let empty_shapes =
    {
      shape_version = version;
      session_global_shapes = Termcode.Gshape.create ();
      session_bound_shape_table = Hpn.create 97;
      session_shape_table = Hpn.create 97;
      session_sum_table = Hpn.create 97;
    } in
  (* It is necessary to copy the global_shapes as potentially detached goal
     shape will refer to an old global_shape assignment: we need to propagate it
     An example is: reload with parse error then reload again with different
     source code.
  *)
  (match from with
  | None -> ()
  | Some from -> Sshape.copy_global_shape from.shapes empty_shapes);
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
    shapes = empty_shapes;
    session_raw_tasks = Hpn.create 97;
    session_task_tables = Hpn.create 97;
    file_state = Hfile.create 3;
    th_state = Ident.Hid.create 7;
    tn_state = Htn.create 97;
    pn_state = Hpn.create 97;
  }

(**************************************************)
(* proof node/attempt/transformation manipulation *)
(**************************************************)

exception AlreadyExist

let add_proof_attempt session prover limit state ~obsolete (edit : Sysutil.file_path option) parentID =
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
let mk_proof_node ~expl (s : session) (n : Ident.ident) (t : Task.task)
    (parent : proof_parent) (node_id : proofNodeID) =
  let pn = { proofn_name = n;
             proofn_expl = expl;
             proofn_parent = parent;
             proofn_attempts = Hprover.create 7;
             proofn_transformations = [] } in
  Hint.add s.proofNode_table node_id pn;
  Hpn.add s.session_raw_tasks node_id t;
  match s.shapes.shape_version with
  | Some version ->
     let sum = Termcode.task_checksum ~version t in
     Sshape.add_sum s node_id sum;
     Sshape.compute_and_add_shape s ~expl node_id t
  | None -> ()

let mk_proof_node_no_task (s : session) (n : Ident.ident)
    (parent : proof_parent) (node_id : proofNodeID) sum shape expl proved =
  let pn = { proofn_name = n;
             proofn_expl = expl;
             proofn_parent = parent;
             proofn_attempts = Hprover.create 7;
             proofn_transformations = [] } in
  Hint.add s.proofNode_table node_id pn;
  Sshape.add_sum s node_id sum;
  Sshape.add_shape s node_id shape;
  Hint.add s.pn_state node_id proved

let mk_new_transf_proof_node (s : session) (parent_name : string)
    (tid : transID) (index : int) (t : Task.task) =
  let id = gen_proofNodeID s in
  let gid,expl,_ = Termcode.goal_expl_task ~root:false t in
  let goal_name = parent_name ^ "." ^ string_of_int index in
  let goal_name = Ident.id_register (Ident.id_derive goal_name gid) in
  mk_proof_node ~expl s goal_name t (Trans tid) id;
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
  | BadID when not (Debug.test_flag Debug.stack_trace) -> assert false

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
        Warning.emit "[Fatal] Session_itp.update_theory_node: parent missing@.";
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
                  Warning.emit "Session_itp.update_goal_node: parent missing@.";
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
  | BadID when not (Debug.test_flag Debug.stack_trace) -> assert false

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
    Warning.emit "[Error] missing required attribute '%s' from element '%s'@."
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

let load_result a (path,acc) r =
  match r.Xml.name with
  | "result" ->
     begin
       match acc with
       | Some _ ->
          Warning.emit "[Error] Too many result elements@.";
          raise (LoadError (a,"too many result elements"))
       | None -> ()
     end;
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
     let res = {
       Call_provers.pr_answer = answer;
       Call_provers.pr_time = time;
       Call_provers.pr_output = "";
       Call_provers.pr_status = Unix.WEXITED 0;
       Call_provers.pr_steps = steps;
       Call_provers.pr_model = Model_parser.default_model;
       }
     in (path,Some res)
  | "undone" | "unedited" -> (path,acc)
  | "path" ->
     let fn = string_attribute "name" r in
     (Sysutil.add_to_path path fn,acc)
  | s ->
    Warning.emit "[Warning] Session.load_result: unexpected element '%s'@."
      s;
    (path,acc)

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
      match session.shapes.shape_version with
      | Some version ->
         Termcode.shape_of_string ~version
           (try List.assoc "shape" g.Xml.attributes
           with Not_found -> "")
      | None -> Termcode.(shape_of_string ~version:current_sum_shape_version "")
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
          let path,res =
            List.fold_left (load_result a) (Sysutil.empty_path,None) a.Xml.elements
          in
          let res = match res with
            | None -> default_unknown_result
            | Some r -> r
          in
          let edit =
            if Sysutil.is_empty_path path then
              match load_option "edited" a with
              | None | Some "" -> None
              | Some s -> Some (Sysutil.system_independent_path_of_file s)
            else
              Some path
          in
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
     (Sysutil.add_to_path path fn,acc)
  | s ->
    Warning.emit "[Warning] Session.load_theory: unexpected element '%s'@."
      s;
    (path,acc)

let load_file session old_provers f =
  match f.Xml.name with
  | "file" ->
    (* This "name" attribute only exists in old sessions *)
    let fn = string_attribute_opt "name" f in
    let fid = gen_fileID session in
    let path,ft =
      List.fold_left
        (load_theory session fid old_provers) (Sysutil.empty_path,[]) f.Xml.elements
    in
    let path =
      if Sysutil.is_empty_path path then
        match fn with
        | Some fn ->
           let l = Sysutil.system_independent_path_of_file fn in
           Debug.dprintf debug "Loaded path from concrete file name: %a@." Sysutil.print_file_path l;
           l
        | None -> assert false
      else path
    in
    let fmt =
      (* If the session is ill-formed and the format is absent, we use the
         extension to decide the format *)
      let def_fmt =
        Env.get_format (Format.asprintf "%a" Sysutil.print_file_path path) in
      string_attribute_def "format" f def_fmt in
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


exception ShapesFileError of string

(*
let get_version (xml: Xml.t) =
  match xml.Xml.content.Xml.name with
  | "why3session" ->
    let shape_version = int_attribute_def "shape_version" xml.Xml.content 1 in
    shape_version
  | s ->
    Warning.emit "[Warning] Session.load_session: unexpected element '%s'@."
                 s;
    Termcode.current_shape_version
 *)

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

(* Read the first part of the shapes: a list of shapes which are then referred
   as H1 ... Hn in the shape corresponding to tasks *)
let rec read_global_buffer gs ch =
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
  | Exit ->
      let g_shape = Buffer.contents shape in
      Buffer.clear shape;
      if g_shape <> "" then
        (Termcode.Gshape.add_shape_g gs g_shape; read_global_buffer gs ch)

  let sum_shape_version = ref None

  let fix_attributes gs ch name attrs =
    match name with
    | "why3session" ->
       begin try
           let sv = List.assoc "shape_version" attrs in
           let sv = Termcode.string_to_sum_shape_version sv in
           sum_shape_version := Some sv;
           if Termcode.is_bound_sum_shape_version sv then read_global_buffer gs ch;
           attrs
         with Not_found ->
           Warning.emit "Session file does not indicate any shape version@.";
           attrs
       end
    | "goal" ->
       begin
         try
           let sum,shape = read_sum_and_shape ch in
           let attrs =
             try
               let old_sum = List.assoc "sum" attrs in
               if sum <> old_sum then
                 begin
                   Warning.emit "old sum = %s ; new sum = %s@." old_sum sum;
                   raise
                     (ShapesFileError
                        "shapes files corrupted (sums do not correspond)")
                 end;
               attrs
             with Not_found -> ("sum", sum) :: attrs
           in
           ("shape",shape) :: attrs
         with ShapesFileError msg ->
           Warning.emit "Error while reading shape file: %s. Continuing without shapes." msg;
           sum_shape_version := None; attrs
       end
    | _ -> attrs

let read_xml_and_shapes gs xml_fn compressed_fn =
  sum_shape_version := None;
  try
    let ch = C.open_in compressed_fn in
    let xml = Xml.from_file ~fixattrs:(fix_attributes gs ch) xml_fn in
    C.close_in ch;
    xml, !sum_shape_version
  with Sys_error msg ->
    raise (ShapesFileError ("cannot open shapes file for reading: " ^ msg))
end

module ReadShapesNoCompress = ReadShapes(Compress.Compress_none)
module ReadShapesCompress = ReadShapes(Compress.Compress_z)

let read_file_session_and_shapes gs dir xml_filename =
  let compressed_shape_filename =
      Filename.concat dir compressed_shape_filename
    in
    if Sys.file_exists compressed_shape_filename then
      if Compress.compression_supported then
        ReadShapesCompress.read_xml_and_shapes gs
          xml_filename compressed_shape_filename
      else
        begin
          Warning.emit "[Warning] could not read goal shapes because \
                        Why3 was not compiled with compress support@.";
          Xml.from_file xml_filename, None
        end
    else
      let shape_filename = Filename.concat dir shape_filename in
      if Sys.file_exists shape_filename then
        ReadShapesNoCompress.read_xml_and_shapes gs
          xml_filename shape_filename
      else
        begin
          Warning.emit "[Warning] could not find goal shapes file@.";
          Xml.from_file xml_filename, None
        end

let build_session ?sum_shape_version (s : session) xml : unit =
  match xml.Xml.name with
  | "why3session" ->
     let sv = try
         Some (Termcode.string_to_sum_shape_version (List.assoc "shape_version" xml.Xml.attributes))
       with Not_found -> None
     in
     Debug.dprintf debug "[Info] build_session: ~sum_shape_version is %a@\n"
       (Pp.print_option Termcode.pp_sum_shape_version) sum_shape_version;
     Debug.dprintf debug "[Info] build_session: sv (from XML structure) is %a@\n"
       (Pp.print_option Termcode.pp_sum_shape_version) sv;
     Debug.dprintf debug "[Info] build_session: s.shapes.shape_version is %a@\n"
       (Pp.print_option Termcode.pp_sum_shape_version) s.shapes.shape_version;
    (* just to keep the old_provers somewhere *)
    let old_provers =
      List.fold_left (load_file s) Mint.empty xml.Xml.elements
    in
    Mint.iter
      (fun id (p,_,_,_) ->
         Debug.dprintf debug "prover %d: %a@." id Whyconf.print_prover p;
         Hprover.replace s.session_prover_ids p id)
      old_provers;
    Debug.dprintf debug "[Info] load_session: done@\n"
  | s ->
    Warning.emit "[Warning] Session.load_session: unexpected element '%s'@."
      s

let load_session (dir : string) =
  let file = Filename.concat dir db_filename in
  if Sys.file_exists file then
    try
      let xml,sum_shape_version =
        read_file_session_and_shapes (Termcode.Gshape.create ())
          (* session.shapes.session_global_shapes *) dir file
      in
      let session = empty_session ?sum_shape_version dir in
      build_session ?sum_shape_version session xml.Xml.content;
      session
    with
    | Sys_error msg ->
       (* xml does not exist yet *)
       raise (SessionFileError msg)
    | Xml.Parse_error s ->
       Warning.emit "XML database corrupted, ignored (%s)@." s;
       raise (SessionFileError "XML corrupted")
  else empty_session dir

(* -------------------- merge/update session --------------------------- *)

(** Pairing *)

module Goal_Shape = struct
  type 'a t = proofNodeID * session
  let checksum (id,s) =
    try Some (Hpn.find s.shapes.session_sum_table id) with
    | Not_found -> None
  let shape (id,s)    =
    try
      (Hpn.find s.shapes.session_shape_table id, Termcode.Gshape.empty_bshape)
    with Not_found -> (Termcode.empty_shape, Termcode.Gshape.empty_bshape)
  let name (id,s)     = (get_proofNode s id).proofn_name
end

module OldAssoGoals = Termcode.Pairing(Goal_Shape)(Goal_Shape)

module Goal_Bound_Shape = struct

  type 'a t = proofNodeID * session

  let checksum (id,s) =
    try Some (Hpn.find s.shapes.session_sum_table id) with
    | Not_found -> None
  let shape (id,s) =
    try
      let li = Hpn.find s.shapes.session_bound_shape_table id in
      (Termcode.Gshape.goal_and_expl_shapes s.shapes.session_global_shapes li, li)
    with Not_found -> (Termcode.empty_shape, Termcode.Gshape.empty_bshape)
  let name (id,s) = (get_proofNode s id).proofn_name

end


module BoundAssoGoals = Termcode.Pairing(Goal_Bound_Shape)(Goal_Bound_Shape)

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
  let sum = Sshape.find_sum old_s detached_goal_id in
  let shape = Sshape.get_shape old_s detached_goal_id in
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

(* State transformation exception that are fatal (any exception that is not part
   of transformation normal behavior) *)
let is_fatal e =
  Generic_arg_trans_utils.(match e with
  | NoProgress | Arg_trans _ | Arg_trans_decl _ | Arg_trans_missing _
  | Arg_trans_term _ | Arg_trans_term2 _ | Arg_trans_term3 _
  | Arg_trans_pattern _ | Arg_trans_type _ | Arg_bad_hypothesis _
  | Cannot_infer_type _ | Unnecessary_terms _ | Remove_unknown _
  | Args_wrapper.Parse_error _
  | Args_wrapper.Arg_expected _ | Args_wrapper.Arg_theory_not_found _
  | Args_wrapper.Arg_expected_none _ | Args_wrapper.Arg_qid_not_found _
  | Args_wrapper.Arg_pr_not_found _ | Args_wrapper.Arg_error _
  | Args_wrapper.Arg_parse_type_error _ | Trans.Unnecessary_arguments _
  | Reflection.NoReification -> false
  | _ -> true)

let () = Exn_printer.register
    (fun fmt e ->
      match e with
      | NoProgress ->
          Format.fprintf fmt "The transformation made no progress.\n"
      | _ -> raise e)

let apply_trans_to_goal ~allow_no_effect s env name args id =
  let task,table = get_task_name_table s id in
  let lang = (get_encapsulating_file s (APn id)).file_format in
  let subtasks = Trans.apply_transform_args name env args table lang task in
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
    Warning.emit "[add_registered_transformation] FATAL transformation already present@.";
    exit 2
  with Not_found ->
    let subgoals =
      apply_trans_to_goal ~allow_no_effect:true s env old_tr.transf_name old_tr.transf_args goal_id
    in
    graft_transf s goal_id old_tr.transf_name old_tr.transf_args subgoals

let rec merge_goal env new_s old_s ~goal_obsolete old_goal new_goal_id =
  Hprover.iter (fun k pa ->
                let pa = get_proof_attempt_node old_s pa in
                merge_proof new_s ~goal_obsolete new_goal_id k pa)
               old_goal.proofn_attempts;
  List.iter
    (merge_trans env old_s new_s new_goal_id)
    old_goal.proofn_transformations;
  let new_goal_node = get_proofNode new_s new_goal_id in
  new_goal_node.proofn_transformations <- List.rev new_goal_node.proofn_transformations;
  update_goal_node (fun _ -> ()) new_s new_goal_id

and merge_trans env old_s new_s new_goal_id old_tr_id =
  let old_tr = get_transfNode old_s old_tr_id in
  let old_subtasks = List.map (fun id -> id,old_s)
      old_tr.transf_subtasks in
  try
    match
    (* add_registered_transformation actually apply the transformation. It can fail *)
    try Some (add_registered_transformation new_s env old_tr new_goal_id)
    with
    | e when not (Debug.test_flag Debug.stack_trace) ->
        (* Non fatal exception are silently ignored *)
        if is_fatal e then
        Warning.emit "FATAL unexpected exception during application of %s: %a@."
          old_tr.transf_name Exn_printer.exn_printer e;
        (* Notify the user but still allow her to load why3 *)
        None
  with
  | Some new_tr_id ->
    let new_tr = get_transfNode new_s new_tr_id in
    (* attach the session to the subtasks to be able to instantiate Pairing *)
    let new_subtasks = List.map (fun id -> id,new_s)
                                new_tr.transf_subtasks in
    let associated,detached =
      match old_s.shapes.shape_version with
      | None ->
          OldAssoGoals.associate ~use_shapes:false old_subtasks new_subtasks
      | Some shape_version ->
        if Termcode.is_bound_sum_shape_version shape_version then
            BoundAssoGoals.associate ~use_shapes:true old_subtasks new_subtasks
          else
            OldAssoGoals.associate ~use_shapes:true old_subtasks new_subtasks
    in
    List.iter
      (function
        | ((new_goal_id,_), Some ((old_goal_id,_), goal_obsolete)) ->
           merge_goal env new_s old_s ~goal_obsolete
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
  with e when not (Debug.test_flag Debug.stack_trace) ->
    (* Printexc.print_backtrace stderr; (* Will appear with stack_trace *) *)
    Warning.emit "[Session_itp.merge_trans] FATAL unexpected exception: %a@." Exn_printer.exn_printer e;
    exit 2


let merge_theory env old_s old_th s th : unit =
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
             let s1 = Sshape.find_sum s ng_id in
             let s2 = Sshape.find_sum old_s old_id in
             Debug.dprintf debug "[merge_theory] goal has checksum@.";
             not (Termcode.equal_checksum s1 s2)
         in
         if goal_obsolete then
           found_obsolete := true;
         merge_goal env s old_s ~goal_obsolete old_goal ng_id
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
    match old_s.shapes.shape_version with
    | None ->
       OldAssoGoals.associate ~use_shapes:false detached_goals !new_goals
    | Some shape_version ->
        if Termcode.is_bound_sum_shape_version shape_version then
          BoundAssoGoals.associate ~use_shapes:true detached_goals !new_goals
        else
          OldAssoGoals.associate ~use_shapes:true detached_goals !new_goals
  in
  List.iter (function
      | ((new_goal_id,_), Some ((old_goal_id,_), goal_obsolete)) ->
        Debug.dprintf debug "[merge_theory] pairing paired one goal, yeah !@.";
        merge_goal env s old_s ~goal_obsolete
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
  let tasks = Task.split_theory th None None in
  let goalsID = List.map (fun _ -> gen_proofNodeID s) tasks in
  let theory = { theory_name = th.Theory.th_name;
                 theory_is_detached = detached;
                 theory_goals = goalsID;
                 theory_parent_name = parent_name;
               } in
  let parent = Theory theory in
  let add_goal parent goal id =
    let name,expl,task = Termcode.goal_expl_task ~root:true goal in
    mk_proof_node ~expl s name task parent id
  in
  List.iter2 (add_goal parent) tasks goalsID;
  begin
    match merge with
    | Some (old_ses, old_th, env) ->
       merge_theory env old_ses old_th s theory
    | _ -> if tasks <> [] then
             found_detached := true
                                 (* FIXME: should be found_new_goals instead of found_detached *)
  end;
  theory

(* add a why file to a session *)
let add_file_section (s:session) (fn:string) ~file_is_detached
    (theories:Theory.theory list) format : file =
  let fn = Sysutil.relativize_filename s.session_dir fn in
  Debug.dprintf debug "[Session_itp.add_file_section] fn = %a@." Sysutil.print_file_path fn;
(*
  if Hfile.mem s.session_files fn then
    begin
      Printexc.print_backtrace stderr;
      Warning.emit "[session] FATAL: file %s already in database@." fn;
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
let merge_file_section ~old_ses ~old_theories ~file_is_detached ~env
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
                            ~merge:(old_ses,old_th,env) s fid th
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
  let theories, format = Env.read_file Env.base_language env ?format fn in
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
  (List.map (fun (_,_,a) -> a) th), format

let merge_file env (ses : session) (old_ses : session) file =
  let format = file_format file in
  let old_theories = file_theories file in
  let file_name = Sysutil.system_dependent_absolute_path (get_dir old_ses) (file_path file) in
  Debug.dprintf debug "merging file %s@." file_name;
  try
    let new_theories, format = read_file env file_name ~format in
    merge_file_section
      ses ~old_ses ~old_theories ~file_is_detached:false
      ~env file_name new_theories format;
    None
  with Loc.Located (_,e) -> (* TODO: capture only syntax and typing errors *)
    merge_file_section
      ses ~old_ses ~old_theories ~file_is_detached:true
      ~env file_name [] format;
    Some e

let merge_files env (ses:session) (old_ses : session) =
  Debug.dprintf debug "merging files from old session@.";
  let errors =
    Hfile.fold
      (fun _ f acc ->
       match merge_file env ses old_ses f with
       | None -> acc
       | Some e -> e :: acc)
      (get_files old_ses) []
  in
  (* recompute shapes if absent or obsolete *)
  if old_ses.shapes.shape_version <> ses.shapes.shape_version then
    begin
      Sshape.clear ses;
      let version = Termcode.current_sum_shape_version in
      ses.shapes.shape_version <- Some version;
      fold_all_session
        ses
        (fun () n ->
         match n with
         | APn id ->
             begin
               try
                 let t = get_task ses id in
                 let _, expl,_ = Termcode.goal_expl_task ~root:false t in
                 let sum = Termcode.task_checksum ~version t in
                 Sshape.add_sum ses id sum;
                 Sshape.compute_and_add_shape ses ~expl id t
               with Not_found -> (* detached goal *)
                 (Sshape.add_sum ses id Termcode.dumb_checksum;
                  Sshape.add_empty_shape ses id)
             end
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

(*
let save_option_def name fmt opt =
  match opt with
  | None -> ()
  | Some s -> save_string_attrib name fmt s
 *)

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
  fprintf fmt "<result@ status=\"%s\"@ time=\"%.2f\"%a/>"
    (match r.Call_provers.pr_answer with
       | Call_provers.Valid -> "valid"
       | Call_provers.Failure _ -> "failure"
       | Call_provers.Unknown _ -> "unknown"
       | Call_provers.HighFailure -> "highfailure"
       | Call_provers.Timeout -> "timeout"
       | Call_provers.OutOfMemory -> "outofmemory"
       | Call_provers.StepLimitExceeded -> "steplimitexceeded"
       | Call_provers.Invalid -> "invalid")
    r.Call_provers.pr_time
    (opt pp_print_int "steps") steps

let save_status fmt s =
  match s with
  | Some result -> save_result fmt result
  | None -> fprintf fmt "<undone/>"

let save_file_path fmt p =
  List.iter
    (fun s -> fprintf fmt "@[<hov 1><path name=\"%s\"/>@]" s)
    (Sysutil.decompose_path p)

let save_proof_attempt fmt ((id,tl,sl,ml),a) =
  fprintf fmt
    "@\n@[<h><proof@ prover=\"%i\"%a%a%a%a>"
    id
    (save_int_def "timelimit" tl) (a.limit.Call_provers.limit_time)
    (save_int_def "steplimit" sl) (a.limit.Call_provers.limit_steps)
    (save_int_def "memlimit" ml) (a.limit.Call_provers.limit_mem)
    (save_bool_def "obsolete" false) a.proof_obsolete;
  begin match a.proof_script with
  | None -> ()
  | Some p -> save_file_path fmt p
  end;
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
  let sum = Sshape.find_sum s pnid in
  let shape = Sshape.get_shape s pnid in
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
    "@\n@[<v 0>@[<h><file%a%a>@]@\n%a"
    (save_string_attrib "format") f.file_format
    (save_bool_def "proved" false) (file_proved s f)
    save_file_path f.file_path;
  List.iter (save_theory s ctxt fmt) f.file_theories;
  fprintf fmt "@]@\n</file>"

let save fname shfname session =
  let ch = open_out fname in
  let chsh = Compress.Compress_z.open_out shfname in
  let fmt = formatter_of_out_channel ch in
  fprintf fmt "<?xml version=\"1.0\" encoding=\"UTF-8\"?>@\n";
  fprintf fmt "<!DOCTYPE why3session PUBLIC \"-//Why3//proof session v5//EN\"@ \"http://why3.lri.fr/why3session.dtd\">@\n";
  fprintf fmt "@[<v 0><why3session shape_version=\"%a\">"
    (Pp.print_option Termcode.pp_sum_shape_version) session.shapes.shape_version;
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
  begin
    match session.shapes.shape_version with
    | Some v ->
      if Termcode.is_bound_sum_shape_version v then
        begin
          (* In version SV6 or higher, first save the list of variables that are
             referenced in shapes. *)
          Termcode.Gshape.write_shape_to_file session.shapes.session_global_shapes chsh;
          Compress.Compress_z.output_string chsh "\n";
        end;
    | None -> ()
  end;
  let ctxt = { prover_ids = prover_ids; provers = provers; ch_shapes = chsh } in
  Hfile.iter (save_file session ctxt fmt) session.session_files;
  fprintf fmt "@]@\n</why3session>";
  fprintf fmt "@.";
  close_out ch;
  Compress.Compress_z.close_out chsh


let save_session (s : session) =
  let uniformize_shape () =
    (* When all is detached, don't erase the current shapes to not lose nodes *)
    if not (Hfile.fold (fun _ f b -> is_detached s (AFile f) && b)
              (get_files s) true) then
      begin
        Sshape.clear_only_shape s;
        s.shapes.shape_version <- Some Termcode.current_sum_shape_version;
        fold_all_session s (fun () any ->
            match any with
            | APn g when not (is_detached s any)  ->
                let t = get_task s g in
                let (_, expl, _) =
                  let root =
                    match get_proof_parent s g with
                    | Trans _ -> false | Theory _ -> true in
                  Termcode.goal_expl_task ~root t in
                Sshape.compute_and_add_shape s ~expl g t;
            | _ -> ()) ()
      end in
  (* Used here so that shape do not save artifacts of the old saved shapes or
     removed goals (making them grow). It also ensures the order of hypothesis
     is deterministic between two runs of Why3. *)
  uniformize_shape ();
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
