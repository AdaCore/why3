open Stdlib

module Hprover = Whyconf.Hprover

let debug = Debug.register_info_flag "session_itp"
    ~desc:"Pring@ debugging@ messages@ about@ Why3@ session@ \
           creation,@ reading@ and@ writing."

type transID = int
type proofNodeID = int

type theory = {
  theory_name     : Ident.ident;
  theory_goals    : proofNodeID list;
  mutable theory_checksum : Termcode.checksum option;
}

let theory_name t = t.theory_name
let theory_goals t = t.theory_goals

type proof_parent = Trans of transID | Theory of theory

type proof_attempt = {
  prover              : Whyconf.prover;
  limit               : Call_provers.resource_limit;
  mutable proof_state : Call_provers.prover_result option;
  (* None means that the call was not done or never returned *)
  proof_obsolete      : bool;
  proof_script        : string option;  (* non empty for external ITP *)
}

type proof_attempt_node = {
  proofa_parent  : proofNodeID;
  proofa_attempt : proof_attempt;
}

type proof_node = {
  proofn_name                    : Ident.ident;
  proofn_task                    : Task.task;
  proofn_parent                  : proof_parent;
  proofn_checksum                : Termcode.checksum option;
  proofn_attempts                : proof_attempt_node Hprover.t;
  mutable proofn_transformations : transID list;
}

type trans_arg =
  | TAint      of int
  | TAstring   of string
  | TAterm     of Term.term
  | TAty       of Ty.ty
  | TAtysymbol of Ty.tysymbol
  (* | ... *)

type transformation_node = {
  transf_name     : string;
  transf_args     : trans_arg list;
  transf_subtasks : proofNodeID list;
  transf_parent   : proofNodeID;
}

type file = {
  file_name     : string;
  file_format   : string option;
  file_theories : theory list;
}

type session = {
  proofNode_table               : proof_node Hint.t;
  mutable next_proofNodeID      : int;
  trans_table                   : transformation_node Hint.t;
  mutable next_transID          : int;
  session_files                 : file Hstr.t;
  mutable session_shape_version : int;
  session_prover_ids            : int Hprover.t;
}

let session_iter_proofNode f s =
  Hint.iter
    (fun id pn -> if id < s.next_proofNodeID then f pn)
    s.proofNode_table

let session_iter_proof_attempt f =
  session_iter_proofNode
    (fun pn ->
       Hprover.iter
         (fun _ pan -> f pan.proofa_attempt)
        pn.proofn_attempts)

type tree = {
    tree_node_id : proofNodeID;
    tree_goal_name : string;
    tree_proof_attempts : proof_attempt list; (* proof attempts on this node *)
    tree_transformations : (transID * string * tree list) list;
                                (* transformations on this node *)
  }

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

let get_node (s : session) (n : int) =
  let _ = Hint.find s.proofNode_table n in n

let get_trans (s : session) (n : int) =
  let _ = Hint.find s.trans_table n in n

let gen_transID (s : session) =
  let id = s.next_transID in
  s.next_transID <- id + 1;
  id

let gen_proofNodeID (s : session) =
  let id = s.next_proofNodeID in
  s.next_proofNodeID <- id + 1;
  id

exception BadID

let get_proofNode (s : session) (id : proofNodeID) =
  try
    Hint.find s.proofNode_table id
  with Not_found -> raise BadID

let get_task (s:session) (id:proofNodeID) =
  let node = get_proofNode s id in
  node.proofn_task

let get_transfNode (s : session) (id : transID) =
  try
    Hint.find s.trans_table id
  with Not_found -> raise BadID

let get_transformations (s : session) (id : proofNodeID) =
  (get_proofNode s id).proofn_transformations

let get_sub_tasks (s : session) (id : transID) =
  (get_transfNode s id).transf_subtasks

let get_proof_parent (s : session) (id : proofNodeID) =
  (get_proofNode s id).proofn_parent

let get_trans_parent (s : session) (id : transID) =
  (get_transfNode s id).transf_parent

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

let fold_all_sub_goals_of_theory s f acc th =
  List.fold_left (fold_all_sub_goals_of_proofn s f) acc th.theory_goals

open Format
open Ident

let print_proof_attempt fmt pa =
  fprintf fmt "%a tl=%d %a"
          Whyconf.print_prover pa.prover
          pa.limit.Call_provers.limit_time
          (Pp.print_option Call_provers.print_prover_result) pa.proof_state

let rec print_tree s fmt t =
  let pn = get_proofNode s t.tree_node_id in
  let parent = match pn.proofn_parent with
    | Theory t -> t.theory_name.id_string
    | Trans id -> (get_transfNode s id).transf_name
  in
  fprintf fmt
    "@[<hv 2> Goal %s;@ parent %s;@ sum %s;@ @[<hov 2>[%a]@]@ @[<hov 2>[%a]@]@]"
    t.tree_goal_name parent
    (Opt.fold (fun _ a -> Termcode.string_of_checksum a) "None" pn.proofn_checksum)
    (Pp.print_list Pp.semi print_proof_attempt) t.tree_proof_attempts
    (Pp.print_list Pp.semi (print_trans s)) t.tree_transformations

and print_trans s fmt (id, name, l) =
  let tn = get_transfNode s id in
  let parent = (get_proofNode s tn.transf_parent).proofn_name.id_string in
  fprintf fmt "@[<hv 2> Trans %s;@ parent %s;@ [%a]@]" name parent
    (Pp.print_list Pp.semi (print_tree s)) l

let print_session fmt s =
  let print_theory s fmt th =
    fprintf fmt "@[<hv 2> Theory %s;@ [%a]@]" th.theory_name.Ident.id_string
      (Pp.print_list Pp.semi (fun fmt a -> print_tree s fmt (get_tree s a))) th.theory_goals
  in
  let print_file s fmt (file, thl) =
    fprintf fmt "@[<hv 2> File %s;@ [%a]@]" file.file_name
      (Pp.print_list Pp.semi (print_theory s)) thl
  in
  let print_s s fmt =
    fprintf fmt "@[%a@]" (Pp.print_list Pp.semi (print_file s))
  in
  let l = Hstr.fold (fun _ f acc -> (f,f.file_theories) :: acc) (get_files s) [] in
  fprintf fmt "%a@." (print_s s) l;;

let empty_session ?shape_version () =
  let shape_version = match shape_version with
    | Some v -> v
    | None -> Termcode.current_shape_version
  in
  { proofNode_table = Hint.create 97;
    next_proofNodeID = 0;
    trans_table = Hint.create 97;
    next_transID = 0;
    session_files = Hstr.create 3;
    session_shape_version = shape_version;
    session_prover_ids = Hprover.create 7;
  }

(**************************************************)
(* proof node/attempt/transformation manipulation *)
(**************************************************)

let mk_proof_attempt session pid pa =
  let pn = get_proofNode session pid in
  let node = { proofa_parent = pid; proofa_attempt = pa } in
  Hprover.replace pn.proofn_attempts pa.prover node

let graft_proof_attempt (s : session) (id : proofNodeID) (pr : Whyconf.prover)
    ~timelimit =
  let pa = {
    prover = pr;
    limit = { Call_provers.limit_time  = timelimit;
              Call_provers.limit_mem   = 0;
              Call_provers.limit_steps = -1; };
    proof_state = None;
    proof_obsolete = false;
    proof_script = None; } in
  mk_proof_attempt s id pa

let remove_proof_attempt (s : session) (id : proofNodeID)
    (prover : Whyconf.prover) =
  let pn = get_proofNode s id in
  Hprover.remove pn.proofn_attempts prover

(* [mk_proof_node s n t p id] register in the session [s] a proof node
   of proofNodeID [id] of parent [p] of task [t] *)
let mk_proof_node (s : session) (n : Ident.ident) (t : Task.task)
    (parent : proof_parent) (node_id : proofNodeID) =
  let sum = Some (Termcode.task_checksum t) in
  let pn = { proofn_name = n;
             proofn_task = t;
             proofn_parent = parent;
             proofn_checksum = sum;
             proofn_attempts = Hprover.create 7;
             proofn_transformations = []} in
  Hint.add s.proofNode_table node_id pn

let mk_proof_node_no_task (s : session) (n : Ident.ident)
    (parent : proof_parent) (node_id : proofNodeID) sum =
  let pn = { proofn_name = n;
             proofn_task = None;
             proofn_parent = parent;
             proofn_checksum = sum;
             proofn_attempts = Hprover.create 7;
             proofn_transformations = []} in
  Hint.add s.proofNode_table node_id pn

let mk_proof_node_task (s : session) (t : Task.task)
    (parent : proof_parent) (node_id : proofNodeID) =
  let name,_,_ = Termcode.goal_expl_task ~root:false t in
  mk_proof_node s name t parent node_id

let mk_transf_proof_node (s : session) (tid : int) (t : Task.task) =
  let id = gen_proofNodeID s in
  mk_proof_node_task s t (Trans tid) id;
  id

let mk_transf_node (s : session) (id : proofNodeID) (node_id : transID)
    (name : string) (args : trans_arg list) (pnl : proofNodeID list) =
  let pn = get_proofNode s id in
  let tn = { transf_name = name;
             transf_args = args;
             transf_subtasks = pnl;
             transf_parent = id; } in
  Hint.add s.trans_table node_id tn;
  pn.proofn_transformations <- node_id::pn.proofn_transformations

let graft_transf  (s : session) (id : proofNodeID) (name : string)
    (args : trans_arg list) (tl : Task.task list) =
  let tid = gen_transID s in
  let sub_tasks = List.map (mk_transf_proof_node s tid) tl in
  mk_transf_node s id tid name args sub_tasks;
  tid

let remove_transformation (s : session) (id : transID) =
  let nt = get_transfNode s id in
  Hint.remove s.trans_table id;
  let pn = get_proofNode s nt.transf_parent in
  let trans_up = List.filter (fun tid -> tid != id) pn.proofn_transformations in
  pn.proofn_transformations <- trans_up

let update_proof_attempt s id pr st =
  let n = get_proofNode s id in
  let pa = Hprover.find n.proofn_attempts pr in
  pa.proofa_attempt.proof_state <- Some st

(****************************)
(*     session opening      *)
(****************************)

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

let load_result r =
  match r.Xml.name with
  | "result" ->
    let status = string_attribute "status" r in
    let answer =
      match status with
      | "valid" -> Call_provers.Valid
      | "invalid" -> Call_provers.Invalid
      | "unknown" -> Call_provers.Unknown ("", None)
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
    Some {
      Call_provers.pr_answer = answer;
      Call_provers.pr_time = time;
      Call_provers.pr_output = "";
      Call_provers.pr_status = Unix.WEXITED 0;
      Call_provers.pr_steps = steps;
      Call_provers.pr_model = Model_parser.default_model;
    }
  | "undone" -> None
  | "unedited" -> None
  | s ->
    Warning.emit "[Warning] Session.load_result: unexpected element '%s'@."
      s;
    None

let load_option attr g =
  try Some (List.assoc attr g.Xml.attributes)
  with Not_found -> None

let load_ident elt =
  let name = string_attribute "name" elt in
  let label = List.fold_left
      (fun acc label ->
         match label with
         | {Xml.name = "label"} ->
           let lab = string_attribute "name" label in
           Ident.Slab.add (Ident.create_label lab) acc
         | _ -> acc
      ) Ident.Slab.empty elt.Xml.elements in
  let preid =
    try
      let load_exn attr g = List.assoc attr g.Xml.attributes in
      let file = load_exn "locfile" elt in
      let lnum =  int_of_string (load_exn "loclnum" elt) in
      let cnumb = int_of_string (load_exn "loccnumb" elt) in
      let cnume = int_of_string (load_exn "loccnume" elt) in
      let pos = Loc.user_position file lnum cnumb cnume in
      Ident.id_user ~label name pos
    with Not_found | Invalid_argument _ ->
      Ident.id_fresh ~label name in
  Ident.id_register preid

(* [load_goal s op p g id] loads the goal of parent [p] from the xml
   [g] of nodeID [id] into the session [s] *)
let rec load_goal session old_provers parent g id =
  match g.Xml.name with
  | "goal" ->
    let gname = load_ident g in
    let csum = string_attribute_opt "sum" g in
    let sum = Opt.map Termcode.checksum_of_string csum in
    mk_proof_node_no_task session gname parent id sum;
    List.iter (load_proof_or_transf session old_provers id) g.Xml.elements;
  | "label" -> ()
  | s ->
    Warning.emit "[Warning] Session.load_goal: unexpected element '%s'@." s

(* [load_proof_or_transf s op id a] load either a proof attempt or a
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
            | [] -> None
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
          let pa = { prover = p;
                     limit = { Call_provers.limit_time  = timelimit;
                               Call_provers.limit_mem   = memlimit;
                               Call_provers.limit_steps = steplimit; };
                     proof_state = res;
                     proof_obsolete = obsolete;
                     proof_script = edit;
                   } in
          mk_proof_attempt session pid pa
        with Failure _ | Not_found ->
          Warning.emit "[Error] prover id not listed in header '%s'@." prover;
          raise (LoadError (a,"prover not listing in header"))
      end
    | "transf" ->
        let trname = string_attribute "name" a in
        let tid = gen_transID session in
        let subtasks_ids =
          List.rev (List.fold_left
                      (fun goals th ->
                       match th.Xml.name with
                       | "goal" -> (gen_proofNodeID session) :: goals
                       | _ -> goals) [] a.Xml.elements)
        in
        mk_transf_node session pid tid trname [] subtasks_ids;
        List.iter2
          (load_goal session old_provers (Trans tid))
          a.Xml.elements subtasks_ids;
    | "metas" -> ()
    | "label" -> ()
    | s ->
        Warning.emit
          "[Warning] Session.load_proof_or_transf: unexpected element '%s'@."
          s

let load_theory session old_provers acc th =
  match th.Xml.name with
  | "theory" ->
    let thname = load_ident th in
    let csum = string_attribute_opt "sum" th in
    let checksum = Opt.map Termcode.checksum_of_string csum in
    let goals = List.rev (List.fold_left (fun goals th -> match th.Xml.name with
        | "goal" -> (gen_proofNodeID session) :: goals
        | _ -> goals) [] th.Xml.elements) in
    let mth = { theory_name = thname;
                theory_checksum = checksum;
                theory_goals = goals; } in
    List.iter2
      (load_goal session old_provers (Theory mth))
      th.Xml.elements goals;
    mth::acc
  | s ->
    Warning.emit "[Warning] Session.load_theory: unexpected element '%s'@."
      s;
    acc

let load_file session old_provers f =
  match f.Xml.name with
  | "file" ->
    let fn = string_attribute "name" f in
    let fmt = load_option "format" f in
    let ft = List.rev
        (List.fold_left
           (load_theory session old_provers) [] f.Xml.elements) in
    let mf = { file_name = fn;
               file_format = fmt;
               file_theories = ft; } in
    Hstr.add session.session_files fn mf;
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
    s.session_shape_version <- shape_version;
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
    Debug.dprintf debug "[Info] load_session: done@\n"
  | s ->
    Warning.emit "[Warning] Session.load_session: unexpected element '%s'@."
      s

let load_session (file : string) =
  let session = empty_session () in
  (* If the xml is present we read it, otherwise we consider it empty *)
  if Sys.file_exists file then
    try
      Termcode.reset_dict ();
      let xml = Xml.from_file file in
      try
        build_session session xml.Xml.content;
        session
      with Sys_error msg ->
        failwith ("Open session: sys error " ^ msg)
    with
    | Sys_error msg ->
      (* xml does not exist yet *)
      raise (SessionFileError msg)
    | Xml.Parse_error s ->
      Warning.emit "XML database corrupted, ignored (%s)@." s;
      raise (SessionFileError "XML corrupted")
  else
    session

(* add a why file from a session *)
let add_file_section (s:session) (fn:string) (theories:Theory.theory list) format : unit =
  let add_theory acc (th : Theory.theory) =
    let add_goal parent goal id =
      let name,_expl,task = Termcode.goal_expl_task ~root:true goal in
      mk_proof_node s name task parent id;
    in
    let tasks = List.rev (Task.split_theory th None None) in
    let goalsID = List.map (fun _ -> gen_proofNodeID s) tasks in
    let theory = { theory_name = th.Theory.th_name;
                   theory_checksum = None;
                   theory_goals = goalsID; } in
    let parent = Theory theory in
    List.iter2 (add_goal parent) tasks goalsID;
    theory::acc
  in
  let theories = List.fold_left add_theory [] theories in
  let f = { file_name = fn;
            file_format = format;
            file_theories = List.rev theories }
  in
  Hstr.add s.session_files fn f

(************************)
(* saving state on disk *)
(************************)

module Mprover = Whyconf.Mprover
module Sprover = Whyconf.Sprover
module PHprover = Whyconf.Hprover

open Format

let save_string = Pp.html_string

type save_ctxt = {
  prover_ids : int PHprover.t;
  provers : (int * int * int * int) Mprover.t;
}

let get_used_provers_with_stats session =
  let prover_table = PHprover.create 5 in
  session_iter_proof_attempt
    (fun pa ->
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

let save_proof_attempt fmt ((id,tl,sl,ml),a) =
  fprintf fmt
    "@\n@[<h><proof@ prover=\"%i\"%a%a%a%a>"
    id
    (save_int_def "timelimit" tl) (a.limit.Call_provers.limit_time)
    (save_int_def "steplimit" sl) (a.limit.Call_provers.limit_steps)
    (save_int_def "memlimit" ml) (a.limit.Call_provers.limit_mem)
    (save_bool_def "obsolete" false) a.proof_obsolete;
  save_status fmt a.proof_state;
  fprintf fmt "</proof>@]"

let save_ident fmt id =
  let n=
    try
      let (_,_,l) = Theory.restore_path id in
      String.concat "." l
    with Not_found -> id.Ident.id_string
  in
  fprintf fmt "name=\"%a\"" save_string n

let save_checksum fmt s =
  fprintf fmt "%s" (Termcode.string_of_checksum s)

let rec save_goal s ctxt fmt pnid =
  let pn = get_proofNode s pnid in
  fprintf fmt
    "@\n@[<v 0>@[<h><goal@ %a>@]"
    save_ident pn.proofn_name;
  let l = Hprover.fold
      (fun _ a acc -> (Mprover.find a.proofa_attempt.prover ctxt.provers,
                       a.proofa_attempt) :: acc)
      pn.proofn_attempts [] in
  let l = List.sort (fun ((i1,_,_,_),_) ((i2,_,_,_),_) -> compare i1 i2) l in
  List.iter (save_proof_attempt fmt) l;
  let l =
    List.fold_left (fun acc t -> (get_transfNode s t) :: acc) [] pn.proofn_transformations
  in
  let l = List.sort (fun t1 t2 -> compare t1.transf_name t2.transf_name) l in
  List.iter (save_trans s ctxt fmt) l;
  fprintf fmt "@]@\n</goal>"

and save_trans s ctxt fmt t =
  fprintf fmt "@\n@[<hov 1>@[<h><transf@ name=\"%a\">@]"
    save_string t.transf_name;
  List.iter (save_goal s ctxt fmt) t.transf_subtasks;
  fprintf fmt "@]@\n</transf>"

module CombinedTheoryChecksum = struct

  let b = Buffer.create 1024

  let f () pn =
    match pn.proofn_checksum with
    | None -> assert false
    | Some c -> Buffer.add_string b (Termcode.string_of_checksum c)

  let _compute s th =
    let () = fold_all_sub_goals_of_theory s f () th in
    let c = Termcode.buffer_checksum b in
    Buffer.clear b; c

end

let save_theory s ctxt fmt t =
  (* commented out since the session needs to be updated for goals to
     have a checksum *)
  (* let c = CombinedTheoryChecksum.compute s t in *)
  (* t.theory_checksum <- Some c; *)
  fprintf fmt
    "@\n@[<v 1>@[<h><theory@ %a%a>@]"
    save_ident t.theory_name
    (opt save_checksum "sum") t.theory_checksum;
  List.iter (save_goal s ctxt fmt) t.theory_goals;
  fprintf fmt "@]@\n</theory>"

let save_file s ctxt fmt _ f =
  fprintf fmt
    "@\n@[<v 0>@[<h><file@ name=\"%a\"%a>@]"
    save_string f.file_name (opt_string "format")
    f.file_format;
  List.iter (save_theory s ctxt fmt) f.file_theories;
  fprintf fmt "@]@\n</file>"

let save fname session =
  let ch = open_out fname in
  let fmt = formatter_of_out_channel ch in
  fprintf fmt "<?xml version=\"1.0\" encoding=\"UTF-8\"?>@\n";
  fprintf fmt "<!DOCTYPE why3session PUBLIC \"-//Why3//proof session v5//EN\"@ \"http://why3.lri.fr/why3session.dtd\">@\n";
  fprintf fmt "@[<v 0><why3session shape_version=\"%d\">"
    session.session_shape_version;
  Termcode.reset_dict ();
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
  let ctxt = { prover_ids = prover_ids; provers = provers } in
  Hstr.iter (save_file session ctxt fmt) session.session_files;
  fprintf fmt "@]@\n</why3session>";
  fprintf fmt "@.";
  close_out ch

let save_session (f : string) (s : session) =
  Sysutil.backup_file f;
  save f s
