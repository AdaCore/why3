open Stdlib

module Hprover = Whyconf.Hprover

let debug = Debug.register_info_flag "session_itp"
    ~desc:"Pring@ debugging@ messages@ about@ Why3@ session@ \
           creation,@ reading@ and@ writing."

type transID = int
type proofNodeID = int

type theory = {
  theory_name     : Ident.ident;
  theory_checksum : Termcode.checksum option;
  theory_goals    : proofNodeID list;
}

type proof_parent = Trans of transID | Theory of theory

type proof_attempt = {
  prover         : Whyconf.prover;
  timelimit      : int;
  memlimit       : int;
  stepslimit     : int;
  proof_state    : Call_provers.prover_result option;
  (* None means that the call was not done or never returned *)
  proof_obsolete : bool;
  proof_script   : string option;  (* non empty for external ITP *)
}

type proof_attempt_node = {
  proofa_parent  : proofNodeID;
  proofa_attempt : proof_attempt;
}

type proof_node = {
  proofn_name                    : Ident.ident;
  proofn_task                    : Task.task;
  proofn_parent                  : proof_parent;
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
  proofNode_table                    : proof_node Hint.t;
  mutable next_proofNodeID      : int;
  trans_table                   : transformation_node Hint.t;
  mutable next_transID          : int;
  session_files                 : file Hstr.t;
  mutable session_shape_version : int;
  session_prover_ids            : int Hprover.t;
  session_file_name             : string;
}

type tree =
  Tree of
    (int * string * int * (int * string * int * tree list) list)

let rec get_goal s id : tree =
  let t = Hint.find s.proofNode_table id in
  let parent = match t.proofn_parent with
    | Theory _ -> -1
    | Trans n -> n
  in
  let trl = List.map (get_trans s) t.proofn_transformations in
  Tree (id,t.proofn_name.Ident.id_string,parent,trl)

and get_trans s id =
  let tr = Hint.find s.trans_table id in
  (id,tr.transf_name,tr.transf_parent,List.map (get_goal s) tr.transf_subtasks)

let get_tree s =
  Hstr.fold
    (fun fn f acc ->
     let c =
       List.map
         (fun th ->
          let goals = List.map (get_goal s) th.theory_goals in
          (th.theory_name.Ident.id_string,goals))
         f.file_theories
     in
     (fn,c) :: acc)
    s.session_files []

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

let get_transfNode (s : session) (id : transID) =
  try
    Hint.find s.trans_table id
  with Not_found -> raise BadID

let empty_session ?shape_version (file : string) =
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
    session_file_name = file;
  }

let add_file_section (s:session) (fn:string) ?format (ths:Theory.theory list): unit =
  let theories = []
(*
    List.rev_map
      (fun (_,thname,th) ->
       let tasks =
         List.rev_map
           (fun t -> t)
           (Task.split_theory th None None)
       in
       { theory_name     = thname;
         theory_checksum = None;
         theory_goals    = tasks }) ths
 *)
  in
  let f = { file_name = fn;
            file_format = format;
            file_theories = List.rev theories }
  in
  Hstr.add s.session_files fn f

exception BadID

let graft_proof_attempt (s : session) (id : proofNodeID) (pa : proof_attempt) =
  let pn = get_proofNode s id in
  let node = { proofa_parent = id; proofa_attempt = pa } in
  Hprover.replace pn.proofn_attempts pa.prover node

let remove_proof_attempt (s : session) (id : proofNodeID)
    (prover : Whyconf.prover) =
  let pn = get_proofNode s id in
  Hprover.remove pn.proofn_attempts prover

(* [mk_proof_node s n t p id] register in the session [s] a proof node
   of proofNodeID [id] of parent [p] of task [t] *)
let mk_proof_node (s : session) (n : Ident.ident) (t : Task.task)
    (parent : proof_parent) (node_id : proofNodeID) =
  let pn = { proofn_name = n;
             proofn_task = t;
             proofn_parent = parent;
             proofn_attempts = Hprover.create 7;
             proofn_transformations = []} in
  Hint.add s.proofNode_table node_id pn

let mk_proof_node_no_task (s : session) (n : Ident.ident)
    (parent : proof_parent) (node_id : proofNodeID) =
  mk_proof_node s n None parent node_id

let mk_proof_node_task (s : session) (t : Task.task)
    (parent : proof_parent) (node_id : proofNodeID) =
  let name,_,_ = Termcode.goal_expl_task ~root:false t in
  mk_proof_node s name t parent node_id

let mk_transf_proof_node (s : session) (tid : int)
    (t : Task.task) =
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
  mk_transf_node s id tid name args sub_tasks

let remove_transformation (s : session) (id : transID) =
  let nt = get_transfNode s id in
  Hint.remove s.trans_table id;
  let pn = get_proofNode s nt.transf_parent in
  let trans_up = List.filter (fun tid -> tid != id) pn.proofn_transformations in
  pn.proofn_transformations <- trans_up;

(************************)
(* saving state on disk *)
(************************)
open Format

let db_filename = "why3session.xml"
let shape_filename = "why3shapes"
let compressed_shape_filename = "why3shapes.gz"
let session_dir_for_save = ref "."

let save_string = Pp.html_string

(****************************)
(*     session opening      *)
(****************************)

exception LoadError of Xml.element * string
(** LoadError (xml,messg) *)
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

let int_attribute field r =
  try
    int_of_string (List.assoc field r.Xml.attributes)
  with Not_found | Invalid_argument _ ->
    (* TODO: use real error *)
    eprintf "[Error] missing required attribute '%s' from element '%s'@."
      field r.Xml.name;
    assert false

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

type load_ctxt = {
  old_provers : (Whyconf.prover * int * int * int) Mint.t ;
}

let read_file_session_and_shapes dir xml_filename =
  try
    let compressed_shape_filename =
      Filename.concat dir compressed_shape_filename
    in
    if Sys.file_exists compressed_shape_filename then
      (*    if Compress.compression_supported then
            Session.ReadShapesCompress.read_xml_and_shapes
             xml_filename compressed_shape_filename
            else *)
      begin
        Warning.emit "[Warning] could not read goal shapes because \
                      Why3 was not compiled with compress support@.";
        Xml.from_file xml_filename, false
      end
    else
      let shape_filename = Filename.concat dir shape_filename in
      (*    if Sys.file_exists shape_filename then
            ReadShapesNoCompress.read_xml_and_shapes xml_filename shape_filename
            else*)
      begin
        Warning.emit "[Warning] could not find goal shapes file@.";
        Xml.from_file xml_filename, false
      end
  with e ->
    Warning.emit "[Warning] failed to read goal shapes: %s@."
      (Printexc.to_string e);
    Xml.from_file xml_filename, false

(* [load_goal s op p g id] loads the goal of parent [p] from the xml
   [g] of nodeID [id] into the session [s] *)
let rec load_goal session old_provers parent g id =
  match g.Xml.name with
  | "goal" ->
    let gname = load_ident g in
    mk_proof_node_no_task session gname parent id;
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
                     timelimit = timelimit;
                     memlimit = memlimit;
                     stepslimit = steplimit;
                     proof_state = res;
                     proof_obsolete = obsolete;
                     proof_script = edit;
                   } in
          graft_proof_attempt session pid pa
        with Failure _ | Not_found ->
          Warning.emit "[Error] prover id not listed in header '%s'@." prover;
          raise (LoadError (a,"prover not listing in header"))
      end
    | "transf" ->
        let trname = string_attribute "name" a in
        let tid = gen_transID session in
        let subtasks = List.fold_left (fun goals th -> match th.Xml.name with
        | "goal" -> (gen_proofNodeID session) :: goals
        | _ -> goals) [] a.Xml.elements in
        mk_transf_node session pid tid trname [] subtasks;
        List.iter2
          (load_goal session old_provers (Trans tid))
          a.Xml.elements subtasks;
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
    let goals = List.fold_left (fun goals th -> match th.Xml.name with
        | "goal" -> (gen_proofNodeID session) :: goals
        | _ -> goals) [] th.Xml.elements in
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

let load_file session old_provers f = (* old_provers *)
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
  let session = empty_session file in
  let use_shapes =
    (* If the xml is present we read it, otherwise we consider it empty *)
    if Sys.file_exists file then
      try
        Termcode.reset_dict ();
        let dir = Filename.dirname file in
        let xml,use_shapes = read_file_session_and_shapes dir file in
        try
          build_session session xml.Xml.content;
          use_shapes
        with Sys_error msg ->
          failwith ("Open session: sys error " ^ msg)
      with
      | Sys_error msg ->
        (* xml does not exist yet *)
        raise (SessionFileError msg)
      | Xml.Parse_error s ->
        Warning.emit "XML database corrupted, ignored (%s)@." s;
        raise (SessionFileError "XML corrupted")
    else false
  in
  session, use_shapes
