open Stdlib

module Hprover = Whyconf.Hprover

let debug = Debug.register_info_flag "session_itp"
  ~desc:"Pring@ debugging@ messages@ about@ Why3@ session@ \
         creation,@ reading@ and@ writing."

type transID = int
type proofNodeID = int

type proof_parent = Trans of transID | Theory of Theory.theory

type proof_attempt = {
  prover         : Whyconf.prover;
  timelimit      : int;
  memlimit       : int;
  stepslimit     : int;
  proof_state    : Call_provers.prover_result option;  (* None means that the call was not done
                                                       or never returned *)
  proof_obsolete : bool;
  proof_script   : string option;  (* non empty for external ITP *)
}

type proof_attempt_node = {
  proofa_parent  : proofNodeID;
  proofa_attempt : proof_attempt;
}

type proof_node = {
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

type theory = {
  theory_name     : Ident.ident;
  theory_checksum : Termcode.checksum option;
  theory_goals    : proofNodeID list;
}

type file = {
  file_name     : string;
  file_format   : string option;
  file_theories : theory list;
}

type session = {
  task_table                    : proof_node Hint.t;
  mutable next_proofNodeID      : int;
  trans_table                   : transformation_node Hint.t;
  mutable next_transID          : int;
  session_files                 : file Hstr.t;
  mutable session_shape_version : int;
  session_prover_ids            : int Hprover.t;
  session_file_name             : string;
 }

let gen_transID (s : session) =
  let id = s.next_transID in
  s.next_transID <- id + 1;
  id

let gen_proofNodeID (s : session) =
  let id = s.next_proofNodeID in
  s.next_proofNodeID <- id + 1;
  id

let empty_session ?shape_version (file : string) =
  let shape_version = match shape_version with
    | Some v -> v
    | None -> Termcode.current_shape_version
  in
  { task_table = Hint.create 97;
    next_proofNodeID = 0;
    trans_table = Hint.create 97;
    next_transID = 0;
    session_files = Hstr.create 3;
    session_shape_version = shape_version;
    session_prover_ids = Hprover.create 7;
    session_file_name = file;
  }

exception BadID

let graft_proof_attempt (s : session) (id : proofNodeID) (pa : proof_attempt) =
  try
    let pn = Hint.find s.task_table id in
    let node = { proofa_parent = id; proofa_attempt = pa } in
    Hprover.replace pn.proofn_attempts pa.prover node
  with Not_found -> raise BadID

let mk_proof_node (s : session) (tid : int) (t : Task.task) =
  let id = gen_proofNodeID s in
  let pn = { proofn_task = t; proofn_parent = Trans tid;
             proofn_attempts = Hprover.create 3;
             proofn_transformations = []} in
  Hint.add s.task_table id pn;
  id

let graft_transf  (s : session) (id : proofNodeID) (name : string) (l : trans_arg list) (tl : Task.task list) =
  try
    let pn = Hint.find s.task_table id in
    let tid = gen_transID s in
    let sub_tasks = List.map (mk_proof_node s tid) tl in
    let tn = { transf_name = name;
               transf_args = l;
               transf_subtasks = sub_tasks;
               transf_parent = id; } in
    Hint.replace s.trans_table tid tn;
    pn.proofn_transformations <- tid::pn.proofn_transformations
  with Not_found -> raise BadID

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

let load_file session old_provers f = old_provers
(*  match f.Xml.name with
    | "file" ->
       let ctxt = { old_provers = old_provers ; keygen = keygen } in
        let fn = string_attribute "name" f in
        let fmt = load_option "format" f in
        let expanded = bool_attribute "expanded" f false in
        let mf = raw_add_file ~keygen:ctxt.keygen ~expanded session fn fmt in
        mf.file_theories <-
          List.rev
          (List.fold_left
             (load_theory ctxt mf) [] f.Xml.elements);
        mf.file_verified <- file_verified mf;
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
            let p = {C.prover_name = name;
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
        *)

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
