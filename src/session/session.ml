(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Stdlib
open Debug
open Util

module Mprover = Whyconf.Mprover
module Sprover = Whyconf.Sprover
module PHprover = Whyconf.Hprover
module C = Whyconf
module Tc = Termcode

let debug = Debug.register_flag "session"
  ~desc:"About the why3 session creation, reading and writing."

(** {2 Type definitions} *)

module PHstr = Util.Hstr

type undone_proof =
    | Scheduled (** external proof attempt is scheduled *)
    | Interrupted
    | Running (** external proof attempt is in progress *)
    | Unedited
    | JustEdited

type proof_attempt_status =
    | Undone of undone_proof
    | Done of Call_provers.prover_result (** external proof done *)
    | InternalFailure of exn (** external proof aborted by internal error *)

type task_option = Task.task option

type 'a goal =
  { mutable goal_key  : 'a;
    goal_name : Ident.ident;
    goal_expl : string option;
    goal_parent : 'a goal_parent;
    mutable goal_checksum : Tc.checksum;
    mutable goal_shape : Tc.shape;
    mutable goal_verified : bool;
    goal_task: task_option;
    mutable goal_expanded : bool;
    goal_external_proofs : 'a proof_attempt PHprover.t;
    goal_transformations : 'a transf PHstr.t;
  }

and 'a proof_attempt =
  { proof_key : 'a;
    mutable proof_prover : Whyconf.prover;
    proof_parent : 'a goal;
    mutable proof_state : proof_attempt_status;
    mutable proof_timelimit : int;
    mutable proof_memlimit : int;
    mutable proof_obsolete : bool;
    mutable proof_archived : bool;
    mutable proof_edited_as : string option;
  }

and 'a goal_parent =
  | Parent_theory of 'a theory
  | Parent_transf of 'a transf

and 'a transf =
    { mutable transf_key : 'a;
      transf_name : string;
      (** Why3 tranformation name *)
      transf_parent : 'a goal;
      mutable transf_verified : bool;
      mutable transf_goals : 'a goal list;
      (** Not mutated after the creation of the session *)
      mutable transf_expanded : bool;
    }

and 'a theory =
    { mutable theory_key : 'a;
      theory_name : Ident.ident;
      theory_parent : 'a file;
      mutable theory_goals : 'a goal list;
      mutable theory_verified : bool;
      mutable theory_expanded : bool;
    }

and 'a file =
    { mutable file_key : 'a;
      file_name : string;
      file_format : string option;
      file_parent : 'a session;
      mutable file_theories: 'a theory list;
      (** Not mutated after the creation *)
      mutable file_verified : bool;
      mutable file_expanded : bool;
    }

and 'a session =
    { session_files : 'a file PHstr.t;
      mutable session_shape_version : int;
      session_dir   : string; (** Absolute path *)
    }

type loaded_prover =
    { prover_config : Whyconf.config_prover;
      prover_driver : Driver.driver}

type loaded_provers = loaded_prover option PHprover.t

type 'a env_session =
    { env : Env.env;
      mutable whyconf : Whyconf.config;
      loaded_provers : loaded_provers;
      session : 'a session}

let update_env_session_config e c = e.whyconf <- c

(*************************)
(**       Iterators      *)
(*************************)
type 'a any =
  | File of 'a file
  | Theory of 'a theory
  | Goal of 'a goal
  | Proof_attempt of 'a proof_attempt
  | Transf of 'a transf

let rec goal_iter_proof_attempt f g =
  PHprover.iter (fun _ a -> f a) g.goal_external_proofs;
  PHstr.iter (fun _ t -> transf_iter_proof_attempt f t) g.goal_transformations

and transf_iter_proof_attempt f t =
  List.iter (goal_iter_proof_attempt f) t.transf_goals

let theory_iter_proof_attempt f t =
  List.iter (goal_iter_proof_attempt f) t.theory_goals

let file_iter_proof_attempt f t =
  List.iter (theory_iter_proof_attempt f) t.file_theories

let session_iter_proof_attempt f s =
  PHstr.iter (fun _ file -> file_iter_proof_attempt f file) s.session_files

let rec iter_proof_attempt f = function
    | Goal g -> goal_iter_proof_attempt f g
    | Theory th -> theory_iter_proof_attempt f th
    | File file -> file_iter_proof_attempt f file
    | Proof_attempt a -> f a
    | Transf tr -> transf_iter_proof_attempt f tr

let rec goal_iter_leaf_goal ~unproved_only f g =
  if not (g.goal_verified && unproved_only) then
    let r = ref true in
    PHstr.iter
      (fun _ t -> r := false;
        List.iter (goal_iter_leaf_goal ~unproved_only f) t.transf_goals)
      g.goal_transformations;
    if !r then f g

(** iterators not reccursive *)
let iter_goal fp ft g =
  PHprover.iter (fun _ a -> fp a) g.goal_external_proofs;
  PHstr.iter (fun _ t -> ft t) g.goal_transformations

let iter_transf f t =
  List.iter (fun g -> f g) t.transf_goals

let goal_iter f g =
  PHprover.iter
    (fun _ a -> f (Proof_attempt a)) g.goal_external_proofs;
  PHstr.iter (fun _ t -> f (Transf t)) g.goal_transformations

let transf_iter f t =
  List.iter (fun g -> f (Goal g)) t.transf_goals

let theory_iter f t =
  List.iter (fun g -> f (Goal g)) t.theory_goals

let file_iter f t =
  List.iter (fun th -> f (Theory th)) t.file_theories

let session_iter f s =
  PHstr.iter (fun _ file -> f (File file)) s.session_files

let iter f = function
    | Goal g -> goal_iter f g
    | Theory th -> theory_iter f th
    | File file -> file_iter f file
    | Proof_attempt _ -> ()
    | Transf tr -> transf_iter f tr

(** Print session *)


module PTreeT = struct
  type 'a t = | Any of 'a any | Session of 'a session
  let decomp = function
    | Any t ->
      let s = match t with
        | File f ->
          if f.file_verified
          then f.file_name
          else f.file_name^"?"
        | Theory th ->
          if th.theory_verified
          then th.theory_name.Ident.id_string
          else th.theory_name.Ident.id_string^"?"
        | Goal g ->
          if g.goal_verified
          then g.goal_name.Ident.id_string
          else g.goal_name.Ident.id_string^"?"
        | Proof_attempt pr ->
          Pp.sprintf_wnl "%a%s%s%s%s"
            Whyconf.print_prover pr.proof_prover
            (match pr.proof_state with
              | Done { Call_provers.pr_answer = Call_provers.Valid} -> ""
              | InternalFailure _ -> "!"
              | _ -> "?")
            (if pr.proof_obsolete || pr.proof_archived then " " else "")
            (if pr.proof_obsolete then "O" else "")
            (if pr.proof_archived then "A" else "")
        | Transf tr ->
          if tr.transf_verified
          then tr.transf_name
          else tr.transf_name^"?" in
      let l = ref [] in
      iter (fun a -> l := (Any a)::!l) t;
      s,!l
    | Session s ->
      let l = ref [] in
      session_iter (fun a -> l := (Any a)::!l) s;
      Filename.basename s.session_dir,!l

end

module PTree = Print_tree.PMake(PTreeT)

let print_any fmt any = PTree.print fmt (PTreeT.Any any)

let print_session fmt s = PTree.print fmt (PTreeT.Session s)

(** 2 Create a session *)

let empty_session ?shape_version dir =
  let shape_version = match shape_version with
    | Some v -> v
    | None -> Termcode.current_shape_version
  in
  { session_files = PHstr.create 3;
    session_shape_version = shape_version;
    session_dir   = dir;
  }

let create_session ?shape_version project_dir =
  if not (Sys.file_exists project_dir) then
    begin
      dprintf debug
        "[Info] '%s' does not exists. Creating directory of that name \
 for the project@." project_dir;
      Unix.mkdir project_dir 0o777
    end;
  empty_session ?shape_version project_dir


let load_env_session ?(includes=[]) session conf_path_opt =
  let config = Whyconf.read_config conf_path_opt in
  let loadpath = (Whyconf.loadpath (Whyconf.get_main config)) @ includes in
  let env = Env.create_env loadpath in
  { session = session;
    env = env;
    whyconf = config;
    loaded_provers = PHprover.create 5;
  }

(************************)
(* session accessor     *)
(************************)

let get_session_file file = file.file_parent

let get_session_theory th = get_session_file th.theory_parent

let rec get_session_goal goal =
  match goal.goal_parent with
    | Parent_transf trans -> get_session_trans trans
    | Parent_theory th    -> get_session_theory th

and get_session_trans transf = get_session_goal transf.transf_parent

let get_session_proof_attempt pa = get_session_goal pa.proof_parent

let get_used_provers session =
  let sprover = ref Sprover.empty in
  session_iter_proof_attempt
    (fun pa -> sprover := Sprover.add pa.proof_prover !sprover)
    session;
  !sprover

exception NoTask

let goal_task g = Util.exn_option NoTask g.goal_task
let goal_task_option g = g.goal_task

let goal_expl g = Util.def_option g.goal_name.Ident.id_string g.goal_expl

(************************)
(* saving state on disk *)
(************************)
open Format

let db_filename = "why3session.xml"

let save_string fmt s =
  for i=0 to String.length s - 1 do
    match String.get s i with
      | '\"' -> pp_print_string fmt "&quot;"
      | '\'' -> pp_print_string fmt "&apos;"
      | '<' -> pp_print_string fmt "&lt;"
      | '>' -> pp_print_string fmt "&gt;"
      | '&' -> pp_print_string fmt "&amp;"
      | c -> pp_print_char fmt c
  done


let save_result fmt r =
  fprintf fmt "@\n<result status=\"%s\" time=\"%.2f\"/>"
    (match r.Call_provers.pr_answer with
       | Call_provers.Valid -> "valid"
       | Call_provers.Failure _ -> "failure"
       | Call_provers.Unknown _ -> "unknown"
       | Call_provers.HighFailure -> "highfailure"
       | Call_provers.Timeout -> "timeout"
       | Call_provers.OutOfMemory -> "outofmemory"
       | Call_provers.Invalid -> "invalid")
    r.Call_provers.pr_time

let save_status fmt s =
  match s with
    | Undone Unedited ->
        fprintf fmt "<unedited/>@\n"
    | Undone _ ->
        fprintf fmt "<undone/>@\n"
    | InternalFailure msg ->
        fprintf fmt "<internalfailure reason=\"%a\"/>@\n"
          save_string (Printexc.to_string msg)
    | Done r -> save_result fmt r


let opt lab fmt = function
  | None -> ()
  | Some s -> fprintf fmt "%s=\"%a\"@ " lab save_string s

let save_proof_attempt provers fmt _key a =
  fprintf fmt
    "@\n@[<v 1><proof@ prover=\"%i\"@ timelimit=\"%d\"@ \
memlimit=\"%d\"@ %aobsolete=\"%b\"@ archived=\"%b\">"
    (Mprover.find a.proof_prover provers) a.proof_timelimit
    a.proof_memlimit
    (opt "edited") a.proof_edited_as a.proof_obsolete
    a.proof_archived;
  save_status fmt a.proof_state;
  fprintf fmt "@]@\n</proof>"

let save_ident fmt id =
  fprintf fmt "name=\"%a\"" save_string id.Ident.id_string;
  match id.Ident.id_loc with
    | None -> ()
    | Some loc ->
      let file,lnum,cnumb,cnume = Loc.get loc in
      fprintf fmt
        "@ locfile=\"%a\"@ loclnum=\"%i\" loccnumb=\"%i\" loccnume=\"%i\""
        save_string file lnum cnumb cnume

let save_label fmt s =
  fprintf fmt "@\n@[<v 1><label@ name=\"%a\"/>@]" save_string s.Ident.lab_string

let rec save_goal provers fmt g =
  assert (Tc.string_of_shape g.goal_shape <> "");
  fprintf fmt
    "@\n@[<v 1><goal@ %a@ %asum=\"%a\"@ proved=\"%b\"@ \
expanded=\"%b\"@ shape=\"%a\">"
    save_ident g.goal_name
    (opt "expl") g.goal_expl
    save_string (Tc.string_of_checksum g.goal_checksum)
    g.goal_verified  g.goal_expanded
    save_string (Tc.string_of_shape g.goal_shape);
  Ident.Slab.iter (save_label fmt) g.goal_name.Ident.id_label;
  PHprover.iter (save_proof_attempt provers fmt) g.goal_external_proofs;
  PHstr.iter (save_trans provers fmt) g.goal_transformations;
  fprintf fmt "@]@\n</goal>"

and save_trans provers fmt _ t =
  fprintf fmt "@\n@[<v 1><transf@ name=\"%a\"@ proved=\"%b\"@ expanded=\"%b\">"
    save_string t.transf_name t.transf_verified t.transf_expanded;
  List.iter (save_goal provers fmt) t.transf_goals;
  fprintf fmt "@]@\n</transf>"

let save_theory provers fmt t =
  fprintf fmt
    "@\n@[<v 1><theory@ %a@ verified=\"%b\"@ expanded=\"%b\">"
    save_ident t.theory_name
    t.theory_verified t.theory_expanded;
  Ident.Slab.iter (save_label fmt) t.theory_name.Ident.id_label;
  List.iter (save_goal provers fmt) t.theory_goals;
  fprintf fmt "@]@\n</theory>"

let save_file provers fmt _ f =
  fprintf fmt
    "@\n@[<v 1><file@ name=\"%a\"@ %averified=\"%b\"@ expanded=\"%b\">"
    save_string f.file_name (opt "format")
    f.file_format f.file_verified f.file_expanded;
  List.iter (save_theory provers fmt) f.file_theories;
  fprintf fmt "@]@\n</file>"

let save_prover fmt p (provers,id) =
  fprintf fmt "@\n@[<v 1><prover@ id=\"%i\"@ \
name=\"%a\"@ version=\"%a\"%a/>@]"
    id save_string p.C.prover_name save_string p.C.prover_version
    (fun fmt s -> if s <> "" then fprintf fmt "@ alternative=\"%a\""
        save_string s)
    p.C.prover_altern;
  Mprover.add p id provers, id+1

let save fname config session =
  let ch = open_out fname in
  let fmt = formatter_of_out_channel ch in
  fprintf fmt "<?xml version=\"1.0\" encoding=\"UTF-8\"?>@\n";
  fprintf fmt "<!DOCTYPE why3session SYSTEM \"%a\">@\n"
    save_string (Filename.concat (Whyconf.datadir (Whyconf.get_main config))
                   "why3session.dtd");
  fprintf fmt "@[<v 1><why3session@ name=\"%a\" shape_version=\"%d\">"
    save_string fname session.session_shape_version;
  let provers,_ = Sprover.fold (save_prover fmt) (get_used_provers session)
    (Mprover.empty,0) in
  PHstr.iter (save_file provers fmt) session.session_files;
  fprintf fmt "@]@\n</why3session>";
  fprintf fmt "@.";
  close_out ch

let save_session config session =
  let f = Filename.concat session.session_dir db_filename in
  Sysutil.backup_file f;
  save f config session

(*******************************)
(*          explanations       *)
(*******************************)

let expl_regexp = Str.regexp "expl:\\(.*\\)"

exception Found of string

let check_expl lab =
  let lab = lab.Ident.lab_string in
  if Str.string_match expl_regexp lab 0 then
    raise (Found (Str.matched_group 1 lab))

let rec get_expl_fmla f =
  Ident.Slab.iter check_expl f.Term.t_label;
  (match f.Term.t_node with
    | Term.Tbinop(Term.Timplies,_,f) -> get_expl_fmla f
    | Term.Tquant(Term.Tforall,fq) ->
      let (_,_,f) = Term.t_open_quant fq in get_expl_fmla f
    | Term.Tlet(_,fb) ->
      let (_,f) = Term.t_open_bound fb in get_expl_fmla f
    | Term.Tcase(_,[fb]) ->
      let (_,f) = Term.t_open_branch fb in get_expl_fmla f
    | _ -> ())

type expl = string option

let get_explanation id task =
  let fmla = Task.task_goal_fmla task in
  try
    get_expl_fmla fmla;
    Ident.Slab.iter check_expl id.Ident.id_label;
    None
  with Found e -> Some e


(*****************************)
(*   update verified field   *)
(*****************************)
type 'a notify = 'a any -> unit
let notify : 'a notify = fun _ -> ()

let file_verified f =
  List.for_all (fun t -> t.theory_verified) f.file_theories

let theory_verified t =
  List.for_all (fun g -> g.goal_verified) t.theory_goals

let transf_verified t =
  List.for_all (fun g -> g.goal_verified) t.transf_goals

let proof_verified a =
  (not a.proof_obsolete) &&
    match a.proof_state with
      | Done { Call_provers.pr_answer = Call_provers.Valid} -> true
      | _ -> false

let goal_verified g =
    try
      PHprover.iter
        (fun _ a ->
          if proof_verified a
          then raise Exit)
        g.goal_external_proofs;
      PHstr.iter
        (fun _ t -> if t.transf_verified then raise Exit)
        g.goal_transformations;
      false
    with Exit -> true

let check_file_verified notify f =
  let b = file_verified f in
  if f.file_verified <> b then begin
    f.file_verified <- b;
    notify (File f)
  end

let check_theory_proved notify t =
  let b = theory_verified t in
  if t.theory_verified <> b then begin
    t.theory_verified <- b;
    notify (Theory t);
    check_file_verified notify t.theory_parent
  end

let rec check_goal_proved notify g =
  let b = goal_verified g in
  if g.goal_verified <> b then begin
    g.goal_verified <- b;
    notify (Goal g);
    match g.goal_parent with
      | Parent_theory t -> check_theory_proved notify t
      | Parent_transf t -> check_transf_proved notify t
  end

and check_transf_proved notify t =
  let b = transf_verified t in
  if t.transf_verified <> b then begin
    t.transf_verified <- b;
    notify (Transf t);
    check_goal_proved notify t.transf_parent
  end

(******************************)
(* raw additions to the model *)
(******************************)
type 'a keygen = ?parent:'a -> unit -> 'a

let add_external_proof
    ?(notify=notify)
    ~(keygen:'a keygen) ~obsolete
    ~archived ~timelimit ~memlimit ~edit (g:'a goal) p result =
  assert (edit <> Some "");
  let key = keygen ~parent:g.goal_key () in
  let a = { proof_prover = p;
            proof_parent = g;
            proof_key = key;
            proof_obsolete = obsolete;
            proof_archived = archived;
            proof_state = result;
            proof_timelimit = timelimit;
            proof_memlimit = memlimit;
            proof_edited_as = edit;
          }
  in
  PHprover.replace g.goal_external_proofs p a;
  check_goal_proved notify g;
  a

let remove_external_proof ?(notify=notify) a =
  let g = a.proof_parent in
  PHprover.remove g.goal_external_proofs a.proof_prover;
  check_goal_proved notify g


let set_proof_state ?(notify=notify) ~obsolete ~archived res a =
  a.proof_state <- res;
  a.proof_obsolete <- obsolete;
  a.proof_archived <- archived;
  notify (Proof_attempt a);
  check_goal_proved notify a.proof_parent

let change_prover a p =
  let g = a.proof_parent in
  PHprover.remove g.goal_external_proofs a.proof_prover;
  PHprover.add g.goal_external_proofs p a;
  a.proof_prover <- p;
  a.proof_obsolete <- true

let set_edited_as edited_as a = a.proof_edited_as <- edited_as

let set_timelimit timelimit a = a.proof_timelimit <- timelimit
let set_memlimit memlimit a = a.proof_memlimit <- memlimit

let set_obsolete ?(notify=notify) a =
  a.proof_obsolete <- true;
  notify (Proof_attempt a);
  check_goal_proved notify a.proof_parent

let set_archived a b = a.proof_archived <- b

let get_edited_as_abs session pr =
  option_map (Filename.concat session.session_dir) pr.proof_edited_as

(* [raw_add_goal parent name expl sum t] adds a goal to the given parent
   DOES NOT record the new goal in its parent, thus this should not be exported
*)
let raw_add_no_task ~(keygen:'a keygen) parent name expl sum shape exp =
  let parent_key = match parent with
    | Parent_theory mth -> mth.theory_key
    | Parent_transf mtr -> mtr.transf_key
  in
  let key = keygen ~parent:parent_key () in
  let goal = { goal_name = name;
               goal_expl = expl;
               goal_parent = parent;
               goal_task = None ;
               goal_checksum = sum;
               goal_shape = shape;
               goal_key = key;
               goal_external_proofs = PHprover.create 7;
               goal_transformations = PHstr.create 3;
               goal_verified = false;
               goal_expanded = exp;
             }
  in
  goal

let raw_add_task ~version ~(keygen:'a keygen) parent name expl t exp =
  let parent_key = match parent with
    | Parent_theory mth -> mth.theory_key
    | Parent_transf mtr -> mtr.transf_key
  in
  let key = keygen ~parent:parent_key () in
  let sum = Termcode.task_checksum ~version t in
  let shape = Termcode.t_shape_buf ~version
    (Task.task_goal_fmla t) in
  let goal = { goal_name = name;
               goal_expl = expl;
               goal_parent = parent;
               goal_task = Some t ;
               goal_checksum = sum;
               goal_shape = shape;
               goal_key = key;
               goal_external_proofs = PHprover.create 7;
               goal_transformations = PHstr.create 3;
               goal_verified = false;
               goal_expanded = exp;
             }
  in
  goal


(* [raw_add_transformation g name adds a transformation to the given goal g
   Adds no subgoals, thus this should not be exported
*)
let raw_add_transformation ~(keygen:'a keygen) g name exp =
  let parent = g.goal_key in
  let key = keygen ~parent () in
  let tr = { transf_name = name;
             transf_parent = g;
             transf_verified = false;
             transf_key = key;
             transf_goals = [];
             transf_expanded = exp;
           }
  in
  PHstr.replace g.goal_transformations name tr;
  tr

let raw_add_theory ~(keygen:'a keygen) mfile thname exp =
  let parent = mfile.file_key in
  let key = keygen ~parent () in
  let mth = { theory_name = thname;
              theory_key = key;
              theory_parent = mfile;
              theory_goals = [];
              theory_verified = false;
              theory_expanded = exp;
            }
  in
  mth

let raw_add_file ~(keygen:'a keygen) session f fmt exp =
  let key = keygen () in
  let mfile = { file_name = f;
                file_key = key;
                file_format = fmt;
                file_theories = [];
                file_verified = false;
                file_expanded = exp;
                file_parent  = session;
              }
  in
  PHstr.replace session.session_files f mfile;
  mfile


(****************************)
(*     session opening      *)
(****************************)

exception LoadError of Xml.element * string
(** LoadError (xml,messg) *)

let bool_attribute field r def =
  try
    match List.assoc field r.Xml.attributes with
      | "true" -> true
      | "false" -> false
      | _ -> assert false
  with Not_found -> def

let int_attribute field r def =
  try
    int_of_string (List.assoc field r.Xml.attributes)
  with Not_found | Invalid_argument _ -> def

let string_attribute_def field r def=
  try
    List.assoc field r.Xml.attributes
  with Not_found -> def

let string_attribute field r =
  try
    List.assoc field r.Xml.attributes
  with Not_found ->
    eprintf "[Error] missing required attribute '%s' from element '%s'@."
      field r.Xml.name;
    assert false

let keygen ?parent:_ () = ()

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
            | "highfailure" -> Call_provers.Failure ""
            | s ->
                eprintf
                  "[Warning] Session.load_result: unexpected status '%s'@." s;
                Call_provers.Failure ""
        in
        let time =
          try float_of_string (List.assoc "time" r.Xml.attributes)
          with Not_found -> 0.0
        in
        Done {
          Call_provers.pr_answer = answer;
          Call_provers.pr_time = time;
          Call_provers.pr_output = "";
          Call_provers.pr_status = Unix.WEXITED 0
        }
    | "undone" -> Undone Interrupted
    | "unedited" -> Undone Unedited
    | s ->
        eprintf "[Warning] Session.load_result: unexpected element '%s'@." s;
        Undone Interrupted

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

let rec load_goal ~old_provers parent acc g =
  match g.Xml.name with
    | "goal" ->
        let gname = load_ident g in
        let expl = load_option "expl" g in
        let sum = Tc.checksum_of_string (string_attribute_def "sum" g "") in
        let shape = Tc.shape_of_string (string_attribute_def "shape" g "") in
        let exp = bool_attribute "expanded" g true in
        let mg = raw_add_no_task ~keygen parent gname expl sum shape exp in
        List.iter (load_proof_or_transf ~old_provers mg) g.Xml.elements;
        mg.goal_verified <- goal_verified mg;
        mg::acc
    | "label" -> acc
    | s ->
        eprintf "[Warning] Session.load_goal: unexpected element '%s'@." s;
        acc

and load_proof_or_transf ~old_provers mg a =
  match a.Xml.name with
    | "proof" ->
        let prover = string_attribute "prover" a in
        let p =
          try
            let p = Util.Mstr.find prover old_provers in
            p
          with Not_found ->
            eprintf "[Error] prover not listing in header '%s'@." prover;
            raise (LoadError (a,"prover not listing in header"))
        in
        let res = match a.Xml.elements with
          | [r] -> load_result r
          | [] -> Undone Interrupted
          | _ ->
            eprintf "[Error] Too many result elements@.";
            raise (LoadError (a,"too many result elements"))

        in
        let edit = load_option "edited" a in
        let edit = match edit with None | Some "" -> None | _ -> edit in
        let obsolete = bool_attribute "obsolete" a true in
        let archived = bool_attribute "archived" a false in
        let timelimit = int_attribute "timelimit" a 2 in
        let memlimit = int_attribute "memlimit" a 0 in
(*
        if timelimit < 0 then begin
            eprintf "[Error] incorrect or unspecified  timelimit '%i'@."
              timelimit;
            raise (LoadError (a,sprintf "incorrect or unspecified timelimit %i"
              timelimit))
        end;
*)
        let (_ : 'a proof_attempt) =
          add_external_proof ~keygen ~archived ~obsolete
            ~timelimit ~memlimit ~edit mg p res
        in
        ()
    | "transf" ->
        let trname = string_attribute "name" a in
        let exp = bool_attribute "expanded" a true in
        let mtr = raw_add_transformation ~keygen mg trname exp in
        mtr.transf_goals <-
          List.rev
          (List.fold_left
             (load_goal ~old_provers (Parent_transf mtr))
             [] a.Xml.elements);
        (* already done by raw_add_transformation
           Hashtbl.add mg.transformations trname mtr *)
        mtr.transf_verified <- transf_verified mtr
    | "label" -> ()
    | s ->
        eprintf
          "[Warning] Session.load_proof_or_transf: unexpected element '%s'@."
          s

let load_theory ~old_provers mf acc th =
  match th.Xml.name with
    | "theory" ->
        let thname = load_ident th in
        let exp = bool_attribute "expanded" th true in
        let mth = raw_add_theory ~keygen mf thname exp in
        mth.theory_goals <-
          List.rev
          (List.fold_left
             (load_goal ~old_provers (Parent_theory mth))
             [] th.Xml.elements);
        mth.theory_verified <- theory_verified mth;
        mth::acc
    | s ->
        eprintf "[Warning] Session.load_theory: unexpected element '%s'@." s;
        acc

let load_file session old_provers f =
  match f.Xml.name with
    | "file" ->
        let fn = string_attribute "name" f in
        let fmt = load_option "format" f in
        let exp = bool_attribute "expanded" f true in
        let mf = raw_add_file ~keygen session fn fmt exp in
        mf.file_theories <-
          List.rev
          (List.fold_left
             (load_theory ~old_provers mf) [] f.Xml.elements);
        mf.file_verified <- file_verified mf;
        old_provers
    | "prover" ->
      (** The id is just for the session file *)
        let id = string_attribute "id" f in
        let name = string_attribute "name" f in
        let version = string_attribute "version" f in
        let altern = string_attribute_def "alternative" f "" in
        let p = {C.prover_name = name;
                   prover_version = version;
                   prover_altern = altern} in
        Util.Mstr.add id p old_provers
    | s ->
        eprintf "[Warning] Session.load_file: unexpected element '%s'@." s;
        old_provers

let old_provers = ref Util.Mstr.empty
let get_old_provers () = !old_provers

let load_session session xml =
  match xml.Xml.name with
    | "why3session" ->
      let shape_version = int_attribute "shape_version" xml 1 in
      session.session_shape_version <- shape_version;
      dprintf debug "[Info] load_session: shape version is %d@\n" shape_version;
      (** just to keep the old_provers somewhere *)
      old_provers :=
        List.fold_left (load_file session) Util.Mstr.empty xml.Xml.elements;
      dprintf debug "[Info] load_session: done@\n"
    | s ->
        eprintf "[Warning] Session.load_session: unexpected element '%s'@." s

exception OpenError of string
type notask = unit
let read_session dir =
  if not (Sys.file_exists dir && Sys.is_directory dir) then
    raise (OpenError (Pp.sprintf "%s is not an existing directory" dir));
  let xml_filename = Filename.concat dir db_filename in
  let session = empty_session dir in
  (** If the xml is present we read it, otherwise we consider it empty *)
  if Sys.file_exists xml_filename then begin
    try
      let xml = Xml.from_file xml_filename in
      try
        load_session session xml.Xml.content;
      with Sys_error msg ->
        failwith ("Open session: sys error " ^ msg)
    with
      | Sys_error _msg ->
      (* xml does not exist yet *)
        raise (OpenError "Can't open")
      | Xml.Parse_error s ->
        Format.eprintf "XML database corrupted, ignored (%s)@." s;
      (* failwith
         ("Open session: XML database corrupted (%s)@." ^ s) *)
        raise (OpenError "XML corrupted")
  end;
  session


(*******************************)
(* Session modification        *)
(* expansion, add childs, ...  *)
(*******************************)

let rec set_goal_expanded g b =
  g.goal_expanded <- b;
  if not b then
    PHstr.iter (fun _ tr -> set_transf_expanded tr b) g.goal_transformations

and set_transf_expanded tr b =
  tr.transf_expanded <- b;
  if not b then
    List.iter (fun g -> set_goal_expanded g b) tr.transf_goals

let set_theory_expanded t b =
  t.theory_expanded <- b;
  if not b then
    List.iter (fun th -> set_goal_expanded th b) t.theory_goals

let set_file_expanded f b =
  f.file_expanded <- b;
  if not b then
    List.iter (fun th -> set_theory_expanded th b) f.file_theories


(** raw add_file *)
let raw_add_file ~version ~x_keygen ~x_goal ~x_fold_theory ~x_fold_file =
  let add_goal parent acc goal =
    let g =
      let name,expl,task = x_goal goal in
      raw_add_task ~version ~keygen:x_keygen parent name expl task false in
    g::acc in
  let add_file session f_name fmt file =
    let rfile = raw_add_file ~keygen:x_keygen session f_name fmt false in
    let add_theory acc thname theory =
      let rtheory = raw_add_theory ~keygen:x_keygen rfile thname false in
      let parent = Parent_theory rtheory in
      let goals = x_fold_theory (add_goal parent) [] theory in
      rtheory.theory_goals <- List.rev goals;
      rtheory.theory_verified <- theory_verified rtheory;
      rtheory::acc
    in
    let theories = x_fold_file add_theory [] file in
    rfile.file_theories <- List.rev theories;
    rfile in
  add_file

(** nice functor *)

module AddFile(X : sig
  type key
  val keygen : key keygen

  type goal
  val goal : goal -> Ident.ident * string option * Task.task

  type theory
  val fold_theory : ('a -> goal -> 'a) -> 'a -> theory -> 'a

  type file
  val fold_file :
    ('a -> Ident.ident (** thname *) -> theory -> 'a) ->
    'a -> file -> 'a

end) = (struct
  let add_file session fn ?format f =
    let file = raw_add_file ~x_keygen:X.keygen ~x_goal:X.goal
      ~version:Termcode.current_shape_version
    ~x_fold_theory:X.fold_theory ~x_fold_file:X.fold_file session
    fn format f in
    check_file_verified notify file;
    file
end : sig
  val add_file :
    X.key session -> string -> ?format:string -> X.file -> X.key file
end)

(* add a why file from a session *)
(** Read file and sort theories by location *)
let read_file env ?format fn =
  let theories = Env.read_file env ?format fn in
  let theories =
    Util.Mstr.fold
      (fun name th acc ->
        (** Hack : with WP [name] and [th.Theory.th_name.Ident.id_string] *)
        let th_name =
          Ident.id_register (Ident.id_derive name th.Theory.th_name) in
         match th.Theory.th_name.Ident.id_loc with
           | Some l -> (l,th_name,th)::acc
           | None   -> (Loc.dummy_position,th_name,th)::acc)
      theories []
  in
  List.sort
    (fun (l1,_,_) (l2,_,_) -> Loc.compare l1 l2)
    theories

let goal_expl_task task =
  let gid = (Task.task_goal task).Decl.pr_name in
  let info = get_explanation gid task in
  gid, info, task

let add_file ~keygen env ?format filename =
  let x_keygen = keygen in
  let x_goal = goal_expl_task in
  let x_fold_theory f acc th =
    let tasks = List.rev (Task.split_theory th None None) in
    List.fold_left f acc tasks in
  let x_fold_file f acc (env,fname) =
    let theories = read_file env ?format fname in
    List.fold_left (fun acc (_,thname,th) -> f acc thname th) acc theories in
  dprintf debug "[Load] file '%s'@\n" filename;
  let file = Filename.concat env.session.session_dir filename in
  let add_file = raw_add_file ~version:env.session.session_shape_version
    ~x_keygen ~x_goal ~x_fold_theory ~x_fold_file in
  let file = add_file env.session filename format (env.env,file) in
  check_file_verified notify file;
  file

let remove_file file =
  let s = file.file_parent in
  PHstr.remove s.session_files file.file_name

(** Transformation *)

module AddTransf(X : sig
  type key
  val keygen : key keygen

  type goal
  val goal : goal -> Ident.ident * string option * Task.task

  type transf
  val fold_transf : ('a -> goal -> 'a) -> 'a -> Task.task -> transf -> 'a
end) = (struct

  let add_goal parent acc goal =
    let name,expl,task = X.goal goal in
    let g =
      raw_add_task ~version:Termcode.current_shape_version
        ~keygen:X.keygen parent
        name expl task false in
    (** no verified since that can't be empty (no proof no transf) and true *)
    g::acc

  let add_transformation g name transf =
    let task = goal_task g in
    let rtransf = raw_add_transformation ~keygen:X.keygen g name true in
    let parent = Parent_transf rtransf in
    let goals = X.fold_transf (add_goal parent) [] task transf in
    rtransf.transf_goals <- List.rev goals;
    rtransf.transf_verified <- transf_verified rtransf;
    rtransf

end : sig
  val add_transformation : X.key goal -> string -> X.transf -> X.key transf
end)

let add_transformation ~keygen ~goal env_session transfn g goals =
  let rtransf = raw_add_transformation ~keygen g transfn true in
  let parent = Parent_transf rtransf in
  let add_goal acc g =
    let name,expl,task = goal g in
    let g = raw_add_task ~version:env_session.session.session_shape_version
      ~keygen parent name expl task  false in
    g::acc in
  let goals = List.fold_left add_goal [] goals in
  rtransf.transf_goals <- List.rev goals;
  rtransf.transf_verified <- transf_verified rtransf;
  rtransf


let remove_transformation ?(notify=notify) t =
  let g = t.transf_parent in
  PHstr.remove g.goal_transformations t.transf_name;
  check_goal_proved notify g


(***************************)
(*      transformations    *)
(***************************)
let add_registered_transformation ~keygen env_session tr_name g =
  let task = goal_task g in
  let gname = g.goal_name in
  let subgoals = Trans.apply_transform tr_name env_session.env task in
  let i = ref 1 in
  let goal task =
    let gid = (Task.task_goal task).Decl.pr_name in
    let expl = get_explanation gid task in
    let goal_name = gname.Ident.id_string ^ "." ^ (string_of_int (!i)) in
    incr i;
    let goal_name = Ident.id_register (Ident.id_derive goal_name gid) in
    goal_name, expl, task
  in
  add_transformation ~keygen ~goal env_session tr_name g subgoals

(*****************************************************)
(**                    Prover Loaded                **)
(*****************************************************)

let load_prover eS prover =
  try
    PHprover.find eS.loaded_provers prover
  with Not_found ->
    let provers = Whyconf.get_provers eS.whyconf in
    let r = Mprover.find_opt prover provers in
    let r = match r with
      | None -> None
      | Some pr ->
        let dr = Driver.load_driver eS.env
          pr.Whyconf.driver pr.Whyconf.extra_drivers in
        Some { prover_config = pr;
               prover_driver = dr}
    in
    PHprover.add eS.loaded_provers prover r;
    r

let unload_provers eS = PHprover.clear eS.loaded_provers

let () = Exn_printer.register
  (fun fmt exn ->
    match exn with
      | NoTask ->
        Format.fprintf fmt
          "A goal doesn't contain a task but here it needs one"
      | _ -> raise exn)


let ft_of_th th =
  let fn = Filename.basename th.theory_parent.file_name in
  let fn = try Filename.chop_extension fn with Invalid_argument _ -> fn in
  (fn, th.theory_name.Ident.id_string)

let rec ft_of_goal g =
  match g.goal_parent with
    | Parent_transf tr -> ft_of_goal tr.transf_parent
    | Parent_theory th -> ft_of_th th

let ft_of_pa a =
  ft_of_goal a.proof_parent

(** TODO see with Undone Edited
    But since it will be perhaps removed...
 *)
let copy_external_proof
    ?notify ~keygen ?obsolete ?archived ?timelimit ?memlimit ?edit
    ?goal ?prover ?attempt_status ?env_session ?session a =
  let session = match env_session with
    | Some eS -> Some eS.session
    | _ -> session in
  let obsolete = def_option a.proof_obsolete obsolete in
  let archived = def_option a.proof_archived archived in
  let timelimit = def_option a.proof_timelimit timelimit in
  let memlimit = def_option a.proof_memlimit memlimit in
  let pas = def_option a.proof_state attempt_status in
  let ngoal = def_option a.proof_parent goal in
  let nprover = match prover with
    | None -> a.proof_prover
    | Some prover -> prover in
  (** copy or generate the edit file if needed *)
  let edit =
    match edit, a.proof_edited_as, session with
      | Some edit, _, _ -> edit
      | _, None, _ -> None
      | _, _, None -> (** In the other case a session is needed *)
        None
      | _, Some file, Some session ->
        assert (file != "");
        (** Copy the edited file *)
        let dir = session.session_dir in
        let file = Filename.concat dir file in
        if not (Sys.file_exists file) then None else
        match prover,goal, ngoal.goal_task, env_session with
          | None,None,_,_ ->
            let dst_file = Sysutil.uniquify file in
            Sysutil.copy_file file dst_file;
            let dst_file = Sysutil.relativize_filename dir dst_file in
            Some dst_file
          | (_, _, None,_)| (_, _, _, None) ->
            (** In the other cases an env_session and a task are needed *)
            None
          | _, _, Some task, Some env_session ->
            match load_prover env_session nprover with
              | None -> None
              | Some prover_conf ->
            let (fn,tn) = ft_of_goal ngoal in
            let driver = prover_conf.prover_driver in
            let dst_file = Driver.file_of_task driver fn tn task in
            let dst_file = Filename.concat dir dst_file in
            let dst_file = Sysutil.uniquify dst_file in
            let old = open_in file in
            let ch = open_out dst_file in
            let fmt = formatter_of_out_channel ch in
            Driver.print_task ~old driver fmt task;
            close_in old;
            close_out ch;
            let dst_file = Sysutil.relativize_filename dir dst_file in
            Some (dst_file)
  in
  add_external_proof ?notify ~keygen
    ~obsolete ~archived ~timelimit ~memlimit ~edit ngoal nprover pas

exception UnloadableProver of Whyconf.prover

let update_edit_external_proof env_session a =
  let prover_conf = match load_prover env_session a.proof_prover with
    | Some prover_conf -> prover_conf
    | None -> raise (UnloadableProver a.proof_prover) in
  let driver = prover_conf.prover_driver in
  let goal = goal_task a.proof_parent in
  let session_dir = env_session.session.session_dir in
  let file =
    match a.proof_edited_as with
      | None ->
        let (fn,tn) = ft_of_pa a in
        let file = Driver.file_of_task driver fn tn goal in
        let file = Filename.concat session_dir file in
        let file = Sysutil.uniquify file in
        let file = Sysutil.relativize_filename session_dir file in
        set_edited_as (Some file) a;
        if a.proof_state = Undone Unedited
        then set_proof_state ~notify ~obsolete:a.proof_obsolete
          ~archived:a.proof_archived
          (Undone Interrupted) a;
        file
      | Some f -> f
  in
  let file = Filename.concat session_dir file in
  let old =
    if Sys.file_exists file
    then
      begin
        let backup = file ^ ".bak" in
        if Sys.file_exists backup
        then Sys.remove backup;
        Sys.rename file backup;
        Some(open_in backup)
      end
    else None
  in
  let ch = open_out file in
  let fmt = formatter_of_out_channel ch in
  Driver.print_task ?old driver fmt goal;
  Util.option_iter close_in old;
  close_out ch;
  file

let print_attempt_status fmt = function
  | Undone _ -> pp_print_string fmt "Undone"
  | Done pr -> Call_provers.print_prover_result fmt pr
  | InternalFailure _ -> pp_print_string fmt "Failure"

let print_external_proof fmt p =
  fprintf fmt "%a - %a (%i, %i)%s%s%s"
    Whyconf.print_prover p.proof_prover
    print_attempt_status p.proof_state
    p.proof_timelimit p.proof_memlimit
    (if p.proof_obsolete then " obsolete" else "")
    (if p.proof_archived then " archived" else "")
    (if p.proof_edited_as <> None then " edited" else "")

(***********************************************************)
(**    Reload a session with the current transformation    *)
(***********************************************************)

(** Pairing *)

module AssoGoals : sig
  val associate : 'a goal list -> 'b goal list ->
    ('b goal * ('a goal option) * bool) list
end = struct
(** When Why3 will require 3.12 put all of that in a function using
    explicit type argument "(type t)" and remove all the Obj.magic *)

  module ToGoal = struct
    (** The functor can't be instantiated with an 'a t so we will give
        a t *)
    type tto (** will represent any type *)
    type t = tto goal
    let checksum g = g.goal_checksum
    let shape g    = g.goal_shape
    let name g     = g.goal_name
  end
  module FromGoal = struct
    (** The functor can't be instantiated with an 'a t so we will give
        a t *)
    type ffrom (** will represent any type *)
    type t = ffrom goal
    let checksum g = g.goal_checksum
    let shape g    = g.goal_shape
    let name g     = g.goal_name
  end

  module AssoGoals = Tc.AssoMake(FromGoal)(ToGoal)
  open ToGoal
  open FromGoal

  let associate (from_goals: 'ffrom goal list) (to_goals: 'tto goal list) :
      ('tto goal * ('ffrom goal option) * bool) list =
    let from_goals : ffrom goal list =
      Obj.magic (from_goals : 'ffrom goal list) in
    let to_goals   : tto goal list =
      Obj.magic (to_goals : 'tto goal list) in
    let associated : (tto goal * (ffrom goal option) * bool) list =
      AssoGoals.associate from_goals to_goals in
    (Obj.magic associated : ('tto goal * ('ffrom goal option) * bool) list)

end

(**********************************)
(* merge a file into another      *)
(**********************************)

let merge_proof ~keygen obsolete to_goal _ from_proof =
  ignore
    (add_external_proof ~keygen
       ~obsolete:(obsolete || from_proof.proof_obsolete)
       ~archived:from_proof.proof_archived
       ~timelimit:from_proof.proof_timelimit
       ~memlimit:from_proof.proof_memlimit
       ~edit:from_proof.proof_edited_as
       to_goal
       from_proof.proof_prover
       from_proof.proof_state)

let rec merge_any_goal ~keygen env obsolete from_goal to_goal =
  set_goal_expanded to_goal from_goal.goal_expanded;
  PHprover.iter (merge_proof ~keygen obsolete to_goal)
    from_goal.goal_external_proofs;
  PHstr.iter (merge_trans ~keygen env to_goal) from_goal.goal_transformations

and merge_trans ~keygen env to_goal _ from_transf =
  let from_transf_name = from_transf.transf_name in
  let to_goal_name = to_goal.goal_name in
  dprintf debug "[Reload] transformation %s for goal %s @\n"
    from_transf_name to_goal_name.Ident.id_string;
  let to_transf =
    add_registered_transformation
      ~keygen env from_transf_name to_goal in
  let associated =
    dprintf debug "[Info] associate_subgoals, shape_version = %d@\n"
      env.session.session_shape_version;
    AssoGoals.associate from_transf.transf_goals to_transf.transf_goals in
  List.iter (function
  | (to_goal, Some from_goal, obsolete) ->
    merge_any_goal ~keygen env obsolete  from_goal to_goal
  | (_, None, _) -> ()
  ) associated

exception OutdatedSession

let merge_theory ~keygen env ~allow_obsolete from_th to_th =
  set_theory_expanded to_th from_th.theory_expanded;
  let from_goals = List.fold_left
    (fun from_goals g ->
      Util.Mstr.add g.goal_name.Ident.id_string g from_goals)
    Util.Mstr.empty from_th.theory_goals
  in
  Util.list_or
    (fun to_goal ->
      try
        let from_goal =
          Util.Mstr.find to_goal.goal_name.Ident.id_string from_goals in
        let goal_obsolete = to_goal.goal_checksum <> from_goal.goal_checksum in
        if goal_obsolete then
          begin
            dprintf debug "[Reload] Goal %s.%s has changed@\n"
              to_th.theory_name.Ident.id_string
              to_goal.goal_name.Ident.id_string;
            if not allow_obsolete then raise OutdatedSession
          end;
        merge_any_goal ~keygen env goal_obsolete from_goal to_goal;
        goal_obsolete
      with
        | Not_found when allow_obsolete -> true
        | Not_found -> raise OutdatedSession
    ) to_th.theory_goals

let merge_file ~keygen env ~allow_obsolete from_f to_f  =
  dprintf debug "[Info] merge_file, shape_version = %d@."
    env.session.session_shape_version;
  set_file_expanded to_f from_f.file_expanded;
  let from_theories = List.fold_left
    (fun acc t -> Util.Mstr.add t.theory_name.Ident.id_string t acc)
    Util.Mstr.empty from_f.file_theories
  in
  let b = 
    Util.list_or
    (fun to_th ->
      try
        let from_th =
          let name = to_th.theory_name.Ident.id_string in
          try Util.Mstr.find name from_theories
          (* TODO: remove this later when all sessions are updated *)
          with Not_found -> Util.Mstr.find ("WP "^name) from_theories
        in
        merge_theory ~keygen env ~allow_obsolete from_th to_th
      with
        | Not_found when allow_obsolete -> true
        | Not_found -> raise OutdatedSession
    )
    to_f.file_theories
  in
  dprintf debug "[Info] merge_file, done@\n";
  b



let rec recompute_all_shapes_goal g =
  let t = goal_task g in
  g.goal_shape <- Termcode.t_shape_buf (Task.task_goal_fmla t);
  g.goal_checksum <- Termcode.task_checksum t;
  PHstr.iter recompute_all_shapes_transf g.goal_transformations

and recompute_all_shapes_transf _ tr =
  List.iter recompute_all_shapes_goal tr.transf_goals

let recompute_all_shapes_theory t =
  List. iter recompute_all_shapes_goal t.theory_goals

let recompute_all_shapes_file _ f =
  List.iter recompute_all_shapes_theory f.file_theories

let recompute_all_shapes session =
  session.session_shape_version <- Termcode.current_shape_version;
  PHstr.iter recompute_all_shapes_file session.session_files

let update_session ~keygen ~allow_obsolete old_session env whyconf =
  dprintf debug "[Info] update_session: shape_version = %d@\n"
    old_session.session_shape_version;
  let new_session =
    create_session ~shape_version:old_session.session_shape_version
      old_session.session_dir
  in
  let new_env_session =
    { session = new_session;
      env = env;
      whyconf = whyconf;
      loaded_provers = PHprover.create 5;
    }
  in
  let obsolete = PHstr.fold (fun _ old_file acc ->
    dprintf debug "[Load] file '%s'@\n" old_file.file_name;
    let new_file = add_file
      ~keygen new_env_session
      ?format:old_file.file_format old_file.file_name
    in
    merge_file ~keygen new_env_session ~allow_obsolete old_file new_file
    || acc)
    old_session.session_files false 
  in
  dprintf debug "[Info] update_session: done@\n";
  let obsolete =
    if old_session.session_shape_version <> Termcode.current_shape_version then
      begin
        dprintf debug "[Info] update_session: recompute shapes@\n";
        recompute_all_shapes new_session;
        true
      end
    else obsolete in
  assert (new_env_session.session.session_shape_version
          = Termcode.current_shape_version);
  new_env_session, obsolete

let get_project_dir fname =
  if not (Sys.file_exists fname) then raise Not_found;
  let d =
    if Sys.is_directory fname then fname
    else if Filename.basename fname = db_filename then begin
      dprintf debug "Info: found db file '%s'@." fname;
      Filename.dirname fname
    end
    else
      begin
        dprintf debug "Info: found regular file '%s'@." fname;
        try Filename.chop_extension fname
        with Invalid_argument _ -> fname^".w3s"
      end
  in
  dprintf debug "Info: using '%s' as directory for the project@." d;
  d

let key_any = function
  | File p -> p.file_key
  | Transf tr -> tr.transf_key
  | Goal g -> g.goal_key
  | Proof_attempt p -> p.proof_key
  | Theory th -> th.theory_key

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3ide.byte"
End:
*)
