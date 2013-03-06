(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2013   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Debug
open Stdlib
open Ty
open Ident
open Decl
open Term
open Theory
open Task

module Mprover = Whyconf.Mprover
module Sprover = Whyconf.Sprover
module PHprover = Whyconf.Hprover
module C = Whyconf
module Tc = Termcode

let debug = Debug.register_info_flag "session"
  ~desc:"Pring@ debugging@ messages@ about@ Why3@ session@ \
         creation,@ reading@ and@ writing."

(** {2 Type definitions} *)

module PHstr = Hstr

type proof_attempt_status =
    | Unedited (** editor not yet run for interactive proof *)
    | JustEdited (** edited but not run yet *)
    | Interrupted (** external proof has never completed *)
    | Scheduled (** external proof attempt is scheduled *)
    | Running (** external proof attempt is in progress *)
    | Done of Call_provers.prover_result (** external proof done *)
    | InternalFailure of exn (** external proof aborted by internal error *)

type task_option = Task.task option

type ident_path =
  { ip_library : string list;
    ip_theory : string;
    ip_qualid : string list;
  }

let print_ident_path fmt ip =
  Format.fprintf fmt "%a.%s.%a"
    (Pp.print_list Pp.dot Pp.string) ip.ip_library
    ip.ip_theory
    (Pp.print_list Pp.dot Pp.string) ip.ip_qualid

let compare_ident_path x y =
  let c = Lists.compare String.compare x.ip_library y.ip_library in
  if c <> 0 then -c else (* in order to be bottom up *)
  let c = String.compare x.ip_theory y.ip_theory in
  if c <> 0 then c else
  let c = Lists.compare String.compare x.ip_qualid y.ip_qualid in
  c

module Pos = struct
  type t = ident_path
  let compare = compare_ident_path
  let equal x y = (x : t) = y
  let hash x = Hashtbl.hash (x : t)
end

module Mpos = Extmap.Make(Pos)
module Spos = Extset.MakeOfMap(Mpos)
module Hpos = Exthtbl.Make(Pos)

type meta_args = meta_arg list

module Mmeta_args = Extmap.Make(struct
  type t = meta_args

  let meta_arg_id = function
    | MAty _  -> 0
    | MAts _  -> 1
    | MAls _  -> 2
    | MApr _  -> 3
    | MAstr _ -> 4
    | MAint _ -> 5

  let compare_meta_arg x y =
    match x,y with
  (** These hash are in fact tag *)
    | MAty  x, MAty  y -> compare (ty_hash x) (ty_hash y)
    | MAts  x, MAts  y -> compare (ts_hash x) (ts_hash y)
    | MAls  x, MAls  y -> compare (ls_hash x) (ls_hash y)
    | MApr  x, MApr  y -> compare (pr_hash x) (pr_hash y)
    | MAstr x, MAstr y -> String.compare x y
    | MAint x, MAint y -> compare x y
    | _ -> compare (meta_arg_id x) (meta_arg_id y)

  let compare = Lists.compare compare_meta_arg
end)

module Smeta_args = Extset.MakeOfMap(Mmeta_args)

type metas_args = Smeta_args.t Mstr.t

module Mmetas_args = Extmap.Make(struct
  type t = metas_args
  let compare = Mstr.compare Smeta_args.compare
end)

type idpos = {
  idpos_ts : ident_path Mts.t;
  idpos_ls : ident_path Mls.t;
  idpos_pr : ident_path Mpr.t;
}

let empty_idpos =
  {
    idpos_ts = Mts.empty;
    idpos_ls = Mls.empty;
    idpos_pr = Mpr.empty;
  }

(* dead code
let posid_of_idpos idpos =
  let posid = Mpos.empty in
  let posid = Mts.fold (fun ts pos ->
    Mpos.add pos (MAts ts)) idpos.idpos_ts posid  in
  let posid = Mls.fold (fun ls pos ->
    Mpos.add pos (MAls ls)) idpos.idpos_ls posid  in
  let posid = Mpr.fold (fun pr pos ->
    Mpos.add pos (MApr pr)) idpos.idpos_pr posid  in
  posid
*)

type expl = string option

type 'a goal =
  { mutable goal_key  : 'a;
    goal_name : Ident.ident;
    goal_expl : expl;
    goal_parent : 'a goal_parent;
    mutable goal_checksum : Tc.checksum;
    mutable goal_shape : Tc.shape;
    mutable goal_verified : bool;
    goal_task: task_option;
    mutable goal_expanded : bool;
    goal_external_proofs : 'a proof_attempt PHprover.t;
    goal_transformations : 'a transf PHstr.t;
    mutable goal_metas : 'a metas Mmetas_args.t;
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
  | Parent_metas  of 'a metas

and 'a metas =
  { mutable metas_key : 'a;
    metas_added : metas_args;
    metas_idpos : idpos;
    metas_parent : 'a goal;
    mutable metas_verified : bool;
    mutable metas_goal : 'a goal;
    (** Not mutated after the creation *)
    mutable metas_expanded : bool;
  }

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
  | Metas of 'a metas

let rec goal_iter_proof_attempt f g =
  PHprover.iter (fun _ a -> f a) g.goal_external_proofs;
  PHstr.iter (fun _ t -> transf_iter_proof_attempt f t) g.goal_transformations;
  Mmetas_args.iter (fun _ t -> metas_iter_proof_attempt f t) g.goal_metas;

and transf_iter_proof_attempt f t =
  List.iter (goal_iter_proof_attempt f) t.transf_goals

and metas_iter_proof_attempt f t =
  goal_iter_proof_attempt f t.metas_goal

let theory_iter_proof_attempt f t =
  List.iter (goal_iter_proof_attempt f) t.theory_goals

let metas_iter_proof_attempt f m =
  goal_iter_proof_attempt f m.metas_goal

let file_iter_proof_attempt f t =
  List.iter (theory_iter_proof_attempt f) t.file_theories

let session_iter_proof_attempt f s =
  PHstr.iter (fun _ file -> file_iter_proof_attempt f file) s.session_files

let iter_proof_attempt f = function
    | Goal g -> goal_iter_proof_attempt f g
    | Theory th -> theory_iter_proof_attempt f th
    | File file -> file_iter_proof_attempt f file
    | Proof_attempt a -> f a
    | Transf tr -> transf_iter_proof_attempt f tr
    | Metas m -> metas_iter_proof_attempt f m

let rec goal_iter_leaf_goal ~unproved_only f g =
  if not (g.goal_verified && unproved_only) then
    let r = ref true in
    PHstr.iter
      (fun _ t -> r := false;
        List.iter (goal_iter_leaf_goal ~unproved_only f) t.transf_goals)
      g.goal_transformations;
    if !r then f g

(** iterators not reccursive *)
let iter_goal fp ft fm g =
  PHprover.iter (fun _ a -> fp a) g.goal_external_proofs;
  PHstr.iter (fun _ t -> ft t) g.goal_transformations;
  Mmetas_args.iter (fun _ t -> fm t) g.goal_metas

let iter_transf f t =
  List.iter (fun g -> f g) t.transf_goals

let iter_metas f t = f t.metas_goal

let iter_file f fi = List.iter f fi.file_theories

let iter_session f s = PHstr.iter (fun _ th -> f th) s.session_files

let goal_iter f g =
  PHprover.iter
    (fun _ a -> f (Proof_attempt a)) g.goal_external_proofs;
  PHstr.iter (fun _ t -> f (Transf t)) g.goal_transformations;
  Mmetas_args.iter (fun _ t -> f (Metas t)) g.goal_metas


let transf_iter f t =
  List.iter (fun g -> f (Goal g)) t.transf_goals

let metas_iter f t =
  f (Goal t.metas_goal)

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
    | Metas m -> metas_iter f m

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
          else tr.transf_name^"?"
        | Metas metas ->
          if metas.metas_verified
          then "metas..."
          else "metas..."^"?"
      in
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


(* dead code
let load_env_session ?(includes=[]) session conf_path_opt =
  let config = Whyconf.read_config conf_path_opt in
  let loadpath = (Whyconf.loadpath (Whyconf.get_main config)) @ includes in
  let env = Env.create_env loadpath in
  { session = session;
    env = env;
    whyconf = config;
    loaded_provers = PHprover.create 5;
  }
*)

(************************)
(* session accessor     *)
(************************)

(* dead code
let get_session_file file = file.file_parent

let get_session_theory th = get_session_file th.theory_parent

let rec get_session_goal goal =
  match goal.goal_parent with
    | Parent_transf trans -> get_session_trans trans
    | Parent_theory th    -> get_session_theory th
    | Parent_metas  metas -> get_session_metas metas


and get_session_trans transf = get_session_goal transf.transf_parent

and get_session_metas metas = get_session_goal metas.metas_parent

let get_session_proof_attempt pa = get_session_goal pa.proof_parent
*)

let get_used_provers session =
  let sprover = ref Sprover.empty in
  session_iter_proof_attempt
    (fun pa -> sprover := Sprover.add pa.proof_prover !sprover)
    session;
  !sprover

exception NoTask

let goal_task g = Opt.get_exn NoTask g.goal_task
let goal_task_option g = g.goal_task

let goal_expl g = Opt.get_def g.goal_name.Ident.id_string g.goal_expl

(************************)
(* saving state on disk *)
(************************)
open Format

let db_filename = "why3session.xml"
let session_dir_for_save = ref "."

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
    | Unedited ->
        fprintf fmt "@\n<unedited/>"
    | Scheduled | Running | Interrupted | JustEdited ->
        fprintf fmt "@\n<undone/>"
    | InternalFailure msg ->
        fprintf fmt "@\n<internalfailure reason=\"%a\"/>"
          save_string (Printexc.to_string msg)
    | Done r -> save_result fmt r


let opt lab fmt = function
  | None -> ()
  | Some s -> fprintf fmt "%s=\"%a\"@ " lab save_string s

let save_proof_attempt fmt (id,a) =
  fprintf fmt
    "@\n@[<v 1><proof@ prover=\"%i\"@ timelimit=\"%d\"@ \
memlimit=\"%d\"@ %aobsolete=\"%b\"@ archived=\"%b\">"
    id a.proof_timelimit a.proof_memlimit
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
      let file = Sysutil.relativize_filename !session_dir_for_save file in
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
  let l = PHprover.fold
    (fun _ a acc -> (Mprover.find a.proof_prover provers, a) :: acc)
    g.goal_external_proofs [] in
  let l = List.sort (fun (i1,_) (i2,_) -> compare i1 i2) l in
  List.iter (save_proof_attempt fmt) l;
  let l = PHstr.fold (fun _ t acc -> t :: acc) g.goal_transformations [] in
  let l = List.sort (fun t1 t2 -> compare t1.transf_name t2.transf_name) l in
  List.iter (save_trans provers fmt) l;
  Mmetas_args.iter (save_metas provers fmt) g.goal_metas;
  fprintf fmt "@]@\n</goal>"

and save_trans provers fmt t =
  fprintf fmt "@\n@[<v 1><transf@ name=\"%a\"@ proved=\"%b\"@ expanded=\"%b\">"
    save_string t.transf_name t.transf_verified t.transf_expanded;
  List.iter (save_goal provers fmt) t.transf_goals;
  fprintf fmt "@]@\n</transf>"

and save_metas provers fmt _ m =
  fprintf fmt "@\n@[<v 1><metas@ proved=\"%b\"@ expanded=\"%b\">"
    m.metas_verified m.metas_expanded;
  let save_pos fmt pos =
    fprintf fmt "@\n@[<v 1>ip_theory=\"%a\">" save_string pos.ip_theory;
    List.iter (fprintf fmt "@\n@[<v 1><ip_library@ name=\"%a\"/>@]" save_string)
      pos.ip_library;
    List.iter (fprintf fmt "@\n@[<v 1><ip_qualid@ name=\"%a\"/>@]" save_string)
      pos.ip_qualid;
    fprintf fmt "@]";
  in
  let save_ts_pos fmt ts pos =
    fprintf fmt "@\n@[<v 1><ts_pos@ name=\"%a\"@ arity=\"%i\"@ \
    id=\"%i\"@ %a</ts_pos>@]"
      save_string ts.ts_name.id_string (List.length ts.ts_args)
      (ts_hash ts) save_pos pos in
  let save_ls_pos fmt ls pos =
    (** TODO: add the signature? *)
    fprintf fmt "@\n@[<v 1><ls_pos@ name=\"%a\"@ id=\"%i\"@ %a</ls_pos>@]"
      save_string ls.ls_name.id_string
      (ls_hash ls) save_pos pos
  in
  let save_pr_pos fmt pr pos =
    fprintf fmt "@\n@[<v 1><pr_pos@ name=\"%a\"@ id=\"%i\"@ %a</pr_pos>@]"
      save_string pr.pr_name.id_string
      (pr_hash pr) save_pos pos
  in
  Mts.iter (save_ts_pos fmt) m.metas_idpos.idpos_ts;
  Mls.iter (save_ls_pos fmt) m.metas_idpos.idpos_ls;
  Mpr.iter (save_pr_pos fmt) m.metas_idpos.idpos_pr;
  Mstr.iter (fun s smeta_args ->
    Smeta_args.iter (save_meta_args fmt s) smeta_args) m.metas_added;
  save_goal provers fmt m.metas_goal;
  fprintf fmt "@]@\n</metas>"

and save_meta_args fmt s l =
  fprintf fmt "@\n@[<v 1><meta@ name=\"%a\">" save_string s;
  let save_meta_arg fmt = function
    | MAty ty -> fprintf fmt "@\n@[<v 1><meta_arg_ty/>";
      save_ty fmt ty;
      fprintf fmt "@]@\n</meta_arg_ty>"
    | MAts ts ->
      fprintf fmt "@\n@[<v 1><meta_arg_ts@ id=\"%i\"/>@]" (ts_hash ts)
    | MAls ls ->
      fprintf fmt "@\n@[<v 1><meta_arg_ls@ id=\"%i\"/>@]" (ls_hash ls)
    | MApr pr ->
      fprintf fmt "@\n@[<v 1><meta_arg_pr@ id=\"%i\"/>@]" (pr_hash pr)
    | MAstr s ->
      fprintf fmt "@\n@[<v 1><meta_arg_str@ val=\"%s\"/>@]" s
    | MAint i ->
      fprintf fmt "@\n@[<v 1><meta_arg_int@ val=\"%i\"/>@]" i
  in
  List.iter (save_meta_arg fmt) l;
  fprintf fmt "@]@\n</meta_args>"

and save_ty fmt ty =
  match ty.ty_node with
  | Tyvar tv ->
    fprintf fmt "@\n@[<v 1><ty_var@ id=\"%i\"/>@]" (tv_hash tv)
  | Tyapp (ts,l) ->
    fprintf fmt "@\n@[<v 1><ty_app@ id=\"%i\"/>" (ts_hash ts);
    List.iter (save_ty fmt) l;
    fprintf fmt "@]@\n</ty_app>"

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

let save fname _config session =
  let ch = open_out fname in
  let fmt = formatter_of_out_channel ch in
  fprintf fmt "<?xml version=\"1.0\" encoding=\"UTF-8\"?>@\n";
  fprintf fmt "<!DOCTYPE why3session PUBLIC \"-//Why3//proof session v2//EN\" \"http://why3.lri.fr/why3session.dtd\">@\n";
(*
  let rel_file = Sysutil.relativize_filename !session_dir_for_save fname in
  fprintf fmt "@[<v 1><why3session@ name=\"%a\" shape_version=\"%d\">"
    save_string rel_file session.session_shape_version;
*)
  fprintf fmt "@[<v 1><why3session shape_version=\"%d\">"
    session.session_shape_version;
  let provers,_ = Sprover.fold (save_prover fmt) (get_used_provers session)
    (Mprover.empty,0) in
  PHstr.iter (save_file provers fmt) session.session_files;
  fprintf fmt "@]@\n</why3session>";
  fprintf fmt "@.";
  close_out ch

let save_session config session =
  let f = Filename.concat session.session_dir db_filename in
  Sysutil.backup_file f;
  session_dir_for_save := session.session_dir;
  save f config session

(*******************************)
(*          explanations       *)
(*******************************)

let expl_regexp = Str.regexp "expl:\\(.*\\)"

let check_expl lab acc =
  let lab = lab.Ident.lab_string in
  if Str.string_match expl_regexp lab 0
  then Some (Str.matched_group 1 lab)
  else acc

let check_expl lab =
  if Ident.Slab.mem Split_goal.stop_split lab then None
  else Ident.Slab.fold check_expl lab None

let rec get_expl_fmla acc f =
  if f.t_ty <> None then acc else
  let res = check_expl f.Term.t_label in
  if res = None then match f.t_node with
    | Term.Ttrue | Term.Tfalse | Term.Tapp _ -> acc
    | Term.Tbinop(Term.Timplies,_,f) -> get_expl_fmla acc f
    | Term.Tlet _ | Term.Tcase _ | Term.Tquant (Term.Tforall, _) ->
        Term.t_fold get_expl_fmla acc f
    | _ -> raise Exit
  else if acc = None then res else raise Exit

let get_expl_fmla f = try get_expl_fmla None f with Exit -> None

let goal_expl_task ~root task =
  let gid = (Task.task_goal task).Decl.pr_name in
  let info =
    let fmla = Task.task_goal_fmla task in
    let res = get_expl_fmla fmla in
    if res <> None || not root then res else check_expl gid.Ident.id_label
  in
  gid, info, task


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

let metas_verified m = m.metas_goal.goal_verified

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
      Mmetas_args.iter
        (fun _ t -> if t.metas_verified then raise Exit)
        g.goal_metas;
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
      | Parent_metas t -> check_metas_proved notify t
  end

and check_transf_proved notify t =
  let b = transf_verified t in
  if t.transf_verified <> b then begin
    t.transf_verified <- b;
    notify (Transf t);
    check_goal_proved notify t.transf_parent
  end


and check_metas_proved notify m =
  let b = metas_verified m in
  if m.metas_verified <> b then begin
    m.metas_verified <- b;
    notify (Metas m);
    check_goal_proved notify m.metas_parent
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
  Opt.map (Filename.concat session.session_dir) pr.proof_edited_as

(* [raw_add_goal parent name expl sum t] adds a goal to the given parent
   DOES NOT record the new goal in its parent, thus this should not be exported
*)
let raw_add_no_task ~(keygen:'a keygen) ~(expanded:bool) parent name expl sum shape =
  let parent_key = match parent with
    | Parent_theory mth -> mth.theory_key
    | Parent_transf mtr -> mtr.transf_key
    | Parent_metas  mms -> mms.metas_key
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
               goal_metas = Mmetas_args.empty;
               goal_verified = false;
               goal_expanded = expanded;
             }
  in
  goal

let raw_add_task ~version ~(keygen:'a keygen) ~(expanded:bool) parent name expl t =
  let parent_key = match parent with
    | Parent_theory mth -> mth.theory_key
    | Parent_transf mtr -> mtr.transf_key
    | Parent_metas  mms -> mms.metas_key
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
               goal_metas = Mmetas_args.empty;
               goal_verified = false;
               goal_expanded = expanded;
             }
  in
  goal


(* [raw_add_transformation g name adds a transformation to the given goal g
   Adds no subgoals, thus this should not be exported
*)
let raw_add_transformation ~(keygen:'a keygen) ~(expanded:bool) g name =
  let parent = g.goal_key in
  let key = keygen ~parent () in
  let tr = { transf_name = name;
             transf_parent = g;
             transf_verified = false;
             transf_key = key;
             transf_goals = [];
             transf_expanded = expanded;
           }
  in
  PHstr.replace g.goal_transformations name tr;
  tr

let raw_add_metas ~(keygen:'a keygen) ~(expanded:bool) g added idpos =
  let parent = g.goal_key in
  let key = keygen ~parent () in
  let ms = { metas_added = added;
             metas_idpos = idpos;
             metas_parent = g;
             metas_verified = false;
             metas_key = key;
             metas_goal = g;
             metas_expanded = expanded;
           }
  in
  g.goal_metas <- Mmetas_args.add added ms g.goal_metas;
  ms

let raw_add_theory ~(keygen:'a keygen) ~(expanded:bool) mfile thname =
  let parent = mfile.file_key in
  let key = keygen ~parent () in
  let mth = { theory_name = thname;
              theory_key = key;
              theory_parent = mfile;
              theory_goals = [];
              theory_verified = false;
              theory_expanded = expanded;
            }
  in
  mth

let raw_add_file ~(keygen:'a keygen) ~(expanded:bool) session f fmt =
  let key = keygen () in
  let mfile = { file_name = f;
                file_key = key;
                file_format = fmt;
                file_theories = [];
                file_verified = false;
                file_expanded = expanded;
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

let int_attribute_def field r def =
  try
    int_of_string (List.assoc field r.Xml.attributes)
  with Not_found | Invalid_argument _ -> def

let int_attribute field r =
  try
    int_of_string (List.assoc field r.Xml.attributes)
  with Not_found | Invalid_argument _ ->
    (** TODO: use real error *)
    eprintf "[Error] missing required attribute '%s' from element '%s'@."
      field r.Xml.name;
    assert false

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
            | "highfailure" -> Call_provers.HighFailure
            | s ->
                eprintf
                  "[Warning] Session.load_result: unexpected status '%s'@." s;
                Call_provers.HighFailure
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
    | "undone" -> Interrupted
    | "unedited" -> Unedited
    | s ->
        eprintf "[Warning] Session.load_result: unexpected element '%s'@." s;
        Interrupted

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
        let expanded = bool_attribute "expanded" g true in
        let mg =
          raw_add_no_task ~keygen ~expanded parent gname expl sum shape
        in
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
            let p = Mstr.find prover old_provers in
            p
          with Not_found ->
            eprintf "[Error] prover not listing in header '%s'@." prover;
            raise (LoadError (a,"prover not listing in header"))
        in
        let res = match a.Xml.elements with
          | [r] -> load_result r
          | [] -> Interrupted
          | _ ->
            eprintf "[Error] Too many result elements@.";
            raise (LoadError (a,"too many result elements"))

        in
        let edit = load_option "edited" a in
        let edit = match edit with None | Some "" -> None | _ -> edit in
        let obsolete = bool_attribute "obsolete" a true in
        let archived = bool_attribute "archived" a false in
        let timelimit = int_attribute_def "timelimit" a 2 in
        let memlimit = int_attribute_def "memlimit" a 0 in
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
        let expanded = bool_attribute "expanded" a true in
        let mtr = raw_add_transformation ~keygen ~expanded mg trname in
        mtr.transf_goals <-
          List.rev
          (List.fold_left
             (load_goal ~old_provers (Parent_transf mtr))
             [] a.Xml.elements);
        (* already done by raw_add_transformation:
           Hashtbl.add mg.transformations trname mtr *)
        (** The attribute "proved" is required but not read *)
        mtr.transf_verified <- transf_verified mtr
    | "metas" -> load_metas ~old_provers mg a;
    | "label" -> ()
    | s ->
        eprintf
          "[Warning] Session.load_proof_or_transf: unexpected element '%s'@."
          s

and load_metas ~old_provers mg a =
  let hts = Hint.create 10 in
  let hls = Hint.create 10 in
  let hpr = Hint.create 10 in
  let idpos, metas_args, goal =
    List.fold_left (fun (idpos, metas, goal) a ->
      match a.Xml.name with
      | "ts_pos" | "ls_pos" | "pr_pos" ->
        let name = string_attribute "name" a in
        let intid = int_attribute "id" a in
        let library, qualid =
          List.fold_left (fun (library,qualid) a ->
            match a.Xml.name with
            | "ip_library" -> string_attribute "name" a::library, qualid
            | "ip_qualid" -> library, string_attribute "name" a::qualid
            | _ ->
              raise (LoadError(a,"Unexpected element")))
            ([],[]) a.Xml.elements in
        let pos = { ip_library = List.rev library;
                    ip_theory = string_attribute "ip_theory" a;
                    ip_qualid = List.rev qualid;
                  } in
        let idpos = begin match a.Xml.name with
          | "ts_pos" ->
            let arity = int_attribute "arity" a in
            let tvs = Util.foldi (fun l _ ->
              (create_tvsymbol (Ident.id_fresh "a"))::l)
              [] 0 arity in
            let ts = Ty.create_tysymbol (Ident.id_fresh name) tvs None in
            Hint.add hts intid ts;
            let idpos_ts = Mts.add ts pos idpos.idpos_ts in
            { idpos with idpos_ts = idpos_ts }
          | "ls_pos" ->
            (** TODO signature? *)
            let ls = Term.create_lsymbol (Ident.id_fresh name) [] None in
            Hint.add hls intid ls;
            let idpos_ls = Mls.add ls pos idpos.idpos_ls in
            { idpos with idpos_ls = idpos_ls }
          | "pr_pos" ->
            let pr = Decl.create_prsymbol (Ident.id_fresh name) in
            Hint.add hpr intid pr;
            let idpos_pr = Mpr.add pr pos idpos.idpos_pr in
            { idpos with idpos_pr = idpos_pr }
          | _ -> assert false
        end in
        (idpos, metas, goal)

      | "meta" -> (idpos, a::metas, goal)
      | "goal"  -> (idpos, metas, a::goal)
      | _ ->
        raise (LoadError(a,"Unexpected element"))
    ) (empty_idpos,[],[]) a.Xml.elements in
  let load_ty a =
    let newtv = Hint.memo 0 (fun _ ->
      Ty.ty_var (create_tvsymbol (Ident.id_fresh "a"))) in
    let rec aux a =
      match a.Xml.name with
      | "ty_var" -> newtv (int_attribute "id" a)
      | "ty_app" ->
        let intid = int_attribute "id" a in
        let ts = Hint.find hts intid in
        Ty.ty_app ts (List.map aux a.Xml.elements)
    | _ ->
      raise (LoadError(a,"Unexpected element")) in
    aux a in
  let load_meta_args a =
    try match a.Xml.name with
    | "meta_arg_ty" -> begin match a.Xml.elements with
      | [ty] -> MAty (load_ty ty)
      | _ -> raise (LoadError (a,"This element must contain only one element"))
    end
    | "meta_arg_str" -> MAstr (string_attribute "val" a)
    | "meta_arg_int" -> MAint (int_attribute "val" a)
    | "meta_arg_ts" ->
      let intid = int_attribute "id" a in
      let ts = Hint.find hts intid in
      MAts ts
    | "meta_arg_ls" ->
      let intid = int_attribute "id" a in
      let ls = Hint.find hls intid in
      MAls ls
    | "meta_arg_pr" ->
      let intid = int_attribute "id" a in
      let pr = Hint.find hpr intid in
      MApr pr
    | _ ->
      raise (LoadError(a,"Unexpected element"))
    with Not_found ->
      raise (LoadError (a,"Unknown id"))
  in
  let load_meta metas_args a =
    let args = List.map load_meta_args a.Xml.elements in
    Mstr.change (function
    | None -> Some (Smeta_args.singleton args)
    | Some s -> Some (Smeta_args.add args s))
      (string_attribute "name" a)
      metas_args
  in
  let metas_args =
    List.fold_left load_meta Mstr.empty metas_args in
  let expanded = bool_attribute "expanded" a true in
  let metas = raw_add_metas ~keygen ~expanded mg metas_args idpos in
  let goal = match goal with
    | [] -> raise (LoadError (a,"No subgoal for this metas"))
    | [goal] -> goal
    | _ ->
      raise (LoadError (a,"Only one goal can appear in a metas element")) in
  metas.metas_goal <-
    List.hd (load_goal ~old_provers (Parent_metas metas) [] goal);
  (* already done by raw_add_transformation:
     Hashtbl.add mg.transformations trname mtr *)
  (** The attribute "proved" is required but not read *)
  metas.metas_verified <- metas_verified metas



let load_theory ~old_provers mf acc th =
  match th.Xml.name with
    | "theory" ->
        let thname = load_ident th in
        let expanded = bool_attribute "expanded" th true in
        let mth = raw_add_theory ~keygen ~expanded mf thname in
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
        let expanded = bool_attribute "expanded" f true in
        let mf = raw_add_file ~keygen ~expanded session fn fmt in
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
        Mstr.add id p old_provers
    | s ->
        eprintf "[Warning] Session.load_file: unexpected element '%s'@." s;
        old_provers

let old_provers = ref Mstr.empty
(* dead code
let get_old_provers () = !old_provers
*)

let load_session session xml =
  match xml.Xml.name with
    | "why3session" ->
      let shape_version = int_attribute_def "shape_version" xml 1 in
      session.session_shape_version <- shape_version;
      dprintf debug "[Info] load_session: shape version is %d@\n" shape_version;
      (** just to keep the old_provers somewhere *)
      old_provers :=
        List.fold_left (load_file session) Mstr.empty xml.Xml.elements;
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

and set_metas_expanded m b =
  m.metas_expanded <- b;
  if not b then set_goal_expanded m.metas_goal b

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
      raw_add_task ~version ~keygen:x_keygen ~expanded:true
        parent name expl task
    in g::acc
  in
  let add_file session f_name fmt file =
    let rfile =
      raw_add_file ~keygen:x_keygen ~expanded:true session f_name fmt
    in
    let add_theory acc thname theory =
      let rtheory =
        raw_add_theory ~keygen:x_keygen ~expanded:true rfile thname
      in
      let parent = Parent_theory rtheory in
      let goals = x_fold_theory (add_goal parent) [] theory in
      rtheory.theory_goals <- List.rev goals;
      rtheory.theory_verified <- theory_verified rtheory;
      rtheory::acc
    in
    let theories = x_fold_file add_theory [] file in
    rfile.file_theories <- List.rev theories;
    rfile
  in
  add_file

(** nice functor *)

(* Claude: "nice" ? but not used anyway
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
*)

(* add a why file from a session *)
(** Read file and sort theories by location *)
let read_file env ?format fn =
  let theories = Env.read_file env ?format fn in
  let ltheories =
    Mstr.fold
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
    ltheories,theories

let add_file_return_theories ~keygen env ?format filename =
  let x_keygen = keygen in
  let x_goal = goal_expl_task ~root:true in
  let x_fold_theory f acc th =
    let tasks = List.rev (Task.split_theory th None None) in
    List.fold_left f acc tasks in
  let x_fold_file f acc ordered_theories =
    List.fold_left (fun acc (_,thname,th) -> f acc thname th) acc
      ordered_theories in
  dprintf debug "[Load] file '%s'@\n" filename;
  let add_file = raw_add_file ~version:env.session.session_shape_version
    ~x_keygen ~x_goal ~x_fold_theory ~x_fold_file in
  let fname = Filename.concat env.session.session_dir filename in
  let ordered_theories,theories = read_file env.env ?format fname in
  let file = add_file env.session filename format ordered_theories in
  check_file_verified notify file;
  file,theories

let add_file ~keygen env ?format filename =
  fst (add_file_return_theories  ~keygen env ?format filename)

let remove_file file =
  let s = file.file_parent in
  PHstr.remove s.session_files file.file_name

(***************************)
(*      transformations    *)
(***************************)

let add_transformation ~keygen env_session transfn g goals =
  let rtransf = raw_add_transformation ~keygen ~expanded:true g transfn in
  let parent = Parent_transf rtransf in
  let i = ref 0 in
  let parent_goal_name = g.goal_name.Ident.id_string in
  let next_subgoal task =
    incr i;
    let gid,expl,_ = goal_expl_task ~root:false task in
    let expl = match expl with
      | None -> string_of_int !i ^ "."
      | Some e -> string_of_int !i ^ ". " ^ e
    in
    let expl = Some expl in
    (* Format.eprintf "parent_goal_name = %s@." parent_goal_name; *)
    let goal_name = parent_goal_name ^ "." ^ string_of_int !i in
    let goal_name = Ident.id_register (Ident.id_derive goal_name gid) in
    (* Format.eprintf "goal_name = %s@." goal_name.Ident.id_string; *)
    goal_name, expl, task
  in
  let add_goal acc g =
    let name,expl,task = next_subgoal g in
    (* Format.eprintf "call raw_add_task with name = %s@." name.Ident.id_string; *)
    let g = raw_add_task ~version:env_session.session.session_shape_version
      ~keygen ~expanded:false parent name expl task
    in
    g::acc
  in
  let goals = List.fold_left add_goal [] goals in
  rtransf.transf_goals <- List.rev goals;
  rtransf.transf_verified <- transf_verified rtransf;
  rtransf


let remove_transformation ?(notify=notify) t =
  let g = t.transf_parent in
  PHstr.remove g.goal_transformations t.transf_name;
  check_goal_proved notify g


let add_registered_transformation ~keygen env_session tr_name g =
  try
    Hstr.find g.goal_transformations tr_name
  with Not_found ->
    let task = goal_task g in
    let subgoals = Trans.apply_transform tr_name env_session.env task in
    add_transformation ~keygen env_session tr_name g subgoals

(****************)
(**    metas    *)
(****************)

(* dead code
let task_nb_decl task =
  Task.task_fold
    (fun n tdecl -> match tdecl.td_node with Decl _ -> n+1 | _ -> n)
    0 task
*)

let pos_of_metas lms =
  let restore_path id =
    let lib,th,qua = Theory.restore_path id in
    { ip_library = lib;
      ip_theory = th;
      ip_qualid = qua
    } in

  let add_ts idpos ts =
    if Mts.mem ts idpos.idpos_ts then idpos else
      {idpos with
        idpos_ts = Mts.add ts (restore_path ts.ts_name) idpos.idpos_ts } in
  let add_ls idpos ls =
    if Mls.mem ls idpos.idpos_ls then idpos else
      {idpos with
        idpos_ls = Mls.add ls (restore_path ls.ls_name) idpos.idpos_ls } in
  let add_pr idpos pr =
    if Mpr.mem pr idpos.idpos_pr then idpos else
      {idpos with
        idpos_pr = Mpr.add pr (restore_path pr.pr_name) idpos.idpos_pr } in

  let look_for_ident idpos = function
    | MAty ty -> ty_s_fold add_ts idpos ty
    | MAts ts -> add_ts idpos ts
    | MAls ls -> add_ls idpos ls
    | MApr pr -> add_pr idpos pr
    | MAstr _ | MAint _ -> idpos  in

  List.fold_left (fun idpos (_,args) ->
    List.fold_left look_for_ident idpos args) empty_idpos lms

let add_registered_metas ~keygen env added0 g =
  let added = List.fold_left (fun ma (s,l) ->
    Mstr.change (function
    | None -> Some (Smeta_args.singleton l)
    | Some std ->
      Some (Smeta_args.add l std)) s ma) Mstr.empty added0 in
  match Mmetas_args.find_opt added g.goal_metas with
  | Some metas -> metas
  | None ->
    let goal,task0 = Task.task_separate_goal (goal_task g) in
    let add_meta task (s,l) =
      let m = Theory.lookup_meta s in
      Task.add_meta task m l in
    (** add before the goal *)
    let task = List.fold_left add_meta task0 added0 in
    let task = add_tdecl task goal in
    let idpos = pos_of_metas added0 in
    let metas = raw_add_metas ~keygen ~expanded:true g added idpos in
    let goal =
      raw_add_task ~version:env.session.session_shape_version
        ~keygen ~expanded:true (Parent_metas metas) g.goal_name g.goal_expl task
    in
    metas.metas_goal <- goal;
    metas

let remove_metas ?(notify=notify) m =
  let g = m.metas_parent in
  g.goal_metas <- Mmetas_args.remove m.metas_added g.goal_metas;
  check_goal_proved notify g


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

let ft_of_th th =
  let fn = Filename.basename th.theory_parent.file_name in
  let fn = try Filename.chop_extension fn with Invalid_argument _ -> fn in
  (fn, th.theory_name.Ident.id_string)

let rec ft_of_goal g =
  match g.goal_parent with
    | Parent_transf tr -> ft_of_goal tr.transf_parent
    | Parent_metas ms  -> ft_of_goal ms.metas_parent
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
  let obsolete = Opt.get_def a.proof_obsolete obsolete in
  let archived = Opt.get_def a.proof_archived archived in
  let timelimit = Opt.get_def a.proof_timelimit timelimit in
  let memlimit = Opt.get_def a.proof_memlimit memlimit in
  let pas = Opt.get_def a.proof_state attempt_status in
  let ngoal = Opt.get_def a.proof_parent goal in
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
        if a.proof_state = Unedited
        then set_proof_state ~notify ~obsolete:a.proof_obsolete
          ~archived:a.proof_archived Interrupted a;
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
  Opt.iter close_in old;
  close_out ch;
  file

let print_attempt_status fmt = function
  | Scheduled | Running ->
    pp_print_string fmt "Running"
  | JustEdited | Interrupted ->
    pp_print_string fmt "Not yet run"
  | Unedited ->
    pp_print_string fmt "Not yet edited"
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

let found_obsolete = ref false

let merge_proof ~keygen obsolete to_goal _ from_proof =
  let obsolete = obsolete || from_proof.proof_obsolete in
  found_obsolete := obsolete || ! found_obsolete;
  ignore
    (add_external_proof ~keygen
       ~obsolete
       ~archived:from_proof.proof_archived
       ~timelimit:from_proof.proof_timelimit
       ~memlimit:from_proof.proof_memlimit
       ~edit:from_proof.proof_edited_as
       to_goal
       from_proof.proof_prover
       from_proof.proof_state)

(* dead code
exception MalformedMetas of ident_path
*)

exception Ts_not_found of tysymbol
exception Ls_not_found of lsymbol
exception Pr_not_found of prsymbol

(** ~theories is the current theory library path empty : [] *)
let rec merge_any_goal ~keygen ~theories env obsolete from_goal to_goal =
  set_goal_expanded to_goal from_goal.goal_expanded;
  PHprover.iter (merge_proof ~keygen obsolete to_goal)
    from_goal.goal_external_proofs;
  PHstr.iter (merge_trans ~keygen ~theories env to_goal)
    from_goal.goal_transformations;
  Mmetas_args.iter (merge_metas ~keygen ~theories env to_goal)
    from_goal.goal_metas


and merge_trans ~keygen ~theories env to_goal _ from_transf =
  try
    let from_transf_name = from_transf.transf_name in
    let to_goal_name = to_goal.goal_name in
    dprintf debug "[Reload] transformation %s for goal %s @\n"
      from_transf_name to_goal_name.Ident.id_string;
    let to_transf =
      try
        add_registered_transformation
          ~keygen env from_transf_name to_goal
      with exn when not (Debug.test_flag Debug.stack_trace) ->
        dprintf debug "[Reload] transformation %s produce an error:%a"
          from_transf_name Exn_printer.exn_printer exn;
        raise Exit
    in
    set_transf_expanded to_transf from_transf.transf_expanded;
    let associated =
      dprintf debug "[Info] associate_subgoals, shape_version = %d@\n"
        env.session.session_shape_version;
      AssoGoals.associate from_transf.transf_goals to_transf.transf_goals in
    List.iter (function
    | (to_goal, Some from_goal, obsolete) ->
      merge_any_goal ~keygen ~theories env obsolete  from_goal to_goal
    | (_, None, _) -> ()
    ) associated
  with Exit -> ()


(** convert the ident from the olf task to the ident at the same
    position in the new task *)
and merge_metas_aux ~keygen ~theories env to_goal _ from_metas =
  (** Find in the new task the new symbol (ts,ls,pr) *)
  (** We order the position bottom up and find the ident as we go
      through the task *)
  dprintf debug "[Reload] metas for goal %s@\n"
    to_goal.goal_name.Ident.id_string;

  (** hashtbl that will contain the conversion *)
  let hts = Hts.create 4 in
  let hls = Hls.create 4 in
  let hpr = Hpr.create 10 in
  let obsolete = ref false in

  (** TODO: replace that when retrieve theory will give the formats *)
  let rec read_theory ip = function
    | [] -> raise (Env.LibFileNotFound ip.ip_library)
    | format::formats ->
      try
        Env.read_theory ~format env.env
          ip.ip_library ip.ip_theory
      with Env.LibFileNotFound _ | Env.TheoryNotFound _ ->
        read_theory ip formats
  in
  let read_theory ip =
    if ip.ip_library = [] then Mstr.find ip.ip_theory theories
    else read_theory ip ["why";"whyml"] in

  let to_idpos_ts = Mts.fold_left (fun idpos_ts from_ts ip ->
    try
      let th = read_theory ip in
      let to_ts = ns_find_ts th.th_export ip.ip_qualid in
      Hts.add hts from_ts to_ts;
      Mts.add to_ts ip idpos_ts
    with e ->
      dprintf debug "[merge metas]@ can't@ find@ ident@ %a@ because@ %a@\n"
        print_ident_path ip Exn_printer.exn_printer e;
      idpos_ts
  ) Mts.empty from_metas.metas_idpos.idpos_ts in
  let to_idpos_ls = Mls.fold_left (fun idpos_ls from_ls ip ->
    try
      let th = read_theory ip in
      let to_ls = ns_find_ls th.th_export ip.ip_qualid in
      Hls.add hls from_ls to_ls;
      Mls.add to_ls ip idpos_ls
    with e ->
      dprintf debug "[merge metas]@ can't@ find@ ident@ %a@ because@ %a@\n"
        print_ident_path ip Exn_printer.exn_printer e;
      idpos_ls
  ) Mls.empty from_metas.metas_idpos.idpos_ls in
  let to_idpos_pr = Mpr.fold_left (fun idpos_pr from_pr ip ->
    try
      let th = read_theory ip in
      let to_pr = ns_find_pr th.th_export ip.ip_qualid in
      Hpr.add hpr from_pr to_pr;
      Mpr.add to_pr ip idpos_pr
    with e ->
      dprintf debug "[merge metas]@ can't@ find@ ident@ %a@ because@ %a"
        print_ident_path ip Exn_printer.exn_printer e;
      idpos_pr
  ) Mpr.empty from_metas.metas_idpos.idpos_pr in

  let to_idpos = {idpos_ts = to_idpos_ts;
                  idpos_ls = to_idpos_ls;
                  idpos_pr = to_idpos_pr;
                 } in


  let print_meta fmt (meta_name,meta_args) =
    fprintf fmt "%s %a"
      meta_name
      (Pp.print_list Pp.space Pretty.print_meta_arg) meta_args in

  (** Now convert the metas to the new symbol *)
  let add_meta ((metas,task) as acc) meta_name meta_args =
    let conv_ts ts = Hts.find_exn hts (Ts_not_found ts) ts in
    let conv_ls ls = Hls.find_exn hls (Ls_not_found ls) ls in
    let conv_pr pr = Hpr.find_exn hpr (Pr_not_found pr) pr in
    let map = function
      | MAty ty -> MAty (Ty.ty_s_map conv_ts ty)
      | MAts ts -> MAts (conv_ts ts)
      | MAls ls -> MAls (conv_ls ls)
      | MApr pr -> MApr (conv_pr pr)
      | (MAstr _ | MAint _) as m -> m
    in
    try
      let meta = Theory.lookup_meta meta_name in
      let smeta_args,task = Smeta_args.fold_left
        (fun ((smeta_args,task) as acc) meta_args ->
          try
            let meta_args = List.map map meta_args in
            Smeta_args.add meta_args smeta_args,
            Task.add_meta task meta meta_args
          with
          | Ts_not_found ts ->
            obsolete := true;
            let pos = Mts.find ts from_metas.metas_idpos.idpos_ts in
            dprintf debug
              "Remove the meta %a during merge because \
               the type symbol %a can't be found@\n"
              print_meta (meta_name,meta_args)
              print_ident_path pos;
            acc
          | Ls_not_found ls ->
            obsolete := true;
            let pos = Mls.find ls from_metas.metas_idpos.idpos_ls in
            dprintf debug
              "Remove the meta %a during merge because \
               the logic symbol %a can't be found@\n"
              print_meta (meta_name,meta_args)
              print_ident_path pos;
            acc
          | Pr_not_found pr ->
            obsolete := true;
            let pos = Mpr.find pr from_metas.metas_idpos.idpos_pr in
            dprintf debug
              "Remove the meta %a during merge because \
               the proposition symbol %a can't be found@\n"
              print_meta (meta_name,meta_args)
              print_ident_path pos;
            acc
        )
        (Smeta_args.empty,task) meta_args in
      (Mstr.add meta_name smeta_args metas,task)
    with
    | Theory.UnknownMeta s ->
      dprintf debug "Remove a meta during merge: meta %s unknown@\n" s;
      acc
  in
  let goal,task = Task.task_separate_goal (goal_task to_goal) in
  let metas,task =
    Mstr.fold_left add_meta (Mstr.empty,task) from_metas.metas_added
  in
  let task = Task.add_tdecl task goal in
  let to_metas =
    raw_add_metas ~keygen ~expanded:from_metas.metas_expanded
      to_goal metas to_idpos
  in
  let to_goal =
    raw_add_task ~version:env.session.session_shape_version
      ~keygen (Parent_metas to_metas) ~expanded:true
      to_goal.goal_name to_goal.goal_expl task
  in
  to_metas.metas_goal <- to_goal;
  dprintf debug "[Reload] metas done@\n";
  merge_any_goal ~keygen ~theories env !obsolete from_metas.metas_goal to_goal

and merge_metas ~keygen ~theories env to_goal s from_metas =
  try
    merge_metas_aux ~keygen ~theories env to_goal s from_metas
  with exn ->
    dprintf debug "[merge metas] error %a during merge, metas removed@\n"
      Exn_printer.exn_printer exn

exception OutdatedSession

let merge_theory ~keygen ~theories env ~allow_obsolete from_th to_th =
  set_theory_expanded to_th from_th.theory_expanded;
  let from_goals = List.fold_left
    (fun from_goals g ->
      Mstr.add g.goal_name.Ident.id_string g from_goals)
    Mstr.empty from_th.theory_goals
  in
  List.iter
    (fun to_goal ->
      try
        let from_goal =
          Mstr.find to_goal.goal_name.Ident.id_string from_goals in
        let goal_obsolete = to_goal.goal_checksum <> from_goal.goal_checksum in
        if goal_obsolete then
          begin
            dprintf debug "[Reload] Goal %s.%s has changed@\n"
              to_th.theory_name.Ident.id_string
              to_goal.goal_name.Ident.id_string;
            if not allow_obsolete then raise OutdatedSession;
            found_obsolete := true;
          end;
        merge_any_goal ~keygen ~theories env goal_obsolete from_goal to_goal
      with
        | Not_found when allow_obsolete -> ()
        | Not_found -> raise OutdatedSession
    ) to_th.theory_goals

let merge_file ~keygen ~theories env ~allow_obsolete from_f to_f =
  dprintf debug "[Info] merge_file, shape_version = %d@\n"
    env.session.session_shape_version;
  set_file_expanded to_f from_f.file_expanded;
  let from_theories = List.fold_left
    (fun acc t -> Mstr.add t.theory_name.Ident.id_string t acc)
    Mstr.empty from_f.file_theories
  in
  List.iter
    (fun to_th ->
      try
        let from_th =
          let name = to_th.theory_name.Ident.id_string in
          try Mstr.find name from_theories
          (* TODO: remove this later when all sessions are updated *)
          with Not_found -> Mstr.find ("WP "^name) from_theories
        in
        merge_theory ~keygen ~theories env ~allow_obsolete from_th to_th
      with
        | Not_found when allow_obsolete -> ()
        | Not_found -> raise OutdatedSession
    )
    to_f.file_theories;
  dprintf debug "[Info] merge_file, done@\n"

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
  found_obsolete := false;
  PHstr.iter (fun _ old_file ->
    dprintf debug "[Load] file '%s'@\n" old_file.file_name;
    let new_file,theories = add_file_return_theories
      ~keygen new_env_session
      ?format:old_file.file_format old_file.file_name
    in
    merge_file ~keygen ~theories
      new_env_session ~allow_obsolete old_file new_file)
    old_session.session_files;
  dprintf debug "[Info] update_session: done@\n";
  let obsolete =
    if old_session.session_shape_version <> Termcode.current_shape_version
    then
      begin
        dprintf debug "[Info] update_session: recompute shapes@\n";
        recompute_all_shapes new_session;
        true
      end
    else
      !found_obsolete
  in
  assert (new_env_session.session.session_shape_version
          = Termcode.current_shape_version);
  new_env_session, obsolete


(** Copy/Paste *)
let rec copy_goal parent from_g =
  let to_g = { from_g with
               goal_parent = parent;
               goal_external_proofs =
      PHprover.create (PHprover.length from_g.goal_external_proofs);
               goal_transformations =
      PHstr.create (PHstr.length from_g.goal_transformations);
               goal_metas = Mmetas_args.empty;
             } in
  PHprover.iter (fun k p -> PHprover.add to_g.goal_external_proofs
    k (copy_proof to_g p)) from_g.goal_external_proofs;
  PHstr.iter (fun k t -> PHstr.add to_g.goal_transformations
    k (copy_transf to_g t)) from_g.goal_transformations;
  to_g.goal_metas <- Mmetas_args.map
    (fun m -> copy_metas to_g m) from_g.goal_metas;
  to_g

and copy_proof to_goal from_pa =
  { from_pa with proof_parent = to_goal}

and copy_transf to_goal from_transf =
  let to_transf = { from_transf with
    transf_parent = to_goal;
    transf_goals = []
  } in
  to_transf.transf_goals <-
    List.map (copy_goal (Parent_transf from_transf))
                from_transf.transf_goals;
  to_transf

and copy_metas to_goal from_metas =
  let to_metas = { from_metas with
    metas_goal = to_goal;
  } in
  to_metas.metas_goal <- copy_goal (Parent_metas to_metas)
    from_metas.metas_goal;
  to_metas

let copy_proof  from_p = copy_proof  from_p.proof_parent  from_p
let copy_transf from_t = copy_transf from_t.transf_parent from_t
let copy_metas  from_m = copy_metas  from_m.metas_parent  from_m

exception Paste_error

let rec add_goal_to_parent ~keygen env from_goal to_goal =
  set_goal_expanded to_goal from_goal.goal_expanded;
  PHprover.iter (fun _ pa -> ignore (add_proof_to_goal ~keygen env to_goal pa))
    from_goal.goal_external_proofs;
  PHstr.iter (fun _ t -> ignore (add_transf_to_goal ~keygen env to_goal t))
    from_goal.goal_transformations;
  Mmetas_args.iter (fun _ m -> ignore (add_metas_to_goal ~keygen env to_goal m))
    from_goal.goal_metas



(** This function is the main difference with merge_metas_aux.
    It use directly the metas doesn't convert them.
 *)
and add_metas_to_goal ~keygen env to_goal from_metas =
  let to_metas =
    raw_add_metas ~keygen ~expanded:from_metas.metas_expanded to_goal
      from_metas.metas_added from_metas.metas_idpos
  in
  let goal,task0 = Task.task_separate_goal (goal_task to_goal) in
  (** add before the goal *)
  let task =
    try
      Mstr.fold_left
        (fun task name s ->
          let m = Theory.lookup_meta name in
          Smeta_args.fold_left
            (fun task l -> Task.add_meta task m l) (** TODO: try with *)
            task s)
        task0 from_metas.metas_added
    with exn ->
      dprintf debug "[Paste] addition of metas produces an error:%a"
        Exn_printer.exn_printer exn;
      raise Paste_error  in
  let task = add_tdecl task goal in
  let to_goal =
    raw_add_task ~version:env.session.session_shape_version
      ~keygen ~expanded:true (Parent_metas to_metas)
      from_metas.metas_goal.goal_name
      from_metas.metas_goal.goal_expl task
  in
  to_metas.metas_goal <- to_goal;
  add_goal_to_parent ~keygen env from_metas.metas_goal to_goal;
  to_metas

and add_proof_to_goal ~keygen env to_goal from_proof_attempt =
  copy_external_proof ~keygen ~obsolete:true ~env_session:env ~goal:to_goal
    from_proof_attempt

and add_transf_to_goal ~keygen env to_goal from_transf =
  let from_transf_name = from_transf.transf_name in
  let to_goal_name = to_goal.goal_name in
  dprintf debug "[Paste] transformation %s for goal %s @\n"
    from_transf_name to_goal_name.Ident.id_string;
  let to_transf =
    try
      add_registered_transformation
        ~keygen env from_transf_name to_goal
    with exn when not (Debug.test_flag Debug.stack_trace) ->
      dprintf debug "[Paste] transformation %s produce an error:%a"
        from_transf_name Exn_printer.exn_printer exn;
      raise Paste_error
  in
  let associated =
    dprintf debug "[Info] associate_subgoals, shape_version = %d@\n"
      env.session.session_shape_version;
    AssoGoals.associate from_transf.transf_goals to_transf.transf_goals in
  List.iter (function
  | (to_goal, Some from_goal, _obsolete) ->
    add_goal_to_parent ~keygen env from_goal to_goal
  | (_, None, _) -> ()
  ) associated;
  to_transf


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
  | Metas  ms -> ms.metas_key

let () = Exn_printer.register
  (fun fmt exn ->
    match exn with
      | NoTask ->
        Format.fprintf fmt
          "A goal doesn't contain a task but here it needs one"
      | OutdatedSession ->
        Format.fprintf fmt
          "The session@ is@ outdated@ (not@ in@ sync@ with@ the@ current@ \
           file).@ In@ this@ configuration@ it@ is@ forbidden."
      | _ -> raise exn)


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3ide.byte"
End:
*)
