(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

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
type 'a hide = 'a option

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

(* dead code

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

*)

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
    (* These hash are in fact tag *)
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

type 'a goal =
  { mutable goal_key  : 'a;
    goal_name : Ident.ident;
    goal_number : int;
    mutable goal_expl : string option;
    goal_parent : 'a goal_parent;
    mutable goal_checksum : Tc.checksum option;
    mutable goal_shape : Tc.shape;
    mutable goal_verified : float option;
    mutable goal_task: task_option;
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
    mutable proof_limit : Call_provers.resource_limit;
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
    mutable metas_verified : float option;
    mutable metas_goal : 'a goal;
    (** Not mutated after the creation *)
    mutable metas_expanded : bool;
  }

and 'a transf =
    { mutable transf_key : 'a;
      transf_name : string;
      (** Why3 tranformation name *)
      transf_parent : 'a goal;
      mutable transf_verified : float option;
      mutable transf_goals : 'a goal list;
      (** Not mutated after the creation of the session *)
      mutable transf_expanded : bool;
      mutable transf_detached : 'a detached option;
    }

and 'a detached =
    { detached_goals: 'a goal list; }

and 'a theory =
    { mutable theory_key : 'a;
      theory_name : Ident.ident;
      theory_parent : 'a file;
      mutable theory_checksum : Termcode.checksum option;
      mutable theory_goals : 'a goal list;
      mutable theory_verified : float option;
      mutable theory_expanded : bool;
      mutable theory_task : Theory.theory hide;
      mutable theory_detached : 'a detached option;
    }

and 'a file =
    { mutable file_key : 'a;
      file_name : string;
      file_format : string option;
      file_parent : 'a session;
      mutable file_theories: 'a theory list;
      (** Not mutated after the creation *)
      mutable file_verified : float option;
      mutable file_expanded : bool;
      mutable file_for_recovery : Theory.theory Mstr.t hide;
    }

and 'a session =
    { session_files : 'a file PHstr.t;
      mutable session_shape_version : int;
      session_prover_ids : int PHprover.t;
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
      mutable files : Theory.theory Stdlib.Mstr.t Stdlib.Mstr.t;
      session : 'a session}

let goal_key g = g.goal_key
let goal_name g = g.goal_name
let goal_verified g = g.goal_verified
let goal_external_proofs g = g.goal_external_proofs
let goal_transformations g = g.goal_transformations
let goal_metas g = g.goal_metas
let goal_expanded g = g.goal_expanded
let goal_parent g = g.goal_parent

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
  if not (Opt.inhabited g.goal_verified && unproved_only) then
    let r = ref true in
    PHstr.iter
      (fun _ t -> r := false;
        List.iter (goal_iter_leaf_goal ~unproved_only f) t.transf_goals)
      g.goal_transformations;
    if !r then f g

let rec fold_all_sub_goals_of_goal f acc g =
  let acc =
    PHstr.fold
      (fun _ tr acc ->
       List.fold_left (fold_all_sub_goals_of_goal f) acc tr.transf_goals)
      g.goal_transformations acc
  in
  let acc =
    Mmetas_args.fold
      (fun _ m acc ->
       fold_all_sub_goals_of_goal f acc m.metas_goal)
      g.goal_metas acc
  in
  f acc g

let fold_all_sub_goals_of_theory f acc th =
  List.fold_left (fold_all_sub_goals_of_goal f) acc th.theory_goals


(** iterators not reccursive *)
let iter_goal fp ft fm g =
  PHprover.iter (fun _ a -> fp a) g.goal_external_proofs;
  PHstr.iter (fun _ t -> ft t) g.goal_transformations;
  Mmetas_args.iter (fun _ t -> fm t) g.goal_metas

let iter_transf f t =
  List.iter (fun g -> f g) t.transf_goals

let iter_metas f t = f t.metas_goal

let iter_theory f t =
  List.iter f t.theory_goals

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
          if Opt.inhabited f.file_verified
          then f.file_name
          else f.file_name^"?"
        | Theory th ->
          if Opt.inhabited th.theory_verified
          then th.theory_name.Ident.id_string
          else th.theory_name.Ident.id_string^"?"
        | Goal g ->
          if Opt.inhabited g.goal_verified
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
          if Opt.inhabited tr.transf_verified
          then tr.transf_name
          else tr.transf_name^"?"
        | Metas metas ->
          if Opt.inhabited metas.metas_verified
          then "metas..."
          else "metas..."^"?"
      in
      let l = ref [] in
      iter (fun a -> l := (Any a)::!l) t;
      s,!l
    | Session s ->
      let l = ref [] in
      session_iter (fun a -> l := (Any a)::!l) s;
      (* Previously "" was `Filename.basename s.session_dir` but
         the tree depend on the filename given in input and not the content
         which is not easy for diffing
      *)
      "",!l

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
    session_prover_ids = PHprover.create 7;
    session_dir   = dir;
  }

let create_session ?shape_version project_dir =
  if not (Sys.file_exists project_dir) then
    begin
      Debug.dprintf debug
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

let get_used_provers_with_stats session =
  let prover_table = PHprover.create 5 in
  session_iter_proof_attempt
    (fun pa ->
      (* record mostly used pa.proof_timelimit pa.proof_memlimit *)
      let prover = pa.proof_prover in
      let timelimits,steplimits,memlimits =
        try PHprover.find prover_table prover
        with Not_found ->
          let x = (Hashtbl.create 5,Hashtbl.create 5,Hashtbl.create 5) in
          PHprover.add prover_table prover x;
          x
      in
      let lim_time = pa.proof_limit.Call_provers.limit_time in
      let lim_mem = pa.proof_limit.Call_provers.limit_mem in
      let lim_steps = pa.proof_limit.Call_provers.limit_steps in
      let tf = try Hashtbl.find timelimits lim_time with Not_found -> 0 in
      let sf = try Hashtbl.find steplimits lim_steps with Not_found -> 0 in
      let mf = try Hashtbl.find memlimits lim_mem with Not_found -> 0 in
      Hashtbl.replace timelimits lim_time (tf+1);
      Hashtbl.replace steplimits lim_steps (sf+1);
      Hashtbl.replace memlimits lim_mem (mf+1))
    session;
  prover_table

exception NoTask

let goal_task g = Opt.get_exn NoTask g.goal_task
let goal_task_option g = g.goal_task

let goal_expl_lazy g =
  match g.goal_expl with
  | Some s -> s
  | None ->
     match g.goal_task with
     | Some t ->
        let _name,expl,_task = Termcode.goal_expl_task ~root:false t in
        g.goal_expl <- Some expl; expl
     | None -> ""

let goal_user_name g =
  let s = goal_expl_lazy g in
  if s <> "" then string_of_int g.goal_number ^ ". " ^ s else
    try let _,_,l = restore_path g.goal_name in
        String.concat "." l
    with Not_found -> g.goal_name.Ident.id_string

(************************)
(* saving state on disk *)
(************************)
open Format

let db_filename = "why3session.xml"
let shape_filename = "why3shapes"
let compressed_shape_filename = "why3shapes.gz"
let session_dir_for_save = ref "."

let save_string = Pp.html_string

let opt pr lab fmt = function
  | None -> ()
  | Some s -> fprintf fmt "@ %s=\"%a\"" lab pr s

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
    | Unedited ->
        fprintf fmt "<unedited/>"
    | Scheduled | Running | Interrupted | JustEdited ->
        fprintf fmt "<undone/>"
    | InternalFailure msg ->
        fprintf fmt "<internalfailure@ reason=\"%a\"/>"
          save_string (Printexc.to_string msg)
    | Done r -> save_result fmt r


let save_bool_def name def fmt b =
  if b <> def then fprintf fmt "@ %s=\"%b\"" name b

let save_int_def name def fmt n =
  if n <> def then fprintf fmt "@ %s=\"%d\"" name n

let opt_string = opt save_string

let save_proof_attempt fmt ((id,tl,sl,ml),a) =
  fprintf fmt
    "@\n@[<h><proof@ prover=\"%i\"%a%a%a%a%a%a>"
    id
    (save_int_def "timelimit" tl) (a.proof_limit.Call_provers.limit_time)
    (save_int_def "steplimit" sl) (a.proof_limit.Call_provers.limit_steps)
    (save_int_def "memlimit" ml) (a.proof_limit.Call_provers.limit_mem)
    (opt_string "edited") a.proof_edited_as
    (save_bool_def "obsolete" false) a.proof_obsolete
    (save_bool_def "archived" false) a.proof_archived;
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

module Compr = Compress.Compress_z

type save_ctxt = {
  prover_ids : int PHprover.t;
  provers : (int * int * int * int) Mprover.t;
  ch_shapes : Compr.out_channel;
}

let save_checksum fmt s =
  fprintf fmt "%s" (Tc.string_of_checksum s)

let rec save_goal ctxt fmt g =
  let shape = Tc.string_of_shape g.goal_shape in
  assert (shape <> "");
  fprintf fmt
    "@\n@[<v 0>@[<h><goal@ %a%a%a>@]"
    save_ident g.goal_name
    (opt_string "expl") g.goal_expl
    (save_bool_def "expanded" false) g.goal_expanded;
  let sum =
    match g.goal_checksum with
    | None -> assert false
    | Some s -> Tc.string_of_checksum s
  in
  Compr.output_string ctxt.ch_shapes sum;
  Compr.output_char ctxt.ch_shapes ' ';
  Compr.output_string ctxt.ch_shapes shape;
  Compr.output_char ctxt.ch_shapes '\n';
(*
  Ident.Slab.iter (save_label fmt) g.goal_name.Ident.id_label;
*)
  let l = PHprover.fold
    (fun _ a acc -> (Mprover.find a.proof_prover ctxt.provers, a) :: acc)
    g.goal_external_proofs [] in
  let l = List.sort (fun ((i1,_,_,_),_) ((i2,_,_,_),_) -> compare i1 i2) l in
  List.iter (save_proof_attempt fmt) l;
  let l = PHstr.fold (fun _ t acc -> t :: acc) g.goal_transformations [] in
  let l = List.sort (fun t1 t2 -> compare t1.transf_name t2.transf_name) l in
  List.iter (save_trans ctxt fmt) l;
  Mmetas_args.iter (save_metas ctxt fmt) g.goal_metas;
  fprintf fmt "@]@\n</goal>"

and save_trans ctxt fmt t =
  fprintf fmt "@\n@[<hov 1>@[<h><transf@ name=\"%a\"%a>@]"
    save_string t.transf_name
    (save_bool_def "expanded" false) t.transf_expanded;
  List.iter (save_goal ctxt fmt) t.transf_goals;
  fprintf fmt "@]@\n</transf>"

and save_metas ctxt fmt _ m =
  fprintf fmt "@\n@[<hov 1><metas%a>"
    (save_bool_def "expanded" false) m.metas_expanded;
  let save_pos fmt pos =
    fprintf fmt "ip_theory=\"%a\">" save_string pos.ip_theory;
    List.iter (fprintf fmt "@\n@[<hov 1><ip_library@ name=\"%a\"/>@]" save_string)
      pos.ip_library;
    List.iter (fprintf fmt "@\n@[<hov 1><ip_qualid@ name=\"%a\"/>@]" save_string)
      pos.ip_qualid;
  in
  let save_ts_pos fmt ts pos =
    fprintf fmt "@\n@[<hov 1><ts_pos@ name=\"%a\"@ arity=\"%i\"@ \
    id=\"%i\"@ %a@]@\n</ts_pos>"
      save_string ts.ts_name.id_string (List.length ts.ts_args)
      (ts_hash ts) save_pos pos in
  let save_ls_pos fmt ls pos =
    (* TODO: add the signature? *)
    fprintf fmt "@\n@[<hov 1><ls_pos@ name=\"%a\"@ id=\"%i\"@ %a@]@\n</ls_pos>"
      save_string ls.ls_name.id_string
      (ls_hash ls) save_pos pos
  in
  let save_pr_pos fmt pr pos =
    fprintf fmt "@\n@[<hov 1><pr_pos@ name=\"%a\"@ id=\"%i\"@ %a@]@\n</pr_pos>"
      save_string pr.pr_name.id_string
      (pr_hash pr) save_pos pos
  in
  Mts.iter (save_ts_pos fmt) m.metas_idpos.idpos_ts;
  Mls.iter (save_ls_pos fmt) m.metas_idpos.idpos_ls;
  Mpr.iter (save_pr_pos fmt) m.metas_idpos.idpos_pr;
  Mstr.iter (fun s smeta_args ->
    Smeta_args.iter (save_meta_args fmt s) smeta_args) m.metas_added;
  save_goal ctxt fmt m.metas_goal;
  fprintf fmt "@]@\n</metas>"

and save_meta_args fmt s l =
  fprintf fmt "@\n@[<hov 1><meta@ name=\"%a\">" save_string s;
  let save_meta_arg fmt = function
    | MAty ty -> fprintf fmt "@\n@[<hov 1><meta_arg_ty/>";
      save_ty fmt ty;
      fprintf fmt "@]@\n</meta_arg_ty>"
    | MAts ts ->
      fprintf fmt "@\n@[<hov 1><meta_arg_ts@ id=\"%i\"/>@]" (ts_hash ts)
    | MAls ls ->
      fprintf fmt "@\n@[<hov 1><meta_arg_ls@ id=\"%i\"/>@]" (ls_hash ls)
    | MApr pr ->
      fprintf fmt "@\n@[<hov 1><meta_arg_pr@ id=\"%i\"/>@]" (pr_hash pr)
    | MAstr s ->
      fprintf fmt "@\n@[<hov 1><meta_arg_str@ val=\"%s\"/>@]" s
    | MAint i ->
      fprintf fmt "@\n@[<hov 1><meta_arg_int@ val=\"%i\"/>@]" i
  in
  List.iter (save_meta_arg fmt) l;
  fprintf fmt "@]@\n</meta>"

and save_ty fmt ty =
  match ty.ty_node with
  | Tyvar tv ->
    fprintf fmt "@\n@[<hov 1><ty_var@ id=\"%i\"/>@]" (tv_hash tv)
  | Tyapp (ts,l) ->
    fprintf fmt "@\n@[<hov 1><ty_app@ id=\"%i\"/>" (ts_hash ts);
    List.iter (save_ty fmt) l;
    fprintf fmt "@]@\n</ty_app>"

module CombinedTheoryChecksum = struct

 let b = Buffer.create 1024

 let f () g =
    match g.goal_checksum with
    | None -> assert false
    | Some c -> Buffer.add_string b (Tc.string_of_checksum c)

 let compute th =
   let () = fold_all_sub_goals_of_theory f () th in
   let c = Tc.buffer_checksum b in
   Buffer.clear b; c

end

let save_theory ctxt fmt t =
  let c = CombinedTheoryChecksum.compute t in
  t.theory_checksum <- Some c;
  fprintf fmt
    "@\n@[<v 1>@[<h><theory@ %a%a%a>@]"
    save_ident t.theory_name
    (opt save_checksum "sum") t.theory_checksum
    (save_bool_def "expanded" false) t.theory_expanded;
  List.iter (save_goal ctxt fmt) t.theory_goals;
  fprintf fmt "@]@\n</theory>"

let save_file ctxt fmt _ f =
  fprintf fmt
    "@\n@[<v 0>@[<h><file@ name=\"%a\"%a%a>@]"
    save_string f.file_name (opt_string "format")
    f.file_format (save_bool_def "expanded" false) f.file_expanded;
  List.iter (save_theory ctxt fmt) f.file_theories;
  fprintf fmt "@]@\n</file>"

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


let save_prover fmt id (p,mostfrequent_timelimit,mostfrequent_steplimit,mostfrequent_memlimit) =
  let steplimit =
    if mostfrequent_steplimit < 0 then None else Some mostfrequent_steplimit
  in
  fprintf fmt "@\n@[<h><prover@ id=\"%i\"@ name=\"%a\"@ \
               version=\"%a\"%a@ timelimit=\"%d\"%a@ memlimit=\"%d\"/>@]"
    id save_string p.C.prover_name save_string p.C.prover_version
    (fun fmt s -> if s <> "" then fprintf fmt "@ alternative=\"%a\""
        save_string s)
    p.C.prover_altern
    mostfrequent_timelimit
    (opt pp_print_int "steplimit") steplimit
    mostfrequent_memlimit

let save fname shfname _config session =
  let ch = open_out fname in
  let chsh = Compr.open_out shfname in
  let fmt = formatter_of_out_channel ch in
  fprintf fmt "<?xml version=\"1.0\" encoding=\"UTF-8\"?>@\n";
  fprintf fmt "<!DOCTYPE why3session PUBLIC \"-//Why3//proof session v5//EN\"@ \"http://why3.lri.fr/why3session.dtd\">@\n";
  (*
    let rel_file = Sysutil.relativize_filename !session_dir_for_save fname in
    fprintf fmt "@[<hov 1><why3session@ name=\"%a\" shape_version=\"%d\">"
    save_string rel_file session.session_shape_version;
  *)
  fprintf fmt "@[<v 0><why3session shape_version=\"%d\">"
    session.session_shape_version;
(*
  Tc.reset_dict ();
*)
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
  PHstr.iter (save_file ctxt fmt) session.session_files;
  fprintf fmt "@]@\n</why3session>";
  fprintf fmt "@.";
  close_out ch;
  Compr.close_out chsh

let save_session config session =
  let f = Filename.concat session.session_dir db_filename in
  Sysutil.backup_file f;
  let fs = Filename.concat session.session_dir shape_filename in
  Sysutil.backup_file fs;
  let fz = Filename.concat session.session_dir compressed_shape_filename in
  Sysutil.backup_file fz;
  session_dir_for_save := session.session_dir;
  let fs = if Compress.compression_supported then fz else fs in
  save f fs config session

(*****************************)
(*   update verified field   *)
(*****************************)
type 'a notify = 'a any -> unit
let notify : 'a notify = fun _ -> ()

let compute_verified get l =
  List.fold_left (fun acc t ->
    match acc,get t with
    | Some x, Some y -> Some (x +. y)
    | _ -> None) (Some 0.0) l

let file_verified f =
  compute_verified (fun t -> t.theory_verified) f.file_theories

let theory_verified t =
  compute_verified (fun g -> g.goal_verified) t.theory_goals

let transf_verified t =
  compute_verified (fun g -> g.goal_verified) t.transf_goals

let metas_verified m = m.metas_goal.goal_verified

let proof_verified a =
  if a.proof_obsolete then None else
    match a.proof_state with
      | Done { Call_provers.pr_answer = Call_provers.Valid;
               Call_provers.pr_time = t } -> Some t
      | _ -> None

let check_goal_verified g =
  let acc = ref None in
  let accumulate v =
    match v with
    | None -> ()
    | Some t ->
      match !acc with
      | Some x -> acc := Some (x +. t)
      | None -> acc := v
  in
  PHprover.iter
    (fun _ a -> accumulate (proof_verified a))
    g.goal_external_proofs;
  PHstr.iter
    (fun _ t -> accumulate t.transf_verified)
    g.goal_transformations;
  Mmetas_args.iter
      (fun _ t -> accumulate t.metas_verified)
    g.goal_metas;
  !acc

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
  let b = check_goal_verified g in
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
    ~archived ~limit ~edit (g:'a goal) p result =
  assert (edit <> Some "");
  let key = keygen ~parent:g.goal_key () in
  let a = { proof_prover = p;
            proof_parent = g;
            proof_key = key;
            proof_obsolete = obsolete;
            proof_archived = archived;
            proof_state = result;
            proof_limit = limit;
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

let set_timelimit timelimit a =
  a.proof_limit <-
    { a.proof_limit with Call_provers.limit_time = timelimit}
let set_memlimit memlimit a =
  a.proof_limit <-
    { a.proof_limit with Call_provers.limit_mem = memlimit}

let set_obsolete ?(notify=notify) a =
  a.proof_obsolete <- true;
  notify (Proof_attempt a);
  check_goal_proved notify a.proof_parent

let set_non_obsolete a =
  a.proof_obsolete <- false;
  notify (Proof_attempt a);
  check_goal_proved notify a.proof_parent

let set_archived a b = a.proof_archived <- b

let get_edited_as_abs session pr =
  Opt.map (Filename.concat session.session_dir) pr.proof_edited_as

(* [raw_add_goal parent name expl sum t] adds a goal to the given parent
   DOES NOT record the new goal in its parent, thus this should not be exported
*)
let raw_add_no_task ~(keygen:'a keygen) ~(expanded:bool)
                    parent name number expl sum shape =
  let parent_key = match parent with
    | Parent_theory mth -> mth.theory_key
    | Parent_transf mtr -> mtr.transf_key
    | Parent_metas  mms -> mms.metas_key
  in
  let key = keygen ~parent:parent_key () in
  let goal = { goal_name = name;
               goal_number = number;
               goal_expl = expl;
               goal_parent = parent;
               goal_task = None ;
               goal_checksum = sum;
               goal_shape = shape;
               goal_key = key;
               goal_external_proofs = PHprover.create 7;
               goal_transformations = PHstr.create 3;
               goal_metas = Mmetas_args.empty;
               goal_verified = None;
               goal_expanded = expanded;
             }
  in
  goal

let raw_add_task ~version ~(keygen:'a keygen) ~(expanded:bool)
                 parent name number expl t =
  let parent_key = match parent with
    | Parent_theory mth -> mth.theory_key
    | Parent_transf mtr -> mtr.transf_key
    | Parent_metas  mms -> mms.metas_key
  in
  let key = keygen ~parent:parent_key () in
  let sum = Some (Termcode.task_checksum ~version t) in
  (* let shape = Termcode.t_shape_buf ~version (Task.task_goal_fmla t) in *)
  let shape = Termcode.t_shape_task ~version ~expl t in
  let goal = { goal_name = name;
               goal_number = number;
               goal_expl = Some expl;
               goal_parent = parent;
               goal_task = Some t ;
               goal_checksum = sum;
               goal_shape = shape;
               goal_key = key;
               goal_external_proofs = PHprover.create 7;
               goal_transformations = PHstr.create 3;
               goal_metas = Mmetas_args.empty;
               goal_verified = None;
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
             transf_verified = None;
             transf_key = key;
             transf_goals = [];
             transf_expanded = expanded;
             transf_detached = None;
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
             metas_verified = None;
             metas_key = key;
             metas_goal = g;
             metas_expanded = expanded;
           }
  in
  g.goal_metas <- Mmetas_args.add added ms g.goal_metas;
  ms

let raw_add_theory ~(keygen:'a keygen) ~(expanded:bool)
    ~(checksum:Tc.checksum option) mfile thname =
  let parent = mfile.file_key in
  let key = keygen ~parent () in
  let mth = { theory_name = thname;
              theory_key = key;
              theory_parent = mfile;
              theory_checksum = checksum;
              theory_goals = [];
              theory_verified = None;
              theory_expanded = expanded;
              theory_task = None;
              theory_detached = None;
            }
  in
  mth

let raw_add_file ~(keygen:'a keygen) ~(expanded:bool) session f fmt =
  let key = keygen () in
  let mfile = { file_name = f;
                file_key = key;
                file_format = fmt;
                file_theories = [];
                file_verified = None;
                file_expanded = expanded;
                file_parent  = session;
                file_for_recovery = None;
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
        Done {
          Call_provers.pr_answer = answer;
          Call_provers.pr_time = time;
          Call_provers.pr_output = "";
          Call_provers.pr_status = Unix.WEXITED 0;
          Call_provers.pr_steps = steps;
          Call_provers.pr_model = Model_parser.default_model;
        }
    | "undone" -> Interrupted
    | "unedited" -> Unedited
    | s ->
        Warning.emit "[Warning] Session.load_result: unexpected element '%s'@."
          s;
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

type 'key load_ctxt = {
  old_provers : (Whyconf.prover * int * int * int) Mint.t ;
  keygen : 'key keygen;
}

let rec load_goal ctxt parent (acc,n) g =
  match g.Xml.name with
    | "goal" ->
        let gname = load_ident g in
        let expl = load_option "expl" g in
        let csum = string_attribute_opt "sum" g in
        let sum = Opt.map Tc.checksum_of_string csum in
        let shape =
          try Tc.shape_of_string (List.assoc "shape" g.Xml.attributes)
          with Not_found -> Tc.shape_of_string ""
        in
        let expanded = bool_attribute "expanded" g false in
        let mg =
          raw_add_no_task ~keygen:ctxt.keygen ~expanded parent gname n expl sum shape
        in
        List.iter (load_proof_or_transf ctxt mg) g.Xml.elements;
        mg.goal_verified <- goal_verified mg;
        (mg::acc,n+1)
    | "label" -> (acc,n)
    | s ->
        Warning.emit "[Warning] Session.load_goal: unexpected element '%s'@." s;
        (acc,n)

and load_proof_or_transf ctxt mg a =
  match a.Xml.name with
    | "proof" ->
      begin
        let prover = string_attribute "prover" a in
        try
          let prover = int_of_string prover in
          let (p,timelimit,steplimit,memlimit) =Mint.find prover ctxt.old_provers in
          let res = match a.Xml.elements with
            | [r] -> load_result r
            | [] -> Interrupted
            | _ ->
              Warning.emit "[Error] Too many result elements@.";
              raise (LoadError (a,"too many result elements"))
          in
          let edit = load_option "edited" a in
          let edit = match edit with None | Some "" -> None | _ -> edit in
          let obsolete = bool_attribute "obsolete" a false in
          let archived = bool_attribute "archived" a false in
          let timelimit = int_attribute_def "timelimit" a timelimit in
          let steplimit = int_attribute_def "steplimit" a steplimit in
          let memlimit = int_attribute_def "memlimit" a memlimit in
          let limit = { Call_provers.limit_time = timelimit;
                        Call_provers.limit_mem = memlimit;
                        Call_provers.limit_steps = steplimit } in
        (*
          if timelimit < 0 then begin
          eprintf "[Error] incorrect or unspecified  timelimit '%i'@."
          timelimit;
          raise (LoadError (a,sprintf "incorrect or unspecified timelimit %i"
          timelimit))
          end;
        *)
          let (_ : 'a proof_attempt) =
            add_external_proof ~keygen:ctxt.keygen ~archived ~obsolete
              ~limit ~edit mg p res
          in
          ()
        with Failure _ | Not_found ->
          Warning.emit "[Error] prover id not listed in header '%s'@." prover;
          raise (LoadError (a,"prover not listing in header"))
      end
    | "transf" ->
        let trname = string_attribute "name" a in
        let expanded = bool_attribute "expanded" a false in
        let mtr = raw_add_transformation ~keygen:ctxt.keygen ~expanded mg trname in
        mtr.transf_goals <-
          List.rev (fst
          (List.fold_left
             (load_goal ctxt (Parent_transf mtr))
             ([],1) a.Xml.elements));
        (* already done by raw_add_transformation:
           Hashtbl.add mg.transformations trname mtr *)
        (* The attribute "proved" is required but not read *)
        mtr.transf_verified <- transf_verified mtr
    | "metas" -> load_metas ctxt mg a;
    | "label" -> ()
    | s ->
        Warning.emit
          "[Warning] Session.load_proof_or_transf: unexpected element '%s'@."
          s

and load_metas ctxt mg a =
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
            let ts = Ty.create_tysymbol (Ident.id_fresh name) tvs NoDef in
            Hint.add hts intid ts;
            let idpos_ts = Mts.add ts pos idpos.idpos_ts in
            { idpos with idpos_ts = idpos_ts }
          | "ls_pos" ->
            (* TODO signature? *)
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
  let expanded = bool_attribute "expanded" a false in
  let metas = raw_add_metas ~keygen:ctxt.keygen ~expanded mg metas_args idpos in
  let goal = match goal with
    | [] -> raise (LoadError (a,"No subgoal for this metas"))
    | [goal] -> goal
    | _ ->
      raise (LoadError (a,"Only one goal can appear in a metas element")) in
  metas.metas_goal <-
    List.hd (fst (load_goal ctxt (Parent_metas metas) ([],1) goal));
  (* already done by raw_add_transformation:
     Hashtbl.add mg.transformations trname mtr *)
  (* The attribute "proved" is required but not read *)
  metas.metas_verified <- metas_verified metas



let load_theory ctxt mf acc th =
  match th.Xml.name with
    | "theory" ->
        let thname = load_ident th in
        let expanded = bool_attribute "expanded" th false in
        let csum = string_attribute_opt "sum" th in
        let checksum = Opt.map Tc.checksum_of_string csum in
        let mth = raw_add_theory ~keygen:ctxt.keygen ~expanded ~checksum mf thname in
        mth.theory_goals <-
          List.rev (fst
          (List.fold_left
             (load_goal ctxt (Parent_theory mth))
             ([],1) th.Xml.elements));
        mth.theory_verified <- theory_verified mth;
        mth::acc
    | s ->
        Warning.emit "[Warning] Session.load_theory: unexpected element '%s'@."
          s;
        acc

let load_file ~keygen session old_provers f =
  match f.Xml.name with
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
            let steplimit = int_attribute_def "steplimit" f 0 in
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

let load_session ~keygen session xml =
  match xml.Xml.name with
    | "why3session" ->
      let shape_version = int_attribute_def "shape_version" xml 1 in
      session.session_shape_version <- shape_version;
      Debug.dprintf debug "[Info] load_session: shape version is %d@\n" shape_version;
      (* just to keep the old_provers somewhere *)
      let old_provers =
        List.fold_left (load_file ~keygen session) Mint.empty xml.Xml.elements
      in
      Mint.iter
        (fun id (p,_,_,_) ->
          Debug.dprintf debug "prover %d: %a@." id Whyconf.print_prover p;
          PHprover.replace session.session_prover_ids p id)
        old_provers;
      Debug.dprintf debug "[Info] load_session: done@\n"
    | s ->
        Warning.emit "[Warning] Session.load_session: unexpected element '%s'@."
          s

exception ShapesFileError of string
exception SessionFileError of string

module ReadShapes (C:Compress.S) = struct

let shape = Buffer.create 97
let sum = Strings.create 32

let read_sum_and_shape ch =
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
                 (String.sub sum 0 nsum) ^
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
      | Exit -> Strings.copy sum, Buffer.contents shape


  let use_shapes = ref true

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
      with _ -> use_shapes := false; attrs
    else attrs

let read_xml_and_shapes xml_fn compressed_fn =
  use_shapes := true;
  try
    let ch = C.open_in compressed_fn in
    let xml = Xml.from_file ~fixattrs:(fix_attributes ch) xml_fn in
    C.close_in ch;
    xml, !use_shapes
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

let read_session_with_keys ~keygen dir =
  if not (Sys.file_exists dir && Sys.is_directory dir) then
    raise (SessionFileError (Pp.sprintf "%s is not an existing directory" dir));
  let xml_filename = Filename.concat dir db_filename in
  let session = empty_session dir in
  let use_shapes =
  (* If the xml is present we read it, otherwise we consider it empty *)
    if Sys.file_exists xml_filename then
      try
(*
        Tc.reset_dict ();
*)
        let xml,use_shapes = read_file_session_and_shapes dir xml_filename in
        try
          load_session ~keygen session xml.Xml.content;
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

let read_session = read_session_with_keys ~keygen:(fun ?parent:_ () -> ())

(*******************************)
(* Session modification        *)
(* expansion, add childs, ...  *)
(*******************************)

let rec set_goal_expanded g b =
  g.goal_expanded <- b;
  if not b then begin
    PHstr.iter (fun _ tr -> set_transf_expanded tr b) g.goal_transformations;
    Mmetas_args.iter (fun _ m -> set_metas_expanded m b) g.goal_metas
  end

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


(* add a why file from a session *)
(** Read file and sort theories by location *)
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
  List.sort
    (fun (l1,_,_) (l2,_,_) -> Loc.compare l1 l2)
    ltheories,theories

let add_file ~keygen env ?format filename =
  let version = env.session.session_shape_version in
  let add_goal parent (acc,n) goal =
    let g =
      let name,expl, task = Termcode.goal_expl_task ~root:true goal in
      raw_add_task
        ~version
        ~keygen ~expanded:true
        parent name n expl task
    in (g::acc,n+1)
  in
  let add_theory acc rfile thname theory =
    let checksum = None (* Some (Tc.theory_checksum theory) *) in
    let rtheory =
      raw_add_theory ~keygen ~expanded:true ~checksum rfile thname
    in
    let parent = Parent_theory rtheory in
    let tasks = List.rev (Task.split_theory theory None None) in
    let goals = fst (List.fold_left (add_goal parent) ([],1) tasks) in
    rtheory.theory_goals <- List.rev goals;
    rtheory.theory_verified <- theory_verified rtheory;
    rtheory.theory_task <- Some theory;
    rtheory::acc
  in
  let add_file session f_name fmt ordered_theories =
    let rfile = raw_add_file ~keygen ~expanded:true session f_name fmt in
    let theories =
      List.fold_left (fun acc (_,thname,th) -> add_theory acc rfile thname th)
        [] ordered_theories in
    rfile.file_theories <- List.rev theories;
    rfile
  in
  let fname = Filename.concat env.session.session_dir filename in
  Debug.dprintf debug "[Session] read file@\n";
  let ordered_theories,theories = read_file env.env ?format fname in
  Debug.dprintf debug "[Session] create tasks@\n";
  let file = add_file env.session filename format ordered_theories in
  let fname =
    Filename.basename (Filename.chop_extension filename)
  in
  env.files <- Mstr.add fname theories env.files;
  file.file_for_recovery <- Some theories;
  check_file_verified notify file;
  file

let remove_file file =
  let s = file.file_parent in
  PHstr.remove s.session_files file.file_name

(***************************)
(*      transformations    *)
(***************************)

let add_transformation ?(init=notify) ?(notify=notify) ~keygen env_session transfn g goals =
  let rtransf = raw_add_transformation ~keygen ~expanded:true g transfn in
  let parent = Parent_transf rtransf in
  let i = ref 0 in
  let parent_goal_name = g.goal_name.Ident.id_string in
  let next_subgoal task =
    incr i;
    let gid,expl,_ = Termcode.goal_expl_task ~root:false task in
    (* Format.eprintf "parent_goal_name = %s@." parent_goal_name; *)
    let goal_name =
(*      if expl = ""
      then *)parent_goal_name ^ "." ^ string_of_int !i
      (* else string_of_int !i ^ ". " ^ expl *)
    in
    let goal_name = Ident.id_register (Ident.id_derive goal_name gid) in
    (* Format.eprintf "goal_name = %s@." goal_name.Ident.id_string; *)
    goal_name, expl, task
  in
  let add_goal (acc,n) g =
    let name,expl,task = next_subgoal g in
    (* Format.eprintf "call raw_add_task with name = %s@." name.Ident.id_string; *)
    let g = raw_add_task ~version:env_session.session.session_shape_version
      ~keygen ~expanded:false parent name n expl task
    in
    (g::acc,n+1)
  in
  let goals = fst (List.fold_left add_goal ([],1) goals) in
  rtransf.transf_goals <- List.rev goals;
  rtransf.transf_verified <- transf_verified rtransf;
  init (Transf rtransf);
  check_goal_proved notify g;
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
    (* add before the goal *)
    let task = List.fold_left add_meta task0 added0 in
    let task = add_tdecl task goal in
    let idpos = pos_of_metas added0 in
    let metas = raw_add_metas ~keygen ~expanded:true g added idpos in
    let goal =
      raw_add_task ~version:env.session.session_shape_version
        ~keygen ~expanded:true (Parent_metas metas) g.goal_name
        1 (goal_expl_lazy g) task
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
         let dr = Whyconf.load_driver (Whyconf.get_main eS.whyconf)
                    eS.env
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
    ?notify ~keygen ?obsolete ?archived ?limit ?edit
    ?goal ?prover ?attempt_status ?env_session ?session a =
  let session = match env_session with
    | Some eS -> Some eS.session
    | _ -> session in
  let obsolete = Opt.get_def a.proof_obsolete obsolete in
  let archived = Opt.get_def a.proof_archived archived in
  let limit = Opt.get_def a.proof_limit limit in
  let pas = Opt.get_def a.proof_state attempt_status in
  let ngoal = Opt.get_def a.proof_parent goal in
  let nprover = match prover with
    | None -> a.proof_prover
    | Some prover -> prover in
  (* copy or generate the edit file if needed *)
  let edit =
    match edit, a.proof_edited_as, session with
      | Some edit, _, _ -> edit
      | _, None, _ -> None
      | _, _, None -> (* In the other case a session is needed *)
        None
      | _, Some file, Some session ->
        assert (file != "");
        (* Copy the edited file *)
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
            (* In the other cases an env_session and a task are needed *)
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
    ~obsolete ~archived ~limit ~edit ngoal nprover pas

exception UnloadableProver of Whyconf.prover

let update_edit_external_proof ~cntexample env_session a =
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
  Driver.print_task ~cntexample ?old driver fmt goal;
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
  fprintf fmt "%a - %a (%i, %i, %i)%s%s%s"
    Whyconf.print_prover p.proof_prover
    print_attempt_status p.proof_state
    (p.proof_limit.Call_provers.limit_time)
    (p.proof_limit.Call_provers.limit_steps)
    (p.proof_limit.Call_provers.limit_mem)
    (if p.proof_obsolete then " obsolete" else "")
    (if p.proof_archived then " archived" else "")
    (if p.proof_edited_as <> None then " edited" else "")

(***********************************************************)
(**    Reload a session with the current transformation    *)
(***********************************************************)

(** Pairing *)

module Goal = struct
  type 'a t = 'a goal
  let checksum g = g.goal_checksum
  let shape g    = g.goal_shape
  let name g     = g.goal_name
  end

module AssoGoals = Tc.Pairing(Goal)(Goal)

(**********************************)
(* merge a file into another      *)
(**********************************)

(* the import_* functions can be used to copy session items from one 'b session
   into another 'b session. The two sessions will have different keys. This is
   different from the copy_* functions where we have 'a = 'b.  Most import
   functions import the entire subtree, but do not include the subtree into the
   parent. For example, [import_theory keygen file theory] will return a new
   theory whose parent is [file], but it will not modify [file.file_theories]
   to contain the new theory. This is left to the caller. An exception to this
   rule is [import_proof_attempt], because of its usage of
   [add_external_proof]. *)

let rec import_theory ~keygen file th =
  let new_th =
    raw_add_theory
      ~keygen
      ~expanded:th.theory_expanded
      ~checksum:th.theory_checksum
      file th.theory_name in
  let goals =
    List.map (import_goal ~keygen (Parent_theory new_th)) th.theory_goals in
  new_th.theory_goals <- goals;
  new_th

and import_goal ~keygen parent g =
  let new_goal =
    raw_add_no_task
      ~keygen
      ~expanded:g.goal_expanded
      parent g.goal_name g.goal_number g.goal_expl g.goal_checksum g.goal_shape in
  PHprover.iter (fun _ v -> import_proof_attempt ~keygen new_goal v)
  g.goal_external_proofs;
  PHstr.iter (fun k v ->
    let tf = import_transf ~keygen new_goal v in
    PHstr.add new_goal.goal_transformations k tf) g.goal_transformations;
  new_goal

and import_proof_attempt ~keygen goal pa =
    ignore (add_external_proof
      ~keygen
      ~obsolete:pa.proof_obsolete
      ~archived:pa.proof_archived
      ~limit:pa.proof_limit
      ~edit:pa.proof_edited_as
      goal pa.proof_prover pa.proof_state)

and import_transf ~keygen goal tf =
  let new_tf =
    raw_add_transformation
      ~keygen
      ~expanded:tf.transf_expanded
      goal
      tf.transf_name in
  let goals =
    List.map (import_goal ~keygen (Parent_transf new_tf)) tf.transf_goals in
  new_tf.transf_goals <- goals;
  new_tf

let found_obsolete = ref false
let found_missed_goals = ref false
let found_missed_goals_in_theory = ref false

let merge_proof ~keygen obsolete to_goal _ from_proof =
  let obsolete = obsolete || from_proof.proof_obsolete in
  found_obsolete := obsolete || ! found_obsolete;
  ignore
    (add_external_proof ~keygen
       ~obsolete
       ~archived:from_proof.proof_archived
       ~limit:from_proof.proof_limit
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




let merge_metas_in_task ~theories env task from_metas =
  (* Find in the new task the new symbol (ts,ls,pr) *)
  (* We order the position bottom up and find the ident as we go
     through the task *)

  (* hashtbl that will contain the conversion *)
  let hts = Hts.create 4 in
  let hls = Hls.create 4 in
  let hpr = Hpr.create 10 in
  let obsolete = ref false in

  let read_theory ip =
    if ip.ip_library = [] then Mstr.find ip.ip_theory theories
    else Env.read_theory env.env ip.ip_library ip.ip_theory in

  let to_idpos_ts = Mts.fold_left (fun idpos_ts from_ts ip ->
    try
      let th = read_theory ip in
      let to_ts = ns_find_ts th.th_export ip.ip_qualid in
      Hts.add hts from_ts to_ts;
      Mts.add to_ts ip idpos_ts
    with e ->
      Debug.dprintf debug "[merge metas]@ can't@ find@ ident@ %a@ because@ %a@\n"
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
      Debug.dprintf debug "[merge metas]@ can't@ find@ ident@ %a@ because@ %a@\n"
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
      Debug.dprintf debug "[merge metas]@ can't@ find@ ident@ %a@ because@ %a"
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

  (* Now convert the metas to the new symbol *)
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
            Debug.dprintf debug
              "Remove the meta %a during merge because \
               the type symbol %a can't be found@\n"
              print_meta (meta_name,meta_args)
              print_ident_path pos;
            acc
          | Ls_not_found ls ->
            obsolete := true;
            let pos = Mls.find ls from_metas.metas_idpos.idpos_ls in
            Debug.dprintf debug
              "Remove the meta %a during merge because \
               the logic symbol %a can't be found@\n"
              print_meta (meta_name,meta_args)
              print_ident_path pos;
            acc
          | Pr_not_found pr ->
            obsolete := true;
            let pos = Mpr.find pr from_metas.metas_idpos.idpos_pr in
            Debug.dprintf debug
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
      Debug.dprintf debug "Remove a meta during merge: meta %s unknown@\n" s;
      acc
  in
  let goal,task = Task.task_separate_goal task in
  let metas,task =
    Mstr.fold_left add_meta (Mstr.empty,task) from_metas.metas_added
  in
  Task.add_tdecl task goal,metas,to_idpos,!obsolete

(** Release and recover goal task *)
let release_task g =
  Debug.dprintf debug "[Session] release %s@." g.goal_name.id_string;
  g.goal_task <- None

let rec release_sub_tasks g =
  release_task g;
  PHstr.iter (fun _ t -> List.iter release_sub_tasks t.transf_goals)
    g.goal_transformations;
  Mmetas_args.iter (fun _ t -> release_sub_tasks t.metas_goal) g.goal_metas

exception UnrecoverableTask of Ident.ident

type 'key update_context =
  { allow_obsolete_goals : bool;
    release_tasks : bool;
    use_shapes_for_pairing_sub_goals : bool;
    keygen : 'key keygen;
    keep_unmatched_theories : bool;
  }

let mk_update_context
  ?(allow_obsolete_goals=false)
  ?(release_tasks=false)
  ?(use_shapes_for_pairing_sub_goals=false)
  ?(keep_unmatched_theories=false)
  keygen =
  { allow_obsolete_goals;
    release_tasks;
    use_shapes_for_pairing_sub_goals;
    keygen;
    keep_unmatched_theories;
  }


let rec recover_sub_tasks ~theories env_session task g =
  g.goal_task <- Some task;
  (* Check that the sum and shape don't change (the order is kept)
     It seems an acceptable limitation. Non-deterministic transformation seems
     ugly.
  *)
  let version = env_session.session.session_shape_version in
  let sum = Termcode.task_checksum ~version task in
  let expl = goal_expl_lazy g in
  let shape = Termcode.t_shape_task ~version ~expl task in
  if not ((match g.goal_checksum with
          | None -> false
          | Some s -> Termcode.equal_checksum sum s) &&
       Termcode.equal_shape shape g.goal_shape) then
    raise (UnrecoverableTask g.goal_name);
  PHstr.iter (fun _ t ->
      let task = goal_task g in
      let subgoals = Trans.apply_transform t.transf_name env_session.env task in
      List.iter2 (recover_sub_tasks ~theories env_session) subgoals t.transf_goals)
    g.goal_transformations;
  Mmetas_args.iter (fun _ t ->
      let task,_metas,_to_idpos,_obsolete =
        merge_metas_in_task ~theories env_session task t in
      (* It is better to keep the original metas and idpos *)
      (* If it is obsolete the next task will see it *)
      recover_sub_tasks ~theories env_session task t.metas_goal
    ) g.goal_metas

let recover_theory_tasks env_session th =
  let theories = Opt.get_exn NoTask th.theory_parent.file_for_recovery in
  let theory = Opt.get_exn NoTask th.theory_task in
  th.theory_checksum <- None (* Some (Tc.theory_checksum theory) *);
  let tasks = List.rev (Task.split_theory theory None None) in
  List.iter2 (recover_sub_tasks ~theories env_session) tasks th.theory_goals

let rec theory_goal g =
  match g.goal_parent with
  | Parent_theory th -> th
  | Parent_transf t -> theory_goal t.transf_parent
  | Parent_metas t -> theory_goal t.metas_parent

let goal_task_or_recover env_session g =
  match g.goal_task with
  | Some task -> task
  | None ->
    recover_theory_tasks env_session (theory_goal g);
    Opt.get g.goal_task

(** merge session *)

(** ~theories is the current theory library path empty : [] *)
let rec merge_any_goal ~ctxt ~theories env obsolete from_goal to_goal =
  set_goal_expanded to_goal from_goal.goal_expanded;
  PHprover.iter (merge_proof ~keygen:ctxt.keygen obsolete to_goal)
    from_goal.goal_external_proofs;
  PHstr.iter (merge_trans ~ctxt ~theories env to_goal)
    from_goal.goal_transformations;
  Mmetas_args.iter (merge_metas ~ctxt ~theories env to_goal)
    from_goal.goal_metas


and merge_trans ~ctxt ~theories env to_goal _ from_transf =
  try
    let from_transf_name = from_transf.transf_name in
    let to_goal_name = to_goal.goal_name in
    Debug.dprintf debug "[Reload] transformation %s for goal %s @\n"
      from_transf_name to_goal_name.Ident.id_string;
    let to_transf =
      try
        add_registered_transformation
          ~keygen:ctxt.keygen env from_transf_name to_goal
      with exn when not (Debug.test_flag Debug.stack_trace) ->
        Debug.dprintf debug "[Reload] transformation %s produce an error:%a"
          from_transf_name Exn_printer.exn_printer exn;
        raise Exit
    in
    set_transf_expanded to_transf from_transf.transf_expanded;
    let associated,detached =
      Debug.dprintf debug "[Info] associate_subgoals, shape_version = %d@\n"
        env.session.session_shape_version;
      AssoGoals.associate ~use_shapes:ctxt.use_shapes_for_pairing_sub_goals
        from_transf.transf_goals to_transf.transf_goals
    in
    List.iter (function
      | (to_goal, Some (from_goal, obsolete)) ->
        merge_any_goal ~ctxt ~theories env obsolete  from_goal to_goal
      | (_, None) ->
        found_missed_goals_in_theory := true)
      associated;
(* TODO: we should copy the goal, using the new type of keys
    if detached <> [] then
    to_transf.transf_detached <- Some { detached_goals = detached }
 *)
    ignore detached
  with Exit -> () (* silent failure, not a good thing... *)

(** convert the ident from the old task to the ident at the same
    position in the new task *)
and merge_metas_aux ~ctxt ~theories env to_goal _ from_metas =
  Debug.dprintf debug "[Reload] metas for goal %s@\n"
    to_goal.goal_name.Ident.id_string;

  let task,metas,to_idpos,obsolete =
    merge_metas_in_task ~theories env (goal_task to_goal) from_metas in

  let to_metas =
    raw_add_metas ~keygen:ctxt.keygen ~expanded:from_metas.metas_expanded
      to_goal metas to_idpos
  in
  let to_goal =
    raw_add_task ~version:env.session.session_shape_version
      ~keygen:ctxt.keygen (Parent_metas to_metas) ~expanded:true
      to_goal.goal_name 1 (goal_expl_lazy to_goal) task
  in
  to_metas.metas_goal <- to_goal;
  Debug.dprintf debug "[Reload] metas done@\n";
  merge_any_goal ~ctxt ~theories env obsolete from_metas.metas_goal to_goal

and merge_metas ~ctxt ~theories env to_goal s from_metas =
  try
    merge_metas_aux ~ctxt ~theories env to_goal s from_metas
  with exn ->
    Debug.dprintf debug "[merge metas] error %a during merge, metas removed@\n"
      Exn_printer.exn_printer exn

exception OutdatedSession

let merge_theory ~ctxt ~theories env from_th to_th =
  found_missed_goals_in_theory := false;
  set_theory_expanded to_th from_th.theory_expanded;
  let get_goal_name g =
    try
      let (_,_,l) = restore_path g.goal_name in
      String.concat "." l
    with Not_found -> g.goal_name.Ident.id_string in
  let from_goals = List.fold_left
    (fun from_goals g -> Mstr.add (get_goal_name g) g from_goals)
    Mstr.empty from_th.theory_goals
  in
  Debug.dprintf debug
    "[Theory checksum] theory %s: old sum = %a, new sum = %a@."
    to_th.theory_name.id_string
    (Pp.print_option Tc.print_checksum) from_th.theory_checksum
    (Pp.print_option Tc.print_checksum) to_th.theory_checksum;
  List.iter
    (fun to_goal ->
      try
        let to_goal_name = get_goal_name to_goal in
        let from_goal = Mstr.find to_goal_name from_goals in
        Debug.dprintf debug
          "[Goal checksum] goal %s: old sum = %a, new sum = %a@."
          to_goal_name
          (Pp.print_option Tc.print_checksum) from_goal.goal_checksum
          (Pp.print_option Tc.print_checksum) to_goal.goal_checksum;
        let goal_obsolete =
          match to_goal.goal_checksum, from_goal.goal_checksum with
          | None, _ -> assert false
          | Some _, None -> true
          | Some s1, Some s2 -> not (Tc.equal_checksum s1 s2)
        in
        if goal_obsolete then
          begin
            Debug.dprintf debug "[Reload] Goal %s.%s has changed@\n"
              to_th.theory_name.Ident.id_string
              to_goal.goal_name.Ident.id_string;
            if not ctxt.allow_obsolete_goals then raise OutdatedSession;
            found_obsolete := true;
          end;
        merge_any_goal ~ctxt ~theories env goal_obsolete from_goal to_goal;
        if ctxt.release_tasks then release_sub_tasks to_goal
      with
        | Not_found when ctxt.allow_obsolete_goals ->
          found_missed_goals_in_theory := true;
          if ctxt.release_tasks then release_sub_tasks to_goal
        | Not_found -> raise OutdatedSession
    ) to_th.theory_goals;
  if not (ctxt.use_shapes_for_pairing_sub_goals ||
            !found_missed_goals_in_theory)
  then
    begin
      Debug.dprintf
        debug
        "[Session] since shapes were not used for pairing, we compute the \
         checksum of the full theory, to estimate the obsolete status for \
         goals.@.";
      let to_checksum = CombinedTheoryChecksum.compute to_th in
      let same_checksum =
        match from_th.theory_checksum with
        | None -> false
        | Some c -> Tc.equal_checksum c to_checksum
      in
      Debug.dprintf
        debug
        "[Session] from_checksum = %a, to_checksum = %a@."
        (Pp.print_option save_checksum) from_th.theory_checksum
        save_checksum to_checksum;
      if same_checksum then
        (* we set all_goals as non obsolete *)
        theory_iter_proof_attempt set_non_obsolete to_th
    end;
  found_missed_goals := !found_missed_goals || !found_missed_goals_in_theory

let merge_file ~ctxt ~theories env from_f to_f =
  Debug.dprintf debug "[Info] merge_file, shape_version = %d@\n"
    env.session.session_shape_version;
  set_file_expanded to_f from_f.file_expanded;
  let from_theories = List.fold_left
    (fun acc t -> Mstr.add t.theory_name.Ident.id_string t acc)
    Mstr.empty from_f.file_theories
  in
  let find_remove k map =
    let elt = Mstr.find k map in
    let acc = Mstr.remove k map in
    elt, acc in
  let remaining_theories =
    List.fold_left
      (fun acc to_th ->
        try
          let from_th, acc =
            let name = to_th.theory_name.Ident.id_string in
            find_remove name acc
          in
          merge_theory ~ctxt ~theories env from_th to_th;
          acc
        with
          | Not_found when ctxt.allow_obsolete_goals -> acc
          | Not_found -> raise OutdatedSession
      )
      from_theories to_f.file_theories in
  if ctxt.keep_unmatched_theories then
    Mstr.iter (fun _ v ->
        to_f.file_theories <-
          (import_theory ~keygen:ctxt.keygen to_f v) :: to_f.file_theories)
      remaining_theories;
  Debug.dprintf debug "[Info] merge_file, done@\n"

let rec recompute_all_shapes_goal ~release g =
  let t = goal_task g in
  let expl = goal_expl_lazy g in
  g.goal_shape <- Termcode.t_shape_task ~expl t;
  g.goal_checksum <- Some (Termcode.task_checksum t);
  if release then release_task g;
  iter_goal
    (fun _pa -> ())
    (iter_transf (recompute_all_shapes_goal ~release))
    (iter_metas  (recompute_all_shapes_goal ~release))
    g

let recompute_all_shapes_theory ~release t =
  iter_theory (recompute_all_shapes_goal ~release) t

let recompute_all_shapes_file ~release f =
  iter_file (recompute_all_shapes_theory ~release) f

let recompute_all_shapes ~release session =
  session.session_shape_version <- Termcode.current_shape_version;
  iter_session (recompute_all_shapes_file ~release) session

let update_session ~ctxt old_session env whyconf =
  Debug.dprintf debug "[Info] update_session: shape_version = %d@\n"
    old_session.session_shape_version;
(*
  AssoGoals.set_use_shapes ctxt.use_shapes_for_pairing_sub_goals;
 *)
  let new_session =
    create_session ~shape_version:old_session.session_shape_version
      old_session.session_dir
  in
  let new_session =
    { new_session with session_prover_ids = old_session.session_prover_ids }
  in
  let will_recompute_shape =
    old_session.session_shape_version <> Termcode.current_shape_version in
  let new_env_session =
    { session = new_session;
      env = env;
      whyconf = whyconf;
      files = Mstr.empty;
      loaded_provers = PHprover.create 5;
    }
  in
  found_obsolete := false;
  found_missed_goals := false;
  let files =
    PHstr.fold (fun _ old_file acc ->
      Debug.dprintf debug "[Load] file '%s'@\n" old_file.file_name;
      let new_file = add_file
        ~keygen:ctxt.keygen new_env_session
        ?format:old_file.file_format old_file.file_name
      in
      let theories = Opt.get new_file.file_for_recovery in
      Debug.dprintf debug "[Merge] file '%s'@\n" old_file.file_name;
      let ctxt = { ctxt with
        release_tasks = ctxt.release_tasks && (not will_recompute_shape) }
      in
      merge_file ~ctxt ~theories new_env_session old_file new_file;
      let fname =
        Filename.basename (Filename.chop_extension old_file.file_name)
      in
      Mstr.add fname theories acc)
      old_session.session_files
      Mstr.empty
  in
  new_env_session.files <- files;
  Debug.dprintf debug "[Info] update_session: done@\n";
  let obsolete =
    if will_recompute_shape
    then
      begin
        Debug.dprintf debug "[Info] update_session: recompute shapes@\n";
        recompute_all_shapes ~release:ctxt.release_tasks new_session;
        true
      end
    else
      !found_obsolete
  in
  assert (new_env_session.session.session_shape_version
          = Termcode.current_shape_version);
  new_env_session, obsolete, !found_missed_goals


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
  (* add before the goal *)
  let task =
    try
      Mstr.fold_left
        (fun task name s ->
          let m = Theory.lookup_meta name in
          Smeta_args.fold_left
            (fun task l -> Task.add_meta task m l) (* TODO: try with *)
            task s)
        task0 from_metas.metas_added
    with exn ->
      Debug.dprintf debug "[Paste] addition of metas produces an error:%a"
        Exn_printer.exn_printer exn;
      raise Paste_error  in
  let task = add_tdecl task goal in
  let to_goal =
    raw_add_task ~version:env.session.session_shape_version
      ~keygen ~expanded:true (Parent_metas to_metas)
      from_metas.metas_goal.goal_name 1
      (goal_expl_lazy from_metas.metas_goal) task
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
  Debug.dprintf debug "[Paste] transformation %s for goal %s @\n"
    from_transf_name to_goal_name.Ident.id_string;
  let to_transf =
    try
      add_registered_transformation
        ~keygen env from_transf_name to_goal
    with exn when not (Debug.test_flag Debug.stack_trace) ->
      Debug.dprintf debug "[Paste] transformation %s produce an error:%a"
        from_transf_name Exn_printer.exn_printer exn;
      raise Paste_error
  in
  let associated,detached =
    Debug.dprintf debug "[Info] associate_subgoals, shape_version = %d@\n"
      env.session.session_shape_version;
    AssoGoals.associate ~use_shapes:false
      from_transf.transf_goals to_transf.transf_goals in
  List.iter (function
  | (to_goal, Some (from_goal, _obsolete)) ->
    add_goal_to_parent ~keygen env from_goal to_goal
  | (_, None) -> ()
  ) associated;
(*
  if detached <> [] then
    to_transf.transf_detached <- Some { detached_goals = detached };
 *)
  ignore(detached);
  to_transf

let get_project_dir fname =
  if not (Sys.file_exists fname) then raise Not_found;
  let d =
    if Sys.is_directory fname then fname
    else if Filename.basename fname = db_filename then begin
      Debug.dprintf debug "Info: found db file '%s'@." fname;
      Filename.dirname fname
    end
    else
      begin
        Debug.dprintf debug "Info: found regular file '%s'@." fname;
        try Filename.chop_extension fname
        with Invalid_argument _ -> fname^".w3s"
      end
  in
  Debug.dprintf debug "Info: using '%s' as directory for the project@." d;
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
      | UnrecoverableTask id ->
        Format.fprintf fmt
          "A@ non-deterministic@ transformation@ is@ used,@ the@ task@ of@ \
           the@ goal@ %s@ can't@ be@ recovered." id.id_string
      | _ -> raise exn)


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3ide.byte"
End:
*)
