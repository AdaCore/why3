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

open Decl
open Theory

let debug = Debug.register_info_flag "detect_poly"
  ~desc:"Print@ debugging@ messages@ of@ the@ \
    'detect_polymorphism'@ transformation."

(* metas to attach to symbols or propositions to tell their polymorphic
   nature can be ignored because it will be treated specifically by
   drivers *)

let meta_ignore_polymorphism_ts =
  register_meta
    "encoding:ignore_polymorphism_ts" [MTtysymbol]
    ~desc:"Ignore@ polymorphism@ of@ given@ type@ symbol."

let meta_ignore_polymorphism_ls =
  register_meta
    "encoding:ignore_polymorphism_ls" [MTlsymbol]
    ~desc:"Ignore@ polymorphism@ of@ given@ logic@ symbol."

let meta_ignore_polymorphism_pr =
  register_meta
    "encoding:ignore_polymorphism_pr" [MTprsymbol]
    ~desc:"Ignore@ polymorphism@ of@ given@ proposition."

(* exclusive meta that is set by the transformation when no
   polymorphic definition is found *)

let meta_monomorphic_types_only =
  register_meta_excl "encoding:monomorphic_only" []
  ~desc:"Set@ when@ no@ occurrences@ of@ type@ variables@ occur."


let check_ts ign_ts ts =
  ts.Ty.ts_args <> [] &&
  ts.Ty.ts_def = Ty.NoDef &&
  not (Ty.Sts.mem ts ign_ts)

let check_ls ign_ls ls =
  not (Term.Sls.mem ls ign_ls) &&
  List.fold_left
    (fun acc ty -> acc || not (Ty.ty_closed ty))
    false
    (Ty.oty_cons ls.Term.ls_args ls.Term.ls_value)

let detect_polymorphism_in_decl ign_ts ign_ls ign_pr d =
  Debug.dprintf debug "|sts|=%d |sls|=%d |spr|=%d@."
                (Ty.Sts.cardinal ign_ts)
                (Term.Sls.cardinal ign_ls)
                (Spr.cardinal ign_pr);
  Debug.dprintf debug "decl %a@."
                Pretty.print_decl d;
  match d.d_node with
  | Dtype ts -> check_ts ign_ts ts
  | Ddata dl ->
     List.fold_left (fun acc (ts,_) -> acc || check_ts ign_ts ts) false dl
  | Dparam ls ->
     Debug.dprintf debug "param %a@."
                Pretty.print_ls ls;
     check_ls ign_ls ls
  | Dlogic dl ->
     (* note: we don't need to check also that definition bodies are
        monomorphic, since it is checked by typing *)
     List.fold_left (fun acc (ls,_) -> acc || check_ls ign_ls ls) false dl
  | Dind (_,indl) ->
     (* note: we don't need to check also that clauses are
        monomorphic, since it is checked by typing *)
     List.fold_left (fun acc (ls,_) -> acc || check_ls ign_ls ls) false indl
  | Dprop (_,pr,t) ->
     (* todo: DO NOT TEST the goal. This requires skolemizing
        type variables in the goal _before_ eliminate_epsilon
        in the transformation chain, to avoid producing
        polymorphic identities in monomorphic tasks *)
     not (Spr.mem pr ign_pr) &&
       let s = Term.t_ty_freevars Ty.Stv.empty t in
       not (Ty.Stv.is_empty s)


let detect_polymorphism_in_task_hd ign_ts ign_l ign_pr t acc =
  match t.Task.task_decl.td_node with
  | Decl d -> acc || detect_polymorphism_in_decl ign_ts ign_l ign_pr d
  | Use _ | Clone _ | Meta _ -> acc


let detect_polymorphism_in_task =
  Trans.on_tagged_ts
    meta_ignore_polymorphism_ts
    (fun sts ->
     Trans.on_tagged_ls
       meta_ignore_polymorphism_ls
       (fun sls ->
        Trans.on_tagged_pr
          meta_ignore_polymorphism_pr
          (fun spr ->
           Trans.fold
             (detect_polymorphism_in_task_hd sts sls spr)
             false)))

let detect_polymorphism task =
  if Trans.apply detect_polymorphism_in_task task then task else
    try
      let g,t = Task.task_separate_goal task in
      let ta = Task.add_meta t meta_monomorphic_types_only [] in
      Task.add_tdecl ta g
    with Task.GoalNotFound ->
      Task.add_meta task meta_monomorphic_types_only []

let () = Trans.register_transform "detect_polymorphism"
  (Trans.store detect_polymorphism)
  ~desc:"Detect if task has polymorphic types somewhere."
