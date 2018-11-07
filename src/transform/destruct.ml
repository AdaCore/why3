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

open Term
open Decl
open Trans
open Args_wrapper
open Generic_arg_trans_utils

(** This file contains transformations with arguments that eliminates logic
    connectors (instantiate, destruct, destruct_alg). *)

(** Explanation *)

(* Explanation for destruct premises *)
let destruct_expl = "destruct premise"

let is_lsymbol t =
  match t.t_node with
  | Tapp (_, []) -> true
  | _ -> false

let create_constant ty =
  let fresh_name = Ident.id_fresh "x" in
  let ls = create_lsymbol fresh_name [] (Some ty) in
  (ls, create_param_decl ls)

let rec return_list list_types type_subst =
  match list_types with
  | [] -> []
  | hd :: tl ->
      create_constant (Ty.ty_inst type_subst hd) :: return_list tl type_subst

let my_ls_app_inst ls ty =
  match ls.ls_value, ty with
    | Some _, None -> raise (PredicateSymbolExpected ls)
    | None, Some _ -> raise (FunctionSymbolExpected ls)
    | Some vty, Some ty -> Ty.ty_match Ty.Mtv.empty vty ty
    | None, None -> Ty.Mtv.empty

let rec build_decls cls x =
  match cls with
  | [] -> []
  | (cs, _) :: tl ->
      let type_subst = my_ls_app_inst cs x.t_ty in
      let l = return_list cs.ls_args type_subst in
      let teqx =
        (t_app cs (List.map (fun x -> t_app_infer (fst x) []) l) x.t_ty) in
      let ht = t_equ x teqx in
      let h = Decl.create_prsymbol (gen_ident "h") in
      let new_hyp = Decl.create_prop_decl Decl.Paxiom h ht in
      ((List.map snd l) @ [new_hyp]) :: build_decls tl x

(* Enumerate all constants of a term *)
let rec compounds_of acc (t: term) =
  match t.t_node with
  | Tapp (ls, _) -> Term.t_fold compounds_of (Term.Sls.add ls acc) t
  | _ -> Term.t_fold compounds_of acc t

(* This tactic acts on a term of algebraic type. It introduces one
   new goal per constructor of the type and introduce corresponding
   variables. It also introduce the equality between the term and
   its destruction in the context.
   When replace is set to true, a susbtitution is done when x is an lsymbol.
 *)
let destruct_alg replace (x: term) : Task.task tlist =
  let ty = x.t_ty in
  (* We list all the constants used in x so that we know the first place in the
     task where we can introduce hypothesis about the destruction of x. *)
  let ls_of_x = ref (compounds_of Term.Sls.empty x) in
  let defined = ref false in
  let r = ref [] in
  match ty with
  | None -> raise (Cannot_infer_type "destruct")
  | Some ty ->
    begin
      match ty.Ty.ty_node with
      | Ty.Tyvar _       -> raise (Cannot_infer_type "destruct")
      | Ty.Tyapp (ts, _) ->
        let trans = decl_l (fun d ->
          match d.d_node with
          (* TODO not necessary to check this first: this can be optimized *)
          | _ when (not !defined) && Term.Sls.is_empty !ls_of_x ->
              if !r = [] then
                [[d]]
              else
                begin
                  defined := true;
                  List.map (fun x -> x @ [d]) !r
                end
          | Dlogic dls          ->
              ls_of_x :=
                List.fold_left
                  (fun acc (ls, _) -> Term.Sls.remove ls acc)
                  !ls_of_x dls;
              [[d]]
          | Dparam ls ->
              ls_of_x := Term.Sls.remove ls !ls_of_x;
              [[d]]
          | Dind (_, ils)       ->
              ls_of_x :=
                List.fold_left
                  (fun acc (ls, _) -> Term.Sls.remove ls acc)
                  !ls_of_x ils;
              [[d]]
          | Ddata dls           ->
              (try
                (let cls = List.assoc ts dls in
                r := build_decls cls x;
                [[d]]
                )
              with Not_found -> [[d]])
          | Dprop (Pgoal, _, _) ->
              [[d]]
          | _ -> [[d]]) None
        in
        if replace && is_lsymbol x then
          compose_l trans (singleton (Subst.subst [x]))
        else
          trans
    end

(* [destruct_term ~original_decl ~decl_name t]: This destroys a headterm and
     generate an appropriate lists of goals/declarations that can be used by
     decl_goal_l.

   [original_decl] referenced the declaration corresponding to [t] in the task.
     It exists only to keep the exists hypothesis. TODO remove ?
   [decl_name] is the name of the [original_decl]. It is here only to name new
     hypotheses.
*)
let destruct_term ~original_decl ~decl_name (t: term) =

  let create_destruct_axiom t =
    let new_pr = create_prsymbol (Ident.id_clone decl_name) in
    create_prop_decl Paxiom new_pr t
  in
  let create_destruct_goal t =
    let new_pr = create_prsymbol (Ident.id_clone decl_name) in
    create_prop_decl Pgoal new_pr t
  in

  match t.t_node with
  | Tbinop (Tand, t1, t2) ->
      let t1 = create_destruct_axiom t1 in
      let t2 = create_destruct_axiom t2 in
      [[Normal_decl t1;Normal_decl t2]]
  | Tbinop (Tor, t1, t2) ->
      let t1 = create_destruct_axiom t1 in
      let t2 = create_destruct_axiom t2 in
      [[Normal_decl t1];[Normal_decl t2]]
  | Tbinop (Timplies, t1, t2) ->
      begin
        let t1 = create_destruct_goal t1 in
        let t2 = create_destruct_axiom t2 in
        (* Creates a task with hypothesis removes (need to prove t1) and one
           with hypothesis replaced by t2 (needs to prove current goal).
           Example: "false -> false" *)
        [[Goal_decl t1]; [Normal_decl t2]]
      end
  | Tquant (Texists, tb) ->
    let (vsl, tr, te) = Term.t_open_quant tb in
    begin match vsl with
    | x :: tl ->
        let ls = create_lsymbol (Ident.id_clone x.vs_name) [] (Some x.vs_ty) in
        let tx = fs_app ls [] x.vs_ty in
        let x_decl = create_param_decl ls in
        (try
           let part_t = t_subst_single x tx te in
           let new_t = t_quant_close Texists tl tr part_t in
           let new_t = create_destruct_axiom new_t in
           [[Normal_decl original_decl; Normal_decl x_decl; Normal_decl new_t]]
         with
         | Ty.TypeMismatch (ty1, ty2) ->
             raise (Arg_trans_type ("destruct_exists", ty1, ty2)))
    | [] -> raise (Arg_trans ("destruct_exists"))
    end
  | _ -> raise (Arg_trans ("destruct"))

(* Destruct the head term of an hypothesis if it is either
   conjunction, disjunction or exists *)
let destruct pr : Task.task tlist =
  decl_goal_l (fun d ->
      match d.d_node with
      | Dprop (Paxiom, dpr, ht) when Ident.id_equal dpr.pr_name pr.pr_name ->
          destruct_term ~original_decl:d ~decl_name:dpr.pr_name ht
      | _ -> [[Normal_decl d]]) None

(* from task [delta, name:forall x.A |- G,
     build the task [delta,name:forall x.A,name':A[x -> t]] |- G] *)
let instantiate (pr: Decl.prsymbol) lt =
  let r = ref [] in
  decl
    (fun d ->
      match d.d_node with
      | Dprop (pk, dpr, ht) when Ident.id_equal dpr.pr_name pr.pr_name ->
          let t_subst = subst_forall_list ht lt in
          let new_pr = create_prsymbol (gen_ident "Hinst") in
          let new_decl = create_prop_decl pk new_pr t_subst in
          r := [new_decl];
          [d]
      | Dprop (Pgoal, _, _) -> !r @ [d]
      | _ -> [d]) None

let () = wrap_and_register
    ~desc:"instantiate <prop> <term list> generates a new hypothesis with quantified variables of prop replaced with terms"
    "instantiate"
    (Tprsymbol (Ttermlist Ttrans)) instantiate

let () = wrap_and_register ~desc:"destruct <name> destructs the head logic constructor of hypothesis name (/\\, \\/, -> or <->).\nTo destruct a literal of algebraic type, use destruct_alg."
    "destruct" (Tprsymbol Ttrans_l) destruct

let () = wrap_and_register ~desc:"destruct <name> destructs as an algebraic type"
    "destruct_alg" (Tterm Ttrans_l) (destruct_alg false)

let () = wrap_and_register ~desc:"destruct <name> destructs as an algebraic type and substitute the definition if an lsymbol was provided"
    "destruct_alg_subst" (Tterm Ttrans_l) (destruct_alg true)
