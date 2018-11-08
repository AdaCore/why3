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

(* Type used to tag new declarations inside the destruct function. *)
type is_destructed =
  | Axiom_term of term
  | Param of Decl.decl
  | Goal_term of term

(* [destruct_term ~original_decl ~decl_name t]: This destroys a headterm and
     generate an appropriate lists of goals/declarations that can be used by
     decl_goal_l.

   [recursive] when false, disallow the recursive calls to destruct_term

   In this function, we use "parallel" to refer to elements of the topmost list
   which are eventually converted to disjoint tasks.
*)
let destruct_term ~recursive (t: term) =
  let original_decl = t in
  (* Standard way to know that a lsymbol is a constructor TODO ? *)
  let is_constructor l =
    l.ls_constr <> 0
  in

  (* Main function *)
  let rec destruct_term (t: term) =
    let destruct_term_exception t =
      if not recursive then [[Axiom_term t]] else
        match destruct_term t with
        | exception _ -> [[Axiom_term t]]
        | l -> l
    in

    match t.t_node with
    | Tbinop (Tand, t1, t2) ->
        let l1 = destruct_term_exception t1 in
        let l2 = destruct_term_exception t2 in
        (* For each parallel branch of l1 we have to append *all* parallel
           branch of l2. *)
        (* TODO efficiency: this is not expected to work on very large terms
           with tons of Tand/Tor. *)
        List.fold_left (fun par_acc seq_list1 ->
            List.fold_left (fun par_acc seq_list2 ->
                par_acc @ ([seq_list1 @ seq_list2])) par_acc l2
          ) [] l1
    | Tbinop (Tor, t1, t2) ->
        let l1 = destruct_term_exception t1 in
        let l2 = destruct_term_exception t2 in
        (* The two branch are completely disjoint. We just concatenate them to
           ensure they are done in parallel *)
        l1 @ l2
    | Tbinop (Timplies, t1, t2) ->
        (* The premises is converted to a goal. The rest is recursively
           destructed in parallel. *)
        let l2 = destruct_term_exception t2 in
        [Goal_term t1] :: l2
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
           (* TODO remove original_decl here ? *)
           (* The recursive call is done after new symbols are introduced so we
              readd the new decls to every generated list. *)
           let l_t = destruct_term_exception new_t in
           List.map (fun x -> Axiom_term original_decl :: Param x_decl :: x) l_t
         with
         | Ty.TypeMismatch (ty1, ty2) ->
             raise (Arg_trans_type ("destruct_exists", ty1, ty2)))
      | [] -> raise (Arg_trans ("destruct_exists"))
      end
    (* Beginning of cases for injection transformation. With C1, C2 constructors,
       simplify H: C1 ?a = C1 ?b into ?a = ?b and remove trivial hypothesis of
       the form H: C1 <> C2. *)
    | Tapp (ls, [{t_node = Tapp (cs1, l1); _}; {t_node = Tapp (cs2, l2); _}])
      when ls_equal ls ps_equ && is_constructor cs1 && is_constructor cs2 ->
      (* Cs1 [l1] = Cs2 [l2] *)
      if ls_equal cs1 cs2 then
        (* Create new hypotheses for equalities of l1 and l2 *)
        try
          [List.map2 (fun x1 x2 ->
               let equal_term = t_app_infer ps_equ [x1; x2] in
               Axiom_term equal_term) l1 l2]
        with
        | _ -> [[Axiom_term t]]
      else
        (* TODO Replace the hypothesis by False or manage to remove the goal. *)
        [[Axiom_term t_false]]

    | Tnot {t_node = Tapp (ls,
                  [{t_node = Tapp (cs1, _); _}; {t_node = Tapp (cs2, _); _}]); _}
        when ls_equal ls ps_equ && is_constructor cs1 && is_constructor cs2 ->
      (* Cs1 [l1] <> Cs2 [l2] *)
      if ls_equal cs1 cs2 then
        [[Axiom_term t]]
      else
        (* The hypothesis is trivial because Cs1 <> Cs2 thus useless *)
        [[]]
    | _ -> raise (Arg_trans ("destruct"))
  in
  destruct_term t

(* Destruct the head term of an hypothesis if it is either
   conjunction, disjunction or exists *)
let destruct ~recursive pr : Task.task tlist =
  let create_destruct_axiom t =
    let new_pr = create_prsymbol (Ident.id_clone pr.pr_name) in
    create_prop_decl Paxiom new_pr t
  in
  let create_destruct_goal t =
    let new_pr = create_prsymbol (gen_ident "G") in
    create_goal ~expl:destruct_expl new_pr t
  in

  decl_goal_l (fun d ->
      match d.d_node with
      | Dprop (Paxiom, dpr, ht) when Ident.id_equal dpr.pr_name pr.pr_name ->
          (* TODO solve the problem of original_decl not being a decl anymore ??? *)
          let decl_list = destruct_term ~recursive ht in
          List.map (fun l -> List.map (fun x ->
              match x with
              | Axiom_term t -> Normal_decl (create_destruct_axiom t)
              | Param d -> Normal_decl d
              | Goal_term t -> Goal_decl (create_destruct_goal t)
            ) l) decl_list
      | _ -> [[Normal_decl d]]) None

(* from task [delta, name:forall x.A |- G,
     build the task [delta,name:forall x.A,name':A[x -> t]] |- G]
   When [rem] is true, the general hypothesis is removed.
*)
let instantiate ~rem (pr: Decl.prsymbol) lt =
  let r = ref [] in
  decl
    (fun d ->
      match d.d_node with
      | Dprop (pk, dpr, ht) when Ident.id_equal dpr.pr_name pr.pr_name
         && pk <> Pgoal ->
          let t_subst = subst_forall_list ht lt in
          let new_pr = create_prsymbol (gen_ident "Hinst") in
          let new_decl = create_prop_decl pk new_pr t_subst in
          r := [new_decl];
          (* We remove the original hypothesis only if [rem] is set *)
          if rem then [] else [d]
      | Dprop (Pgoal, _, _) -> !r @ [d]
      | _ -> [d]) None

let () = wrap_and_register
    ~desc:"instantiate <prop> <term list> generates a new hypothesis with quantified variables of prop replaced with terms"
    "instantiate"
    (Tprsymbol (Ttermlist Ttrans)) (instantiate ~rem:false)

let () = wrap_and_register
    ~desc:"instantiate <prop> <term list> generates a new hypothesis with quantified variables of prop replaced with terms. Also remove the old hypothesis."
    "inst_rem"
    (Tprsymbol (Ttermlist Ttrans)) (instantiate ~rem:true)

let () = wrap_and_register ~desc:"destruct <name> destructs the head logic constructor of hypothesis name (/\\, \\/, -> or <->).\nTo destruct a literal of algebraic type, use destruct_alg."
    "destruct" (Tprsymbol Ttrans_l) (destruct ~recursive:false)

let () = wrap_and_register ~desc:"destruct <name> recursively destructs the head logic constructor of hypothesis name (/\\, \\/, -> or <->).\nTo destruct a literal of algebraic type, use destruct_alg."
    "destruct_rec" (Tprsymbol Ttrans_l) (destruct ~recursive:true)

let () = wrap_and_register ~desc:"destruct <name> destructs as an algebraic type"
    "destruct_alg" (Tterm Ttrans_l) (destruct_alg false)

let () = wrap_and_register ~desc:"destruct <name> destructs as an algebraic type and substitute the definition if an lsymbol was provided"
    "destruct_alg_subst" (Tterm Ttrans_l) (destruct_alg true)
