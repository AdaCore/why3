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

open Term
open Decl
open Trans
open Args_wrapper
open Generic_arg_trans_utils

(** This file contains transformations with arguments that eliminates logic
    connectors (instantiate, destruct, destruct_term). *)

(** Explanation *)

(* Explanation for destruct premises *)
let destruct_expl = "destruct premise"

let is_lsymbol t =
  match t.t_node with
  | Tapp (_, []) -> true
  | _ -> false

let create_constant ?name ty =
  let name = Opt.get_def "x" name in
  let fresh_name = Ident.id_fresh name in
  let ls = create_lsymbol fresh_name [] (Some ty) in
  (ls, create_param_decl ls)

let chose_next_name names =
  match names with
  | hd :: tl -> (Some hd, tl)
  | [] -> (None, [])

let rec return_list ~names list_types type_subst =
  match list_types with
  | [] -> (names, [])
  | hd :: tl ->
      let (name, names) = chose_next_name names in
      let ty = Ty.ty_inst type_subst hd in
      let (names, res) = return_list ~names tl type_subst in
      (names, create_constant ?name ty :: res)

let my_ls_app_inst ls ty =
  match ls.ls_value, ty with
    | Some _, None -> raise (PredicateSymbolExpected ls)
    | None, Some _ -> raise (FunctionSymbolExpected ls)
    | Some vty, Some ty -> Ty.ty_match Ty.Mtv.empty vty ty
    | None, None -> Ty.Mtv.empty

let rec build_decls ~names cls x =
  match cls with
  | [] -> []
  | (cs, _) :: tl ->
      let type_subst = my_ls_app_inst cs x.t_ty in
      let (names, l) = return_list ~names cs.ls_args type_subst in
      let teqx =
        (t_app cs (List.map (fun x -> t_app_infer (fst x) []) l) x.t_ty) in
      let ht = t_equ x teqx in
      let h = Decl.create_prsymbol (gen_ident "h") in
      let new_hyp = Decl.create_prop_decl Decl.Paxiom h ht in
      ((List.map snd l) @ [new_hyp]) :: build_decls ~names tl x

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
let destruct_term ?names replace (x: term) : Task.task tlist =
  let names = Opt.get_def [] names in
  (* Shortcut function *)
  let add_decl_list task l =
    List.fold_left (fun task d -> Task.add_decl task d) task l in
  (* Shortcut used for map *)
  let add_decl d task = Task.add_decl task d in

  let ty = x.t_ty in
  match ty with
  | None -> raise (Cannot_infer_type "destruct")
  | Some ty ->
    begin
      match ty.Ty.ty_node with
      | Ty.Tyvar _       -> raise (Cannot_infer_type "destruct")
      | Ty.Tyapp (ts, _) ->
        (* This records the constants that the destructed terms is defined with
           (in order not to generate the equality before their definition). *)
        let ls_of_x = compounds_of Term.Sls.empty x in
        (* [ls_of_x] is the set of constants used in the term definition. Each
           time we encounter one, we remove it from the Sls. When there are none
           left, we can put the definition of equality for the destructed term.
           [r] are the new declarations made by the destruction.
           [defined] records is set to true when the definitions have been added
           [task_list] is the tasks under construction *)
        let trans = fold_map (fun t ((ls_of_x, r, defined), task_list) ->
          match t.Task.task_decl.Theory.td_node with
          | Theory.Decl d ->
              begin match d.d_node with
                (* TODO not necessary to check this first: can be optimized *)
                | _ when (not defined) && Term.Sls.is_empty ls_of_x ->
                    if r = [] then
                      ((ls_of_x, r, defined), List.map (add_decl d) task_list)
                    else
                      ((ls_of_x, [], true),
                       let add_r =
                         List.fold_left (fun acc_task_list task ->
                             List.fold_left (fun acc_task_list ldecl ->
                                 (add_decl_list task ldecl) :: acc_task_list)
                               acc_task_list r)
                           [] task_list in
                       List.map (add_decl d) add_r)
                | Dlogic dls          ->
                    let ls_of_x =
                      List.fold_left
                        (fun acc (ls, _) -> Term.Sls.remove ls acc)
                        ls_of_x dls in
                    ((ls_of_x, r, defined), List.map (add_decl d) task_list)
                | Dparam ls ->
                    let ls_of_x = Term.Sls.remove ls ls_of_x in
                    ((ls_of_x, r, defined), List.map (add_decl d) task_list)
                | Dind (_, ils) ->
                    let ls_of_x =
                      List.fold_left
                        (fun acc (ls, _) -> Term.Sls.remove ls acc)
                        ls_of_x ils in
                    ((ls_of_x, r, defined), List.map (add_decl d) task_list)
                | Ddata dls ->
                    begin try
                        let cls = List.assoc ts dls in
                        let r = build_decls ~names cls x in
                        ((ls_of_x, r, defined), List.map (add_decl d) task_list)
                      with Not_found -> ((ls_of_x, r, defined),
                                         List.map (add_decl d) task_list)
                    end
                | Dprop (Pgoal, _, _) ->
                    ((ls_of_x, r, defined), List.map (add_decl d) task_list)
                | _ -> ((ls_of_x, r, defined), List.map (add_decl d) task_list)
              end
          | _ -> ((ls_of_x, r, defined),
                  List.map (fun task ->
                      Task.add_tdecl task t.Task.task_decl) task_list)
          )
            (ls_of_x, [], false) [None]
        in
        if replace && is_lsymbol x then
          compose_l trans (singleton (Subst.subst [x]))
        else
          trans
    end

(** [expand p] returns a list of triples [(bindings, equalities, term)], where

    1. [bindings] map pattern variables in [p] to term variables in [term]
    2. [equalities] contain equalities between pattern variables from [as]
      patterns, term variables, and terms
    3. [term] corresponds to [p] under [bindings] and [equalities] *)
let rec expand (p:pattern) : ((vsymbol option * lsymbol) list * (vsymbol * lsymbol * term) list * term) list =
  match p.pat_node with
  | Pwild ->
      let ls =
        let id = Ident.id_fresh "_" in
        create_lsymbol id [] (Some p.pat_ty)
      in
      [[None, ls], [], t_app ls [] ls.ls_value]
  | Pvar v ->
      let ls =
        let id = Ident.id_clone v.vs_name in
        create_lsymbol id [] (Some p.pat_ty)
      in
      [[Some v, ls], [], t_app ls [] ls.ls_value]
  | Papp (ls, args) ->
      let rec aux args =
        match args with
        | [] -> [[], [], []] (* really. *)
        | arg::args' ->
            let for_args' (x, eqs, t) (x', eqs', l) =
              x@x', eqs@eqs', t::l
            in
            let for_arg l' arg =
              List.map (for_args' arg) l'
            in
            List.flatten
              (List.map (for_arg (aux args'))
                 (expand arg))
      in
      let for_arg (bds, eqs, args) =
        bds, eqs, t_app ls args (Some p.pat_ty)
      in
      List.map for_arg (aux args)
  | Por (p1, p2) ->
      expand p1 @ expand p2
  | Pas (p, v) ->
      let ls =
        let id = Ident.id_clone v.vs_name in
        create_lsymbol id [] (Some p.pat_ty)
      in
      let for_t (bds, eqs, t) =
        let eqs' = eqs@[(v, ls, t)] in
        let t' = t_app ls [] ls.ls_value in
        bds, eqs', t'
      in
      List.map for_t (expand p)

(* Type used to tag new declarations inside the destruct function. *)
type is_destructed =
  | Axiom_term of term
  | Param of Decl.decl
  | Goal_term of term

(* [destruct_fmla ~decl_name t]: This destroys a headterm and
     generate an appropriate lists of goals/declarations that can be used by
     decl_goal_l.

   [recursive] when false, disallow the recursive calls to destruct_fmla

   In this function, we use "parallel" to refer to elements of the topmost list
   which are eventually converted to disjoint tasks.
*)
let destruct_fmla ~recursive (t: term) =
  (* Standard way to know that a lsymbol is a constructor TODO ? *)
  let is_constructor l =
    l.ls_constr <> 0
  in

  (* Main recursive function:
     [toplevel] when true, removing implications is allowed. Become false as
     soon as we destruct non-implication construct
  *)
  let rec destruct_fmla ~toplevel (t: term) =
    let destruct_fmla_exception ~toplevel t =
      if not recursive then [[Axiom_term t]] else
        match destruct_fmla ~toplevel t with
        | exception _ -> [[Axiom_term t]]
        | l -> l
    in

    match t.t_node with
    | Tfalse ->
        []
    | Ttrue ->
        [[]]
    | Tbinop (Tand, t1, t2) ->
        let l1 = destruct_fmla_exception ~toplevel:false t1 in
        let l2 = destruct_fmla_exception ~toplevel:false t2 in
        (* For each parallel branch of l1 we have to append *all* parallel
           branch of l2 which are not new goals. In case of new goals, we are
           not allowed to use the left/right conclusions to prove the goal.
           Example:
           H: (A -> (B /\ C) /\ (C -> A)
           Goal g: C
        *)
        (* TODO efficiency: this is not expected to work on very large terms
           with tons of Tand/Tor. *)
        List.fold_left (fun par_acc seq_list1 ->
            List.fold_left (fun par_acc seq_list2 ->
                par_acc @ [seq_list1 @ seq_list2]) par_acc l2
          ) [] l1
    | Tbinop (Tor, t1, t2) ->
        let l1 = destruct_fmla_exception ~toplevel:false t1 in
        let l2 = destruct_fmla_exception ~toplevel:false t2 in
        (* The two branch are completely disjoint. We just concatenate them to
           ensure they are done in parallel *)
        l1 @ l2
    | Tbinop (Timplies, t1, t2) when toplevel ->
        (* The premises is converted to a goal. The rest is recursively
           destructed in parallel. *)
        let l2 = destruct_fmla_exception ~toplevel t2 in
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
           (* The recursive call is done after new symbols are introduced so we
              readd the new decls to every generated list. *)
           let l_t = destruct_fmla_exception ~toplevel:false new_t in
           List.map (fun x -> Param x_decl :: x) l_t
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
      (* Cs1 [l1] = Cs2 [l2] *)
      if ls_equal cs1 cs2 then
        [[Axiom_term t]]
      else
        (* The hypothesis is trivial because Cs1 <> Cs2 thus useless *)
        [[]]
    | Tnot t1 ->
        (* Keep toplevel: this is considered an implication *)
        destruct_fmla_exception ~toplevel (t_implies t1 t_false)
    | Tif (t1, t2, t3) ->
        let ts2 =
          destruct_fmla_exception ~toplevel:false t2 |>
          List.map (fun ts -> Axiom_term t1 :: ts)
        in
        let ts3 =
          destruct_fmla_exception ~toplevel:false t3 |>
          List.map (fun ts -> Axiom_term (t_not t1) :: ts)
        in
        ts2 @ ts3
    | Tcase (t, tbs) when toplevel ->
        let for_branch tb =
          let pat, rhs = t_open_branch tb in
          let for_expansion (bds, eqs, t') =
            let mvs =
              let for_binding acc vls =
                match vls with
                | Some v, ls -> Mvs.add v (t_app ls [] ls.ls_value) acc
                | None, _ -> acc
              in
              List.fold_left for_binding Mvs.empty bds in
            let mvs =
              let for_eq acc (vs, ls, _) =
                Mvs.add vs (t_app ls [] ls.ls_value) acc
              in
              List.fold_left for_eq mvs eqs
            in
            let for_rhs rhs' =
              let mk_const (_, ls) = Param (create_param_decl ls) in
              let mk_eq_axiom (_, ls, t) = Param (create_logic_decl [make_ls_defn ls [] t]) in
              List.map mk_const bds @
              List.map mk_eq_axiom eqs @
              [Axiom_term (t_equ t t')] @
              rhs'
            in
            t_subst mvs rhs |>
            destruct_fmla_exception ~toplevel:false |>
            List.map for_rhs
          in
          List.map for_expansion (expand pat)
        in
        List.map for_branch tbs |>
        List.flatten |>
        List.flatten
    | _ -> raise (Arg_trans ("destruct"))
  in
  destruct_fmla ~toplevel:true t

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
          let decl_list = destruct_fmla ~recursive ht in
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
    ~desc:"instantiate <prop> <term list>@ \
      generates@ a@ new@ hypothesis@ with@ quantified@ variables@ \
      of@ <prop>@ replaced@ with@ the@ given@ terms."
    "instantiate"
    (Tprsymbol (Ttermlist Ttrans)) (instantiate ~rem:false)

let () = wrap_and_register
    ~desc:"instantiate <prop> <term list>@ \
      generates@ a@ new@ hypothesis@ with@ quantified@ variables@ \
      of@ <prop>@ replaced@ with@ then@ given@ terms.@ \
      Also@ removes@ the@ old@ hypothesis."
    "inst_rem"
    (Tprsymbol (Ttermlist Ttrans)) (instantiate ~rem:true)

let () = wrap_and_register
    ~desc:"destruct <name>@ \
      destructs@ the@ top-most@ propositional@ connector@ \
      (/\\,@ \\/,@ ->@ or@ <->)@ of@ the@ given@ hypothesis.@ \
      To@ destruct@ a@ literal@ of@ an@ algebraic@ type,@ \
      use@ 'destruct_term'."
    "destruct" (Tprsymbol Ttrans_l) (destruct ~recursive:false)

let () = wrap_and_register
    ~desc:"destruct_rec <name>@ \
      recursively@ destructs@ the@ top@ propositional@ connectors@ \
      (/\\,@ \\/,@ ->@ or@ <->)@ of@ the@ given@ hypothesis.@ \
      To@ destruct@ a@ literal@ of@ an@ algebraic@ type,@ \
      use@ 'destruct_term'."
    "destruct_rec" (Tprsymbol Ttrans_l) (destruct ~recursive:true)

let () = wrap_and_register
    ~desc:"destruct_term <term> [using] <id list>@ \
      destructs@ the@ given@ term@ of@ an@ algebraic@ type.@ \
      Option@ 'using'@ can@ be@ used@ to@ name@ the@ elements@ \
      created@ by@ 'destruct_term'."
    "destruct_term" (Tterm (Topt ("using", Tidentlist Ttrans_l)))
    (fun t names -> destruct_term ?names false t)

let () = wrap_and_register
    ~desc:"destruct_term_subst <term> [using] <id list>@ \
      destructs@ the@ given@ term@ of@ an@ algebraic@ type@ \
      and@ substitutes@ the@ definition@ if@ the@ term@ is@ \
      a@ constant@ function@ symbol.@ \
      Option@ 'using'@ can@ be@ used@ to@ name@ the@ elements@ \
      created@ by@ 'destruct_term_subst'."
    "destruct_term_subst" (Tterm (Topt ("using", Tidentlist Ttrans_l)))
    (fun t names -> destruct_term ?names true t)
