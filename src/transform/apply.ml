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

open Trans
open Term
open Decl
open Theory
open Task
open Args_wrapper
open Reduction_engine
open Generic_arg_trans_utils

(** This file contains transformations with arguments that acts on specific
    declarations to refine them (rewrite, replace, apply, unfold, subst...) *)


let debug_matching = Debug.register_info_flag "print_match"
  ~desc:"Print@ terms@ that@ were@ not@ successfully@ matched@ by@ ITP@ tactic@ apply."

(* Do as intros: introduce all premises of hypothesis pr and return a triple
   (goal, list_premises, binded variables) *)
let intros f =
  let rec intros_aux lp lv f =
    match f.t_node with
    | Tbinop (Timplies, f1, f2) ->
        intros_aux (f1 :: lp) lv f2
    | Tquant (Tforall, fq) ->
        let vsl, _, fs = t_open_quant fq in
        intros_aux lp (lv @ vsl) fs
    | _ -> (lp, lv, f) in
  intros_aux [] [] f

let term_decl d =
  match d.td_node with
  | Decl ({d_node = Dprop (_pk, _pr, t)}) -> t
  | _ -> raise (Arg_trans "term_decl")

let pr_prsymbol pr =
  match pr with
  | Decl {d_node = Dprop (_pk, pr, _t)} -> Some pr
  | _ -> None

(* Looks for the hypothesis name and return it. If not found return None *)
let find_hypothesis (name:Ident.ident) task =
  let ndecl = ref None in
  let _ = task_iter (fun x -> if (
    match (pr_prsymbol x.td_node) with
    | None -> false
    | Some pr -> Ident.id_equal pr.pr_name name) then ndecl := Some x) task in
  !ndecl

(* [with_terms subst_ty subst lv wt]: Takes the list of variables in lv that are
   not part of the substitution and try to match them with the list of values
   from wt (ordered). *)
(* TODO we could use something simpler than first_order_matching here. *)
let with_terms ~trans_name subst_ty subst lv withed_terms =
  Debug.dprintf debug_matching "Calling with_terms@.";
  (* Get the list of variables of lv that are not in subst. *)
  let lv, slv = List.fold_left (fun (acc, accs) v ->
    match (Mvs.find v subst) with
    | _ -> acc, accs
    | exception Not_found -> t_var v :: acc, Svs.add v accs) ([], Svs.empty) lv
  in
  let lv = List.rev lv in

  (* Length checking for nice errors *)
  let diff = Svs.cardinal slv - List.length withed_terms in
  match diff with
  | _ when diff < 0 ->
      Debug.dprintf debug_matching "Too many withed terms@.";
      raise (Arg_trans (trans_name ^ ": the last " ^
                        string_of_int (-diff)
                        ^ " terms in with are useless"))
  | _ when diff > 0 ->
      Debug.dprintf debug_matching "Not enough withed terms@.";
      raise (Arg_trans (trans_name ^ ": there are " ^
                        string_of_int diff
                        ^ " terms missing"))
  | _ (* when diff = 0 *) ->
      let new_subst_ty, new_subst =
        try first_order_matching slv lv withed_terms with
        | Reduction_engine.NoMatch (Some (t1, t2)) ->
            Debug.dprintf debug_matching "Term %a and %a can not be matched. Failure in matching@."
                Pretty.print_term t1 Pretty.print_term t2;
            raise (Arg_trans_term (trans_name, t1, t2))
        | Reduction_engine.NoMatchpat (Some (p1, p2)) ->
            Debug.dprintf debug_matching "Term %a and %a can not be matched. Failure in matching@."
              Pretty.print_pat p1 Pretty.print_pat p2;
            raise (Arg_trans_pattern (trans_name, p1, p2))
        | Reduction_engine.NoMatch None ->
            Debug.dprintf debug_matching "with_terms: No match@.";
            raise (Arg_trans trans_name)
      in
      let subst_ty = Ty.Mtv.union
          (fun _x y z ->
            if Ty.ty_equal y z then
              Some y
            else
              raise (Arg_trans_type (trans_name ^ ": ", y, z)))
          subst_ty new_subst_ty
      in
      let subst =
        Mvs.union (fun _x y z ->
          if Term.t_equal_nt_nl y z then
            Some y
          else
            raise (Arg_trans_term (trans_name ^ ": ", y, z)))
          subst new_subst
      in
      subst_ty, subst

(* This function first try to match left_term and right_term with a substitution
   on lv/slv. It then tries to fill the holes with the list of withed_terms.
   trans_name is used for nice error messages. Errors are returned when the size
   of withed_terms is incorrect.
*)
(* TODO Having both slv and lv is redundant but we need both an Svs and the
   order of elements: to be improved.
*)
let matching_with_terms ~trans_name slv lv left_term right_term withed_terms =
  let (subst_ty, subst) =
    try first_order_matching slv [left_term] [right_term] with
    | Reduction_engine.NoMatch (Some (t1, t2)) ->
      Debug.dprintf debug_matching
        "Term %a and %a can not be matched. Failure in matching@."
        Pretty.print_term t1 Pretty.print_term t2;
      raise (Arg_trans_term (trans_name, t1, t2))
    | Reduction_engine.NoMatchpat (Some (p1, p2)) ->
      Debug.dprintf debug_matching
        "Term %a and %a can not be matched. Failure in matching@."
        Pretty.print_pat p1 Pretty.print_pat p2;
      raise (Arg_trans_pattern (trans_name, p1, p2))
    | Reduction_engine.NoMatch None -> raise (Arg_trans trans_name)
  in
  let subst_ty, subst =
    let withed_terms = match withed_terms with None -> [] | Some l -> l in
    with_terms ~trans_name subst_ty subst lv withed_terms
  in
  subst_ty, subst

(* Apply:
   1) takes the hypothesis and introduce parts of it to keep only the last
      element of the implication. It gathers the premises and variables in a
      list.
   2) try to find a good substitution for the list of variables so that last
      element of implication is equal to the goal.
   3) generate new goals corresponding to premises with variables instantiated
      with values found in 2).
 *)
let apply pr withed_terms : Task.task Trans.tlist = Trans.store (fun task ->
  let name = pr.pr_name in
  let g, task = Task.task_separate_goal task in
  let g = term_decl g in
  let d = find_hypothesis name task in
  if d = None then raise (Arg_error "apply");
  let d = Opt.get d in
  let t = term_decl d in
  let (lp, lv, nt) = intros t in
  let slv = List.fold_left (fun acc v -> Svs.add v acc) Svs.empty lv in
  match matching_with_terms ~trans_name:"apply" slv lv nt g withed_terms with
  | exception e -> raise e
  | subst_ty, subst ->
      let inst_nt = t_ty_subst subst_ty subst nt in
      if (Term.t_equal_nt_nl inst_nt g) then
        let nlp = List.map (t_ty_subst subst_ty subst) lp in
        List.map (fun ng -> Task.add_decl task
              (create_prop_decl Pgoal (create_prsymbol (gen_ident "G")) ng)) nlp
      else
        raise (Arg_trans_term ("apply", inst_nt, g)))

let replace rev f1 f2 t =
  match rev with
  | true -> replace_in_term f1 f2 t
  | false -> replace_in_term f2 f1 t

(* Generic fold to be put in Trans ? TODO *)
let fold (f: decl -> 'a -> 'a) (acc: 'a): 'a Trans.trans =
  Trans.fold (fun t acc -> match t.task_decl.td_node with
  | Decl d -> f d acc
  | _ -> acc) acc

(* - If f1 unifiable to t with substitution s then return s.f2 and replace every
     occurences of s.f1 with s.f2 in the rest of the term
   - Else call recursively on subterms of t *)
(* If a substitution s is found then new premises are computed as e -> s.e *)
let replace_subst lp lv f1 f2 withed_terms t =
  (* is_replced is common to the whole execution of replace_subst. Once an
     occurence is found, it changes to Some (s) so that only one instanciation
     is rewrritten during execution *)

  (* first_order_matching requires an Svs but we still need the order in
     with_terms. *)
  let slv = List.fold_left (fun acc v -> Svs.add v acc) Svs.empty lv in

  let rec replace is_replaced f1 f2 t : _ * Term.term =
    match is_replaced with
    | Some(subst_ty,subst) ->
        is_replaced, replace_in_term (t_ty_subst subst_ty subst f1) (t_ty_subst subst_ty subst f2) t
    | None ->
      begin
        (* Catch any error from first_order_matching or with_terms. *)
        match matching_with_terms ~trans_name:"rewrite" slv lv f1 t (Some withed_terms) with
        | exception _e ->
            Term.t_map_fold
                (fun is_replaced t -> replace is_replaced f1 f2 t)
                is_replaced t
        | subst_ty, subst ->
              let sf1 = t_ty_subst subst_ty subst f1 in
              if (Term.t_equal_nt_nl sf1 t) then
                Some (subst_ty, subst), t_ty_subst subst_ty subst f2
              else
                t_map_fold (fun is_replaced t -> replace is_replaced f1 f2 t)
                  is_replaced t
      end
  in

  let is_replaced, t =
    replace None f1 f2 t in
  match is_replaced with
  | None -> raise (Arg_trans "rewrite: no term matching the given pattern")
  | Some(subst_ty,subst) ->
      (List.map (t_ty_subst subst_ty subst) lp, t)

let rewrite_in rev with_terms h h1 =
  let found_eq =
    (* Used to find the equality we are rewriting on *)
    (* TODO here should fold with a boolean stating if we found equality yet to
       not go through all possible hypotheses *)
    fold (fun d acc ->
      match d.d_node with
      | Dprop (Paxiom, pr, t) when Ident.id_equal pr.pr_name h.pr_name ->
          let lp, lv, f = intros t in
          let t1, t2 = (match f.t_node with
          | Tapp (ls, [t1; t2]) when ls_equal ls ps_equ ->
              (* Support to rewrite from the right *)
              if rev then (t1, t2) else (t2, t1)
          | Tbinop (Tiff, t1, t2) ->
              (* Support to rewrite from the right *)
              if rev then (t1, t2) else (t2, t1)
          | _ -> raise (Arg_bad_hypothesis ("rewrite", f))) in
          Some (lp, lv, t1, t2)
      | _ -> acc) None in
  (* Return instantiated premises and the hypothesis correctly rewritten *)
  let lp_new found_eq =
    match found_eq with
    | None -> raise (Arg_error "rewrite")
    | Some (lp, lv, t1, t2) ->
      fold (fun d acc ->
        match d.d_node with
        | Dprop (p, pr, t)
            when (Ident.id_equal pr.pr_name h1.pr_name &&
                 (p = Paxiom || p = Pgoal)) ->
          let lp, new_term = replace_subst lp lv t1 t2 with_terms t in
            Some (lp, create_prop_decl p pr new_term)
        | _ -> acc) None in
  (* Pass the premises as new goals. Replace the former toberewritten
     hypothesis to the new rewritten one *)
  let recreate_tasks lp_new =
    match lp_new with
    | None -> raise (Arg_trans "recreate_tasks")
    | Some (lp, new_term) ->
      let trans_rewriting =
        Trans.decl (fun d -> match d.d_node with
        | Dprop (p, pr, _t)
            when (Ident.id_equal pr.pr_name h1.pr_name &&
                 (p = Paxiom || p = Pgoal)) ->
          [new_term]
        | _ -> [d]) None in
      let list_par =
        List.map
          (fun e ->
            Trans.decl (fun d -> match d.d_node with
            | Dprop (p, pr, _t)
              when (Ident.id_equal pr.pr_name h1.pr_name &&
                    p = Paxiom) ->
                [d]
            | Dprop (Pgoal, _, _) ->
                [create_prop_decl Pgoal (Decl.create_prsymbol (gen_ident "G")) e]
            | _ -> [d] )
          None) lp in
      Trans.par (trans_rewriting :: list_par) in

  (* Composing previous functions *)
  Trans.bind (Trans.bind found_eq lp_new) recreate_tasks

let rewrite_list opt rev with_terms hl h1 =
  let found_decl =
    fold (fun d (ok,acc) ->
        if ok then (ok,acc)
        else
          match d.d_node with
          | Dprop (p, pr, t)
               when (Ident.id_equal pr.pr_name h1.pr_name &&
                     (p = Paxiom || p = Pgoal)) ->
             (true,Some (p,pr,t))
          | _ -> (ok, acc)) (false, None) in
  let found_term = Trans.bind found_decl
                     (fun (_, od) -> Trans.store (fun _ ->
                        match od with
                        | Some (_,_,t) -> ([],t)
                        | None -> raise (Arg_error "rewrite"))) in
  let do_h h (lp, term) =
    (* Used to find the equality we are rewriting on *)
    (* TODO here should fold with a boolean stating if we found equality yet to
       not go through all possible hypotheses *)
    fold (fun d (acclp,accterm) ->
      match d.d_node with
      | Dprop (Paxiom, pr, t) when Ident.id_equal pr.pr_name h.pr_name ->
          let lp, lv, f = intros t in
          let t1, t2 = (match f.t_node with
          | Tapp (ls, [t1; t2]) when ls_equal ls ps_equ ->
              (* Support to rewrite from the right *)
              if rev then (t1, t2) else (t2, t1)
          | Tbinop (Tiff, t1, t2) ->
              (* Support to rewrite from the right *)
              if rev then (t1, t2) else (t2, t1)
          | _ -> raise (Arg_bad_hypothesis ("rewrite", f))) in
          let new_lp, new_term =
            if opt
            then try replace_subst lp lv t1 t2 with_terms accterm
                 with Arg_trans _ -> (acclp, accterm)
            else replace_subst lp lv t1 t2 with_terms accterm in
       new_lp@acclp, new_term
      | _ -> (acclp, accterm)) (lp, term) in
  let do_all = List.fold_left (fun acc h -> Trans.bind acc (do_h h)) found_term hl in
  (* Pass the premises as new goals. Replace the former toberewritten
     hypothesis to the new rewritten one *)
  let recreate_tasks (lp, term) =
    let trans_rewriting =
      Trans.decl (fun d -> match d.d_node with
      | Dprop (p, pr, _t)
         when (Ident.id_equal pr.pr_name h1.pr_name &&
               (p = Paxiom || p = Pgoal)) ->
         [create_prop_decl p pr term]
      | _ -> [d]) None in
    let list_par =
      List.map
        (fun e ->
            Trans.decl (fun d -> match d.d_node with
            | Dprop (p, pr, _t)
              when (Ident.id_equal pr.pr_name h1.pr_name &&
                    p = Paxiom) ->
                [d]
            | Dprop (Pgoal, _, _) ->
                [create_prop_decl Pgoal (Decl.create_prsymbol (gen_ident "G")) e]
            | _ -> [d] )
          None) lp in
    Trans.par (trans_rewriting :: list_par) in
  Trans.bind do_all recreate_tasks

let find_target_prop h : prsymbol trans =
  Trans.store (fun task ->
               match h with
                 | Some pr -> pr
                 | None -> Task.task_goal task)

let rewrite with_terms rev h h1 =
  let with_terms =
    match with_terms with
    | None -> []
    | Some l -> l
  in
  Trans.bind (find_target_prop h1) (rewrite_in (not rev) with_terms h)

let rewrite_list with_terms rev opt hl h1 =
  let with_terms =
    match with_terms with
    | None -> []
    | Some l -> l
  in
  Trans.bind (find_target_prop h1) (rewrite_list opt (not rev) with_terms hl)

(* This function is used to detect when we found the hypothesis/goal we want
   to replace/unfold into. *)
let detect_prop pr k h =
  match h with
  | None -> k = Pgoal
  | Some h -> Ident.id_equal pr.pr_name h.pr_name && (k = Paxiom || k = Pgoal)

let detect_prop_list pr k hl =
  match hl with
  | None -> k = Pgoal
  | Some [] -> (* Should not be able to parse the empty list *)
      raise (Arg_trans "replace")
  | Some hl ->
      ((List.exists (fun h -> Ident.id_equal pr.pr_name h.pr_name) hl)
         && (k = Paxiom || k = Pgoal))

(* Replace occurences of t1 with t2 in h. When h is None, the default is to
   replace in the goal.
*)
let replace t1 t2 hl =
  if not (Ty.ty_equal (t_type t1) (t_type t2)) then
    raise (Arg_trans_term ("replace", t1, t2))
  else
    (* Create a new goal for equality of the two terms *)
    let g = Decl.create_prop_decl Decl.Pgoal (create_prsymbol (gen_ident "G")) (t_app_infer ps_equ [t1; t2]) in
    let ng = Trans.goal (fun _ _ -> [g]) in
    let g = Trans.decl (fun d ->
      match d.d_node with
      | Dprop (p, pr, t) when detect_prop_list pr p hl ->
          [create_prop_decl p pr (replace true t1 t2 t)]
      | _ -> [d]) None in
    Trans.par [g; ng]


let t_replace_app unf ls_defn t =
  let (vl, tls) = ls_defn in
  match t.t_node with
  | Tapp (ls, tl) when ls_equal unf ls ->
     let add (mt,mv) x y =
       Ty.ty_match mt x.vs_ty (t_type y), Mvs.add x y mv
     in
     let mtv,mvs =
       List.fold_left2 add (Ty.Mtv.empty,Mvs.empty) vl tl
     in
     let mtv = Ty.oty_match mtv tls.t_ty t.t_ty in
     t_ty_subst mtv mvs tls
  | _ -> t

let rec t_ls_replace ls ls_defn t =
  t_replace_app ls ls_defn (t_map (t_ls_replace ls ls_defn) t)

let unfold unf hl =
  let r = ref None in
  Trans.decl
    (fun d ->
      match d.d_node with
        (* Do not work on mutually recursive functions *)
      | Dlogic [(ls, ls_defn)] when ls_equal ls unf ->
          r := Some (open_ls_defn ls_defn);
          [d]
      | Dprop (k, pr, t) when detect_prop_list pr k hl ->
        begin
          match !r with
          | None -> [d]
          | Some ls_defn ->
              let t = t_ls_replace unf ls_defn t in
              let new_decl = create_prop_decl k pr t in
              [new_decl]
        end
      | _ -> [d]) None

(* This found any equality which at one side contains a single lsymbol and is
   local. It gives same output as found_eq. *)
let find_eq2 is_local_decl =
    fold (fun d acc ->
      match d.d_node with
      | Dprop (k, pr, t) when k != Pgoal && is_local_decl d ->
        begin
          let acc = (match t.t_node with
          | Tapp (ls, [t1; t2]) when ls_equal ls ps_equ ->
            (match t1.t_node, t2.t_node with
            | Tapp (_, []), _ ->
                Some (Some pr, t1, t2)
            | _, Tapp (_, []) ->
                Some (Some pr, t2, t1)
            | _ -> acc)
          | _ -> acc) in
          acc
        end
      | Dlogic [(ls, ld)] when is_local_decl d ->
        (* Function without arguments *)
        let vl, e = open_ls_defn ld in
        if vl = [] then
          Some (None, t_app_infer ls [], e)
        else
          acc
      | _ -> acc) None

let subst_eq found_eq =
  match found_eq with
    | None -> raise (Arg_trans "subst_eq")
    | Some (Some pr_eq, t1, t2) ->
      begin
        Trans.decl (fun d ->
          match d.d_node with
          (* Remove equality over which we subst *)
          | Dprop (_k, pr, _t) when pr_equal pr pr_eq  ->
            []
          (* Replace in all hypothesis *)
          | Dprop (kind, pr, t) ->
            [create_prop_decl kind pr (t_replace t1 t2 t)]
          | Dlogic ldecl_list ->
            let ldecl_list =
              List.map (fun (ls, ls_def) ->
                let (vl, t) = open_ls_defn ls_def in
                make_ls_defn ls vl (t_replace t1 t2 t)) ldecl_list
            in
            [create_logic_decl ldecl_list]

          (* TODO unbelievably complex for something that simple... *)
          | Dind ((is: ind_sign), (ind_list: ind_decl list)) ->
            let ind_list: ind_decl list =
              List.map (fun ((ls: lsymbol), (idl: (prsymbol * term) list)) ->
                let idl = List.map (fun (pr, t) -> (pr, t_replace t1 t2 t)) idl in
                (ls, idl)) ind_list
            in
            [create_ind_decl is ind_list]

          | Dtype _ | Ddata _ | Dparam _ -> [d]) None
      end
    | Some (None, t1, t2) ->
      begin
         Trans.decl (fun d ->
           match d.d_node with
           | Dlogic [(ls, _ld)] when try (t1 = Term.t_app_infer ls []) with _ -> false ->
              []
           (* Replace in all hypothesis *)
           | Dprop (kind, pr, t) ->
             [create_prop_decl kind pr (t_replace t1 t2 t)]

          | Dlogic ldecl_list ->
            let ldecl_list =
              List.map (fun (ls, ls_def) ->
                let (vl, t) = open_ls_defn ls_def in
                make_ls_defn ls vl (t_replace t1 t2 t)) ldecl_list
            in
            [create_logic_decl ldecl_list]

          (* TODO unbelievably complex for something that simple... *)
          | Dind ((is: ind_sign), (ind_list: ind_decl list)) ->
            let ind_list: ind_decl list =
              List.map (fun ((ls: lsymbol), (idl: (prsymbol * term) list)) ->
                let idl = List.map (fun (pr, t) -> (pr, t_replace t1 t2 t)) idl in
                (ls, idl)) ind_list
            in
            [create_ind_decl is ind_list]

          | Dtype _ | Ddata _ | Dparam _ -> [d]) None
       end

let subst_eq_list (found_eq_list, _) =
  List.fold_left (fun acc_tr found_eq ->
    Trans.compose (subst_eq found_eq) acc_tr) Trans.identity found_eq_list

let subst_all (is_local_decl: Decl.decl -> bool) =
   Trans.bind (find_eq2 is_local_decl) subst_eq

let return_local_decl task =
  let decl_list = get_local_task task in
  let is_local_decl d = List.exists (fun x -> Decl.d_equal d x) decl_list in
  is_local_decl

let return_local_decl = Trans.store return_local_decl

let subst_all = Trans.bind return_local_decl subst_all

let rec repeat f task =
  try
    let new_task = Trans.apply f task in
    (* TODO this is probably expansive. Use a checksum or an integer ? *)
    if Task.task_equal new_task task then
      raise Exit
    else
      repeat f new_task
  with
  | _ -> task

let repeat f = Trans.store (repeat f)

let subst_all = repeat subst_all

(* TODO implement subst_all as repeat subst ??? *)

let () =
  wrap_and_register ~desc:"substitute all ident equalities and remove them"
    "subst_all"
    (Ttrans) subst_all

let () = wrap_and_register ~desc:"sort declarations"
    "sort"
    (Ttrans) sort

let () = wrap_and_register ~desc:"unfold ls [in] pr: unfold logic symbol ls in list of hypothesis pr. The argument in is optional: by default unfold in the goal." (* TODO *)
    "unfold"
    (Tlsymbol (Topt ("in", Tprlist Ttrans))) unfold

let () = wrap_and_register
    ~desc:"replace <term1> <term2> [in] <name list> replaces occcurences of term1 by term2 in prop name. If no list is given, replace in the goal."
    "replace"
    (Tterm (Tterm (Topt ("in", Tprlist Ttrans_l)))) replace

let _ = wrap_and_register
    ~desc:"rewrite [<-] <name> [in] <name2> [with] <list term> rewrites equality defined in name into name2 using exactly all terms of the list as instance for what cannot be deduced directly" "rewrite"
    (Toptbool ("<-",(Tprsymbol (Topt ("in", Tprsymbol (Topt ("with", Ttermlist Ttrans_l))))))) (fun rev h h1opt term_list -> rewrite term_list rev h h1opt)

let _ = wrap_and_register
    ~desc:"rewrite_list [<-] <list name> [?] [in] <name2> [with] <list term> rewrites equalities defined in <list name> into name2 using exactly all terms of the list as instance for what cannot be deduced directly. If [?] is set, each of the rewrites is optional." "rewrite_list"
    (Toptbool ("<-", (Tprlist (Toptbool ("?", Topt ("in",  Tprsymbol (Topt ("with", Ttermlist Ttrans_l)))))))) (fun rev hl opt h1opt term_list -> rewrite_list term_list rev opt hl h1opt)

let () = wrap_and_register
    ~desc:"apply <prop> [with] <list term> applies prop to the goal and \
uses the list of terms to instantiate the variables that are not found." "apply"
    (Tprsymbol (Topt ("with", Ttermlist Ttrans_l))) (fun x y -> apply x y)


(*********)
(* Subst *)
(*********)

(* Creation of as structure that associates the replacement of terms as a
   function of the
*)
type constant_subst_defining =
  | Cls of lsymbol
  | Cpr of prsymbol

module Csd = Stdlib.MakeMSHW (struct
  type t = constant_subst_defining
  let tag (c: t) = match c with
  | Cls ls -> ls.ls_name.Ident.id_tag
  | Cpr pr -> pr.pr_name.Ident.id_tag
end)

module Mcsd = Csd.M

(* We find the hypotheses that have a substitution equality for elements of the
   to_subst list. We check that we never take more than one equality per
   lsymbol to substitute.
*)
let find_eq_aux (to_subst: Term.lsymbol list) =
  fold (fun d (acc, used) ->
    match d.d_node with
    | Dprop (k, pr, t) when k != Pgoal ->
        let acc, used = (match t.t_node with
        | Tapp (ls, [t1; t2]) when ls_equal ls ps_equ ->
          (* Allow to rewrite from the right *)
          begin
            match t1.t_node, t2.t_node with
            | Tapp (ls, []), _ when List.exists (ls_equal ls) to_subst &&
                                    (* Check ls is not already taken *)
                                    not (List.exists (ls_equal ls) used) ->
                Mcsd.add (Cpr pr) (t1, t2) acc, ls :: used
            | _, Tapp (ls, []) when List.exists (ls_equal ls) to_subst &&
                                    (* Check ls is not already taken *)
                                    not (List.exists (ls_equal ls) used) ->
                Mcsd.add (Cpr pr) (t2, t1) acc, ls :: used
            | _ -> acc, used
          end
        | _ -> acc, used) in
        acc, used
    | Dlogic [(ls, ld)] when List.exists (ls_equal ls) to_subst &&
                             (* Check ls is not already taken *)
                             not (List.exists (ls_equal ls) used) ->
      (* Function without arguments *)
      let vl, e = open_ls_defn ld in
      if vl = [] then
        Mcsd.add (Cls ls) (t_app_infer ls [], e) acc, ls :: used
      else
        acc, used
    | _ -> acc, used) (Mcsd.empty,[])

(* Wrap-around function to parse lsymbol instead of terms *)
let find_eq to_subst =
  let to_subst = (List.map
     (fun t -> match t.t_node with
     | Tapp (ls, []) -> ls
     | _ -> raise (Arg_trans "subst_eq")) to_subst)
  in
  find_eq_aux to_subst

(* This produce an ordered list of tdecl which is the original task minus the
   hypotheses/constants that were identified for substitution.
   This shall be done on tdecl.
*)
let remove_hyp_and_constants (replacing_hyps, used_ls) =
  (* The task_fold on tdecl is necessary as we *need* all the tdecl (in
     particular to identify local decls).
  *)
  Task.task_fold (fun (subst, list_tdecl) td ->
    match td.td_node with
    | Decl d ->
      begin
        match d.d_node with
        | Dprop (kind, pr, _t) when kind != Pgoal &&
                                    Mcsd.mem (Cpr pr) replacing_hyps ->
          let from_t, to_t = Mcsd.find (Cpr pr) replacing_hyps in
          (* TODO find a way to be more efficient than this *)
          let to_t = Generic_arg_trans_utils.replace_subst subst to_t in
          Mterm.add from_t to_t subst, list_tdecl
        | Dlogic [ls, _] when Mcsd.mem (Cls ls) replacing_hyps ->
          let from_t, to_t = Mcsd.find (Cls ls) replacing_hyps in
          (* TODO find a way to be more efficient than this *)
          let to_t = Generic_arg_trans_utils.replace_subst subst to_t in
          Mterm.add from_t to_t subst, list_tdecl
        | Dparam ls when List.exists (ls_equal ls) used_ls ->
          subst, list_tdecl
        | _ ->
          subst, (replace_tdecl subst td :: list_tdecl)
      end
    | _ -> (subst, td :: list_tdecl)
    ) (Mterm.empty, [])

let remove_hyp_and_constants (replacing_hyps, used_ls) =
  Trans.store (remove_hyp_and_constants (replacing_hyps, used_ls))

let is_goal td =
  match td.td_node with
  | Decl d ->
      begin
        match d.d_node with
        | Dprop (Pgoal, _, _) -> true
        | _ -> false
      end
  | _ -> false

(* Use the list of tdecl that should be able to be readded into a task if there
   was sufficiently few things that were removed to the task.
   To do this, we use Task.add_tdecl (because we think its the safest).
   Note that we also try to keep the order of the declarations (because
   usability). So, each time we add a new declaration, we try to add all the
   transformations that failed (supposedly because they use a variable declared
   after it).
*)
let readd_decls (list_decls, subst: tdecl list * _) =
  List.fold_left (fun (task_uc, list_to_add) (d: tdecl) ->
    let d = replace_tdecl subst d in
    let task_uc, list_to_add =
      List.fold_left (fun (task_uc, list_to_add) (d: tdecl) ->
        try
          let new_task_uc = Task.add_tdecl task_uc d in
          new_task_uc, list_to_add
        with
          (* TODO find all possible exceptions here *)
          _ -> task_uc, d :: list_to_add)
        (task_uc, []) list_to_add
    in
    (* We always need to add the goal last *)
    if is_goal d then
      if list_to_add != [] then
        raise (Arg_trans_decl ("subst_eq", list_to_add))
      else
        try
          (Task.add_tdecl task_uc d, [])
        with
        (* TODO find all possible exceptions here *)
          _ -> raise (Arg_trans_decl ("subst_eq", [d]))
    else
      try
        (Task.add_tdecl task_uc d, List.rev list_to_add)
      with
        _ -> (task_uc, List.rev (d :: list_to_add)))
    (None, []) list_decls

let readd_decls (subst, list_decls) =
  let (task, _l) = readd_decls (list_decls, subst) in
  Trans.return task

let find args = Trans.bind (find_eq args) remove_hyp_and_constants

let subst args = Trans.bind (find args) readd_decls

let () = wrap_and_register ~desc:"remove a literal using an equality on it"
    "subst"
    (Ttermlist Ttrans) subst
