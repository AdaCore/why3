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
open Ty
open Term
open Ident
open Intro_projections_counterexmp

(** For see intro_vc_vars_counterexmp.mli for detailed description
    of this transformation. *)

let meta_vc_location =
  Theory.register_meta_excl "vc_location" [Theory.MTstring]
  ~desc:"Location@ of@ the@ term@ that@ triggers@ vc@ in@ the@ form@ file:line:col."

(* Information about the term that triggers VC.  *)
type vc_term_info = {
  vc_inside : bool;
  (* true if the term that triggers VC is currently processed *)
  vc_loc : Loc.position option;
  (* the position of the term that triggers VC *)
  vc_pre_or_post : bool;
  (* true if VC was generated for precondition or postcondition *)
}

let is_model_vc_attr l =
  attr_equal l Ity.annot_attr || attr_equal l model_vc_post_attr

let check_enter_vc_term t info vc_loc =
  (* Check whether the term that triggers VC is entered.
     If it is entered, extract the location of the term and if the VC is
     postcondition or precondition of a function, extract the name of
     the corresponding function.
  *)
  if Sattr.exists is_model_vc_attr t.t_attrs then
    begin
      vc_loc := t.t_loc;
      { vc_inside = true;
        vc_loc = t.t_loc;
        vc_pre_or_post = Sattr.mem model_vc_post_attr t.t_attrs }
    end
  else
    info

(* Preid table necessary to avoid duplication of *_vc_constant *)
module Hprid = Exthtbl.Make (struct
  type t = preid
  let equal x y = x.pre_name = y.pre_name && Sattr.equal x.pre_attrs y.pre_attrs
  let hash p = Exthtbl.hash p
end)

let same_line_loc loc1 loc2 =
  match loc1, loc2 with
  | Some loc1, Some loc2 ->
      let (f1, l1, _, _) = Loc.get loc1 in
      let (f2, l2, _, _) = Loc.get loc2 in
      f1 = f2 && l1 = l2
  | _ -> false

let same_line_locs loc1 ls =
  let is_same =
    match ls.id_loc with
    | Some loc when same_line_loc (Some loc) loc1 -> true
    | _ -> false
  in
  is_same ||
  Sattr.exists (fun x ->
      let loc = extract_written_loc x in
      same_line_loc loc loc1) ls.id_attrs

let add_model_trace_attr name attrs =
  if Sattr.exists is_model_trace_attr attrs then
    attrs
  else
    let mt_attr = create_attribute ("model_trace:" ^ name) in
    Sattr.add mt_attr attrs

(*  Used to generate duplicate vc_constant and axioms for counterex generation.
    This function is always called when the term is in negative position or
    under a positive term that is not introducible. This means it never change the
    goal.

    @param info used to know if the current term is under a vc_attr
    @param vc_loc is the location of the vc_attr (returned value)
    @param vc_map is a container for generated vc_constant id (used to avoid duplication)
    @param vc_var contains the variables we can safely use as CE (ie: we introduced these)
    @param t: current subterm of the goal
    @return list of declarations added by do_intro
 *)
let rec do_intro info vc_loc vc_map vc_var t =
  let info = check_enter_vc_term t info vc_loc in
  let do_intro = do_intro info vc_loc vc_map vc_var in

  (* Do the necessary machinery to add a printable counterexample when encountered
     (variable or function without arguments) *)
  let new_counter_example_variable ls info =
    if info.vc_inside then begin
      match info.vc_loc with
      | None -> []
      | Some loc when not (same_line_locs info.vc_loc ls) ->
          (* variable inside the term T that triggers VC. If the variable
             should be in counterexample, introduce new constant in location
             loc with all attributes necessary for collecting it for
             counterexample and make it equal to the variable *)
          if relevant_for_counterexample ls then
            begin
              let const_attr = ls.id_attrs in
              let const_name = ls.id_string^"_vc_constant" in
              let axiom_name = ls.id_string^"_vc_axiom" in
              let labels_attr =
                Sattr.filter (fun x ->
                    Strings.has_prefix "at:" x.attr_string)
                  t.t_attrs
              in
              let const_attr = Sattr.union const_attr labels_attr in
              let const_attr = add_model_trace_attr ls.id_string const_attr in
              (* Create a new id here to check the couple name, location. *)
              let id_new = Ident.id_user ~attrs:const_attr const_name loc in
              (* The following check is used to avoid duplication of
                 *_vc_constant_n.  We keep track of the preids that have already
                 been duplicated in vc_map.  Note that we need to do it before
                 these preid are casted to lsymbol (by Term.create_lsymbol)
                 because those integrates a unique hash that would make
                 identical preid different lsymbol *)
              if (Hprid.mem vc_map id_new) then
                []
              else
                begin
                  Hprid.add vc_map id_new true;
                  intro_const_equal_to_term
                    ~term:t ~id_new:id_new ~axiom_name
                end
            end
          else
            []
      | _ -> []
    end
    else [] in

  match t.t_node with
  | Tapp (ls, tl) ->
    begin
      match tl with
      | [] ->
        new_counter_example_variable ls.ls_name info
      | _ ->
        List.fold_left
            (fun defs term ->
              List.append defs (do_intro term))
            []
            tl
    end
  | Tvar v ->
    if (Hvs.mem vc_var v) then
      new_counter_example_variable v.vs_name info
    else
      []
  | Tbinop (_, f1, f2) ->
      List.append (do_intro f1) (do_intro f2)
  | Tquant (_, fq) ->
    let _, _, f = t_open_quant fq in
    do_intro f
  | Tlet (t, tb) ->
    let _, f = t_open_bound tb in
    List.append (do_intro t) (do_intro f)
  | Tnot f ->
    do_intro f
  | Tif (f1, f2, f3) ->
    List.append
      (List.append (do_intro f1) (do_intro f2))
        (do_intro f3)
  | Tcase (t, _) ->
    do_intro t
    (* todo: handle the second argument of Tcase *)
  | Tconst _ -> []
  | Ttrue -> []
  | Tfalse -> []
  | Teps _ -> []

(* Meant to remove foralls in positive positions (not necessarily in top
   position). vc_var is the set of variables we already introduced. *)
let rec remove_positive_foralls vc_var f =
  match f.t_node with
  | Tbinop (Timplies,f1,f2) ->
      let (decl, fres) = remove_positive_foralls vc_var f2 in
      (decl, t_implies f1 fres)
(*  | Tbinop (Tor, f1, f2) ->
      let (decl1, fres1) = remove_positive_foralls vc_var f1 in
      let (decl2, fres2) = remove_positive_foralls vc_var f2 in
      (decl1 @ decl2, t_or fres1 fres2)*)
  | Tbinop (Tand, f1, f2) ->
      let (decl1, fres1) = remove_positive_foralls vc_var f1 in
      let (decl2, fres2) = remove_positive_foralls vc_var f2 in
      (decl1 @ decl2, t_and fres1 fres2)
  | Tquant (Tforall, fq) ->
      let vsl,_trl,f_t = t_open_quant fq in
      let intro_var subst vs =
        let ls = create_lsymbol (id_clone vs.vs_name) [] (Some vs.vs_ty) in
        Hvs.add vc_var vs true;
        Mvs.add vs (fs_app ls [] vs.vs_ty) subst,
        create_param_decl ls
      in
      let subst, dl = Lists.map_fold_left intro_var Mvs.empty vsl in
      let f = t_attr_copy f (t_subst subst f_t) in
      let decl, goal = remove_positive_foralls vc_var f in
      (dl @ decl, goal)
  | _ -> ([], f)


(*  Introduces foralls, lets, and implications at the head of the goal.  When
    under a vc_attr, it can make calls to do_intros which creates new
    declarations for counterexample generation.  When no more intros are
    possible, it calls remove_positive_foralls which do an experimental
    introduction of foralls even under another constructs (example: H /\ forall
    i. P(i) yields (i, H /\ P(i)).  Note that it seems difficult and "unsafe"
    to merge these two functions

    It is adapted from transform/introduce.ml. (we mainly added do_intros calls
    and removed split optimizations.

    @param info used to know if the current term is under a vc_attr
    @param vc_loc is the location of the vc_attr (returned value)
    @param vc_map is a container for generated vc_constant id
    (used to avoid duplication)
    @param vc_var current set of variables we introduced
    @param f current goal
    @return pair of the declarations introduced and the modified goal. *)
let rec intros info vc_loc vc_map vc_var f =
  let info = check_enter_vc_term f info vc_loc in
  let intros = intros info vc_loc vc_map vc_var in
  match f.t_node with
  | Tbinop (Timplies,f1,f2) ->
      let f2 = t_attr_copy f f2 in
      let l = if info.vc_inside then do_intro info vc_loc vc_map vc_var f1 else [] in
      let id = create_prsymbol (id_fresh "H") in
      let d = create_prop_decl Paxiom id f1 in
      let decl, goal = intros f2 in
      (d :: l @ decl, goal)
  | Tquant (Tforall,fq) ->
      let vsl,_trl,f_t = t_open_quant fq in
      let intro_var subst vs =
        let ls = create_lsymbol (id_clone vs.vs_name) [] (Some vs.vs_ty) in
        Hvs.add vc_var vs true;
        Mvs.add vs (fs_app ls [] vs.vs_ty) subst,
        create_param_decl ls
      in
      let subst, dl = Lists.map_fold_left intro_var Mvs.empty vsl in
      (* if vs is a symbol that is tagged with a model or model_projected
         attribute, we have to allow it to be printed but it won't be
         available after its substitution *)
      (* preserve attributes and location of f *)
      let f = t_attr_copy f (t_subst subst f_t) in
      let decl, goal = intros f in
      (dl @ decl, goal)
  | Tlet (t,fb) ->
      let vs,f = t_open_bound fb in
      let ls = create_lsymbol (id_clone vs.vs_name) [] (Some vs.vs_ty) in
      let f = t_subst_single vs (fs_app ls [] vs.vs_ty) f in
      let d = create_logic_decl [make_ls_defn ls [] t] in
      (* If we are not inside a vc we don't want left side of let
         otherwise we might want it *)
      let decl, goal = intros f in
      if info.vc_inside then
        let l = do_intro info vc_loc vc_map vc_var t in
        (d :: l @ decl, goal)
      else
        (d :: decl, goal)
  | _ ->
      let (dl, goal) = remove_positive_foralls vc_var f in
      if info.vc_inside then
        let l = do_intro info vc_loc vc_map vc_var f in
        (l @ dl, goal)
      else
        (dl,goal)

let do_intro_vc_vars_counterexmp info vc_loc pr t =
  (* TODO initial guess on number of counter-examples to print *)
  let vc_map = Hprid.create 100 in
  let vc_var = Hvs.create 100 in
  let tvs = t_ty_freevars Stv.empty t in
  let mk_ts tv () = create_tysymbol (id_clone tv.tv_name) [] NoDef in
  let tvm = Mtv.mapi mk_ts tvs in
  let decls = Mtv.map create_ty_decl tvm in
  let subst = Mtv.map (fun ts -> ty_app ts []) tvm in
  let (defs_intros, t) =
    intros info vc_loc vc_map vc_var (t_ty_subst subst Mvs.empty t) in
  let defs_do_intro = do_intro info vc_loc vc_map vc_var t in
  Mtv.values decls @ defs_intros @ defs_do_intro @ [(create_prop_decl Pgoal pr t)]

let intro_vc_vars_counterexmp2 task =
  let info = {
    vc_inside = false;
    vc_loc = None;
    vc_pre_or_post = false;
  } in
  let vc_loc = ref None in
  (* Do introduction and find location of term triggering VC *)
  let do_intro_trans = Trans.goal (do_intro_vc_vars_counterexmp info vc_loc) in
  let task = (Trans.apply do_intro_trans) task in

  (* Pass meta with location of the term triggering VC to printer  *)
  let vc_loc_meta = Theory.lookup_meta "vc_location" in
  let g,task = Task.task_separate_goal task in
  let pos_str = match !vc_loc with
    | None -> ""
    | Some loc ->
      let (file, line, col1, col2) = Loc.get loc in
      Printf.sprintf "%s:%d:%d:%d" file line col1 col2
  in
  let task = Task.add_meta task vc_loc_meta [Theory.MAstr pos_str] in
  Task.add_tdecl task g

let intro_vc_vars_counterexmp = Trans.store intro_vc_vars_counterexmp2

let () = Trans.register_transform "intro_vc_vars_counterexmp"
  intro_vc_vars_counterexmp
  ~desc:"Introduce."

let get_location_of_vc task =
  let meta_args = Task.on_meta_excl meta_vc_location task in
  match meta_args with
  | Some [Theory.MAstr loc_str] ->
    (* There may be colons in the file name. We still split on the colon, look at
       the last three elements, and put the remaining ones back together to form the
       file name. We may lose colons at the beginning or end of the filename, but
       even on windows that's not allowed. *)
    let split = Strings.rev_split ':' loc_str in
    let loc =  match split with
      | col2 :: col1 :: line :: ((_ :: _) as rest) ->
        let line = int_of_string line in
        let col1 = int_of_string col1 in
        let col2 = int_of_string col2 in
        let filename = Strings.join ":" (List.rev rest) in
        Some (Loc.user_position filename line col1 col2)
      | _ -> None in
    loc
  | _ -> None
