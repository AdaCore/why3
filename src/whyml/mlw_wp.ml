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

open Wstdlib
open Ident
open Ty
open Term
open Decl
open Theory
open Mlw_ty
open Mlw_ty.T
open Mlw_expr
open Mlw_decl

let debug = Debug.register_info_flag "whyml_wp"
  ~desc:"Print@ details@ of@ verification@ conditions@ generation."

let no_track = Debug.register_flag "wp_no_track"
  ~desc:"Do@ not@ remove@ redundant@ type@ invariant@ conditions@ from@ VCs."

let no_eval = Debug.register_flag "wp_no_eval"
  ~desc:"Do@ not@ simplify@ pattern@ matching@ on@ record@ datatypes@ in@ VCs."

let lemma_label = Ident.create_label "why3:lemma"

(** Marks *)

let fresh_mark () = create_vsymbol (id_fresh "'mark") ty_mark

let fs_at =
  let ty = ty_var (create_tvsymbol (id_fresh "a")) in
  create_lsymbol (id_fresh "at") [ty; ty_mark] (Some ty)

let fs_old =
  let ty = ty_var (create_tvsymbol (id_fresh "a")) in
  create_lsymbol (id_fresh "old") [ty] (Some ty)

let mark_theory =
  let uc = create_theory ~path:["why3";"Mark"] (id_fresh "Mark") in
  let uc = add_ty_decl uc ts_mark in
  close_theory uc

let th_mark_at =
  let uc = create_theory (id_fresh "WP builtins: at") in
  let uc = use_export uc mark_theory in
  let uc = add_param_decl uc fs_at in
  close_theory uc

let th_mark_old =
  let uc = create_theory (id_fresh "WP builtins: old") in
  let uc = use_export uc th_mark_at in
  let uc = add_param_decl uc fs_old in
  close_theory uc

let fs_now = create_lsymbol (id_fresh "%now") [] (Some ty_mark)
let t_now = fs_app fs_now [] ty_mark
let e_now = e_ghost (e_lapp fs_now [] (ity_pur ts_mark []))

(* [vs_old] appears in the postconditions given to the core API,
   which expects every vsymbol to be a pure part of a pvsymbol *)
let vs_old = pv_old.pv_vs
let t_old  = t_var vs_old

let t_at_old t = t_app fs_at [t; t_old] t.t_ty

let ls_absurd = create_lsymbol (id_fresh "absurd") [] None
let t_absurd  = t_label_add Split_goal.stop_split (ps_app ls_absurd [])

let mk_t_if f = t_if f t_bool_true t_bool_false
let to_term t = if t.t_ty = None then mk_t_if t else t

(* any vs in post/xpost is either a pvsymbol or a fresh mark *)
let ity_of_vs vs =
  if Ty.ty_equal vs.vs_ty ty_mark then ity_mark else (restore_pv vs).pv_ity

(* replace every occurrence of [old(t)] with [at(t,'old)] *)
let rec remove_old f = match f.t_node with
  | Tapp (ls,[t]) when ls_equal ls fs_old -> t_at_old (remove_old t)
  | _ -> t_map remove_old f

(* replace every occurrence of [at(t,'now)] with [t] *)
let rec remove_at f = match f.t_node with
  | Tapp (ls, [t; { t_node = Tapp (fs,[]) }])
    when ls_equal ls fs_at && ls_equal fs fs_now -> remove_at t
  | _ -> t_map remove_at f

(* replace [at(t,'old)] with [at(t,lab)] everywhere in formula [f] *)
let old_mark lab t = t_subst_single vs_old (t_var lab) t

(* replace [at(t,lab)] with [at(t,'now)] everywhere in formula [f] *)
let erase_mark lab t = t_subst_single lab t_now t

(* retreat to the point of the current postcondition's ['old] *)
let backstep fn q xq =
  let lab = fresh_mark () in
  let f = fn (old_mark lab q) (Mexn.map (old_mark lab) xq) in
  erase_mark lab f

(** WP utilities *)

let default_exn_post xs _ =
  let vs = create_vsymbol (id_fresh "result") (ty_of_ity xs.xs_ity) in
  create_post vs t_true

let default_post vty ef =
  let vs = create_vsymbol (id_fresh "result") (ty_of_vty vty) in
  create_post vs t_true, Mexn.mapi default_exn_post ef.eff_raises

let wp_label ?(override=false) e f =
  let loc =
    if e.e_loc = None then f.t_loc
    else if f.t_loc = None then e.e_loc
    else if override then e.e_loc else f.t_loc
  in
  let lab = Ident.Slab.union e.e_label f.t_label in
  t_label ?loc lab f

let expl_pre       = Ident.create_label "expl:precondition"
let expl_post      = Ident.create_label "expl:postcondition"
let expl_xpost     = Ident.create_label "expl:exceptional postcondition"
let expl_assume    = Ident.create_label "expl:assumption"
let expl_assert    = Ident.create_label "expl:assertion"
let expl_check     = Ident.create_label "expl:check"
let expl_absurd    = Ident.create_label "expl:unreachable point"
let expl_type_inv  = Ident.create_label "expl:type invariant"
let expl_loop_init = Ident.create_label "expl:loop invariant init"
let expl_loop_keep = Ident.create_label "expl:loop invariant preservation"
let expl_loopvar   = Ident.create_label "expl:loop variant decrease"
let expl_variant   = Ident.create_label "expl:variant decrease"

let lab_has_expl =
  Slab.exists
    (fun l -> Strings.has_prefix "expl:" l.lab_string)

let rec wp_expl l f =
  if lab_has_expl f.t_label then f
  else match f.t_node with
    | _ when Slab.mem Split_goal.stop_split f.t_label -> t_label_add l f
    | Tbinop (Tand,f1,f2) -> t_label_copy f (t_and (wp_expl l f1) (wp_expl l f2))
    | Teps _ -> t_label_add l f (* post-condition, push down later *)
    | _ -> f

let wp_and ~sym f1 f2 =
  if sym then t_and_simp f1 f2 else t_and_asym_simp f1 f2

let wp_ands ~sym fl =
  if sym then t_and_simp_l fl else t_and_asym_simp_l fl

let wp_implies f1 f2 = t_implies_simp f1 f2

let wp_let v t f = t_let_close_simp v t f

let wp_forall vl f = t_forall_close_simp vl [] f

let is_equality_for v f = match f.t_node with
  | Tapp (ps, [{ t_node = Tvar u }; t])
    when ls_equal ps ps_equ && vs_equal u v && t_v_occurs v t = 0 ->
      Some t
  | _ ->
      None

let wp_forall_post v p f =
  (* we optimize for the case when a postcondition
     is of the form (... /\ result = t /\ ...) *)
  let rec down p = match p.t_node with
    | Tbinop (Tand,l,r) ->
        let t, l, r =
          let t, l = down l in
          if t <> None then t, l, r else
            let t, r = down r in t, l, r
        in
        t, if t = None then p else t_label_copy p (t_and_simp l r)
    | _ ->
        let t = is_equality_for v p in
        t, if t = None then p else t_true
  in
  if ty_equal v.vs_ty ty_unit then
    t_subst_single v t_void (wp_implies p f)
  else match down p with
    | Some t, p -> wp_let v t (wp_implies p f)
    | _ -> wp_forall [v] (wp_implies p f)

let t_and_subst v t1 t2 =
  (* if [t1] defines variable [v], return [t2] with [v] replaced by its
     definition. Otherwise return [t1 /\ t2] *)
  match is_equality_for v t1 with
  | Some def -> t_subst_single v def t2
  | None -> t_and_simp t1 t2

let t_implies_subst v t1 t2 =
  (* if [t1] defines variable [v], return [t2] with [v] replaced by its
     definition. Otherwise return [t1 -> t2] *)
  match is_equality_for v t1 with
  | Some def -> t_subst_single v def t2
  | None -> t_implies_simp t1 t2

let regs_of_writes eff = Sreg.union eff.eff_writes eff.eff_ghostw
let exns_of_raises eff = Sexn.union eff.eff_raises eff.eff_ghostx

let open_post q =
  let v, f = open_post q in
  v, Slab.fold wp_expl q.t_label f

let open_unit_post q =
  let v, q = open_post q in
  t_subst_single v t_void q

let create_unit_post =
  let v = create_vsymbol (id_fresh "void") ty_unit in
  fun q -> create_post v q

let vs_result e =
  create_vsymbol (id_fresh ?loc:e.e_loc "result") (ty_of_vty e.e_vty)

(** WP state *)

type wp_env = {
  prog_known : Mlw_decl.known_map;
  pure_known : Decl.known_map;
  global_env : Env.env;
  ps_int_le  : Term.lsymbol;
  ps_int_ge  : Term.lsymbol;
  ps_int_lt  : Term.lsymbol;
  ps_int_gt  : Term.lsymbol;
  fs_int_pl  : Term.lsymbol;
  fs_int_mn  : Term.lsymbol;
  letrec_var : variant list Mint.t;
}

let decrease_alg ?loc env old_t t =
  let oty = t_type old_t in
  let nty = t_type t in
  let quit () =
    Loc.errorm ?loc "no default order for %a" Pretty.print_term t in
  let ts = match oty with { ty_node = Tyapp (ts,_) } -> ts | _ -> quit () in
  let csl = Decl.find_constructors env.pure_known ts in
  if csl = [] then quit ();
  let sbs = ty_match Mtv.empty (ty_app ts (List.map ty_var ts.ts_args)) oty in
  let add_arg fty acc =
    let fty = ty_inst sbs fty in
    if ty_equal fty nty then
      let vs = create_vsymbol (id_fresh "f") nty in
      pat_var vs, t_or_simp (t_equ (t_var vs) t) acc
    else pat_wild fty, acc in
  let add_cs (cs,_) =
    let pl, f = Lists.map_fold_right add_arg cs.ls_args t_false in
    t_close_branch (pat_app cs pl oty) f in
  t_case old_t (List.map add_cs csl)

let decrease_def ?loc env old_t t =
  if ty_equal (t_type old_t) ty_int && ty_equal (t_type t) ty_int
  then t_and (ps_app env.ps_int_le [t_nat_const 0;old_t])
             (ps_app env.ps_int_lt [t;old_t])
  else decrease_alg ?loc env old_t t

let decrease loc lab env olds varl =
  let rec decr olds varl = match olds, varl with
    | (old_t, Some old_r)::olds, (t, Some r)::varl
      when oty_equal old_t.t_ty t.t_ty && ls_equal old_r r ->
        let dt = ps_app r [t; old_t] in
        t_or_simp dt (t_and_simp (t_equ old_t t) (decr olds varl))
    | (old_t, None)::olds, (t, None)::varl
      when oty_equal old_t.t_ty t.t_ty ->
        let dt = decrease_def ?loc env old_t t in
        t_or_simp dt (t_and_simp (t_equ old_t t) (decr olds varl))
    | (old_t, None)::_, (t, None)::_ ->
        decrease_def ?loc env old_t t
    | _ -> t_false
  in
  t_label ?loc lab (decr olds varl)

let expl_variant = Slab.add Split_goal.stop_split (Slab.singleton expl_variant)
let expl_loopvar = Slab.add Split_goal.stop_split (Slab.singleton expl_loopvar)

(** Reconstruct pure values after writes *)

(* The counter-example model related data needed for creating new
   variable. *)
type model_data = {
  md_append_to_model_trace : string;
    (* The string that will be appended to the end of "model_trace:" label.
       It is used to specify the reason why the variable is created. *)
  md_loc                   : Loc.position option;
    (* The location of the new variable. *)
  md_context_labels         : Slab.t option;
    (* The labels of an element that represents the context in
       that the variable is created.
       Used in SPARK branch - the SPARK locations are kept in
       labels and when a new variable is created, these location
       labels are copied from md_context_labels. *)
}

let create_model_data ?loc ?context_labels append_to_model_trace =
(* Creates new counter-example model related data.
   @param loc : the location of the new variable

   @param context_labels : The labels of an element that represents the context in that
   the variable is created.

   @param append_to_model_trace : The string that will be appended to the end of
   "model_trace:" label. It is used to specify the reason why the variable is created. *)
  {
    md_append_to_model_trace = append_to_model_trace;
    md_loc = loc;
    md_context_labels = context_labels;
  }

let create_model_data_opt ~loc ?context_labels append_to_model_trace =
  match loc with
  | None -> None
  | Some loc -> Some (create_model_data ~loc ?context_labels append_to_model_trace)

let mk_var id ty md =
  let new_labels, loc = match md with
    | None ->
      (* If there is no model data remove model labels (prevents counter-example
	 projections of this variable, displaying this variable in counterexample, ...) *)
      let new_labels = Ident.remove_model_labels ~labels:id.id_label in
      (new_labels, None)
    | Some md -> begin
        let new_labels =
          append_to_model_trace_label ~labels:id.id_label
            ~to_append:("@"^md.md_append_to_model_trace)
        in
        let new_labels = match md.md_context_labels with
          | None -> new_labels
          | Some s -> Slab.union s new_labels
        in
        (new_labels, md.md_loc)
    end
  in

  create_vsymbol (id_fresh ~label:new_labels ?loc id.id_string) ty

(* replace "contemporary" variables with fresh ones *)
let rec subst_at_now now mvs t = match t.t_node with
  | Tvar vs when now ->
      begin try t_var (Mvs.find vs mvs) with Not_found -> t end
  | Tapp (ls, _) when ls_equal ls fs_old -> assert false
  | Tapp (ls, [_; mark]) when ls_equal ls fs_at ->
      let now = match mark.t_node with
        | Tvar vs when vs_equal vs vs_old -> assert false
        | Tapp (ls,[]) when ls_equal ls fs_now -> true
        | _ -> false in
      t_map (subst_at_now now mvs) t
  | Tlet _ | Tcase _ | Teps _ | Tquant _ ->
      (* do not open unless necessary *)
      let mvs = Mvs.set_inter mvs (t_vars t) in
      if Mvs.is_empty mvs then t else
      t_map (subst_at_now now mvs) t
  | _ ->
      t_map (subst_at_now now mvs) t

(* generic expansion of an algebraic type value *)
let analyze_var fn_down fn_join lkm km vs ity =
  let var_of_fd fd =
    create_vsymbol (id_fresh "y") (ty_of_ity fd.fd_ity) in
  let branch (cs,fdl) =
    let vl = List.map var_of_fd fdl in
    let pat = pat_app cs (List.map pat_var vl) vs.vs_ty in
    let t = fn_join cs (List.map2 fn_down vl fdl) vs.vs_ty in
    t_close_branch pat t in
  let csl = Mlw_decl.inst_constructors lkm km ity in
  t_case_simp (t_var vs) (List.map branch csl)

(* given a map of modified regions, construct the updated value of [vs] *)
let update_var env (mreg : vsymbol Mreg.t) vs =
  let rec update vs { fd_ity = ity; fd_mut = mut } =
    (* are we a mutable variable? *)
    let get_vs r = Mreg.find_def vs r mreg in
    let vs = Opt.fold (fun _ -> get_vs) vs mut in
    (* should we update our value further? *)
    let check_reg r _ = reg_occurs r ity.ity_vars in
    if ity_immutable ity || not (Mreg.exists check_reg mreg) then t_var vs
    else analyze_var update fs_app env.pure_known env.prog_known vs ity in
  update vs { fd_ity = ity_of_vs vs; fd_ghost = false; fd_mut = None }

(* given a map of modified regions, update every affected variable in [f] *)
let update_term env (mreg : vsymbol Mreg.t) f =
  (* [vars] : modified variable -> updated value *)
  let update vs _ = match update_var env mreg vs with
    | { t_node = Tvar nv } when vs_equal vs nv -> None
    | t -> Some t in
  let vars = Mvs.mapi_filter update (t_vars f) in
  (* [vv'] : modified variable -> fresh variable *)
  let new_var vs _ = mk_var vs.vs_name vs.vs_ty (create_model_data_opt ~loc:f.t_loc ~context_labels:f.t_label "model_quantify") in
  let vv' = Mvs.mapi new_var vars in
  (* update modified variables *)
  let update v t f = wp_let (Mvs.find v vv') t f in
  Mvs.fold update vars (subst_at_now true vv' f)

let get_single_region_of_var vs =
  match (ity_of_vs vs).ity_node with
    | Ityapp (_,_,[r]) -> Some r
    | _ -> None

(* look for a variable with a single region equal to [reg] *)
let var_of_region reg f =
  let test acc vs =
    match get_single_region_of_var vs with
    | Some r when reg_equal r reg -> Some vs
    | _ -> acc in
  t_v_fold test None f

let quantify md env regs f =
  (* mreg : modified region -> vs *)
  let get_var reg () =
    let ty = ty_of_ity reg.reg_ity in
    let id = match var_of_region reg f with
      | Some vs -> vs.vs_name
      | None -> reg.reg_name in
    let md = match md.md_loc with
      | None ->
	(
	  match id.id_loc with
	  | None -> None
	  | Some l ->
	    Some (create_model_data
		    ~loc:l ~context_labels:id.id_label md.md_append_to_model_trace)
	)
      | _ -> Some md in
    mk_var id ty md in
  let mreg = Mreg.mapi get_var regs in
  (* quantify over the modified resions *)
  let f = update_term env mreg f in
  wp_forall (List.rev (Mreg.values mreg)) f

(** Invariants *)

let get_invariant km t =
  let ty = t_type t in
  let ts = match ty.ty_node with
    | Tyapp (ts,_) -> ts
    | _ -> assert false in
  let rec find_td = function
    | (its,_,inv) :: _ when ts_equal ts its.its_ts -> inv
    | _ :: tdl -> find_td tdl
    | [] -> assert false in
  let pd = Mid.find ts.ts_name km in
  let inv = match pd.Mlw_decl.pd_node with
    | Mlw_decl.PDdata tdl -> find_td tdl
    | _ -> assert false in
  let sbs = Ty.ty_match Mtv.empty (t_type inv) ty in
  let u, p = open_post (t_ty_subst sbs Mvs.empty inv) in
  wp_expl expl_type_inv (t_subst_single u t p)

let ps_inv = Term.create_psymbol (id_fresh "inv")
  [ty_var (create_tvsymbol (id_fresh "a"))]

let full_invariant lkm km vs ity =
  let rec update vs { fd_ity = ity } =
    if not (ity_has_inv ity) then t_true else
    (* what is our current invariant? *)
    let f = match ity.ity_node with
      | Ityapp (its,_,_) when its.its_inv ->
          if Debug.test_flag no_track
          then get_invariant km (t_var vs)
          else ps_app ps_inv [t_var vs]
      | _ -> t_true in
    (* what are our sub-invariants? *)
    let join _ fl _ = wp_ands ~sym:true fl in
    let g = analyze_var update join lkm km vs ity in
    (* put everything together *)
    wp_and ~sym:true f g
  in
  update vs { fd_ity = ity; fd_ghost = false; fd_mut = None }

(** Value tracking *)

type point = int
type value = point list Mls.t (* constructor -> field list *)

type state = {
  st_km   : Mlw_decl.known_map;
  st_lkm  : Decl.known_map;
  st_mem  : value Hint.t;
  st_next : point ref;
}

(* dead code
type names = point Mvs.t  (* variable -> point *)
type condition = lsymbol Mint.t (* point -> constructor *)
type lesson = condition list Mint.t (* point -> conditions for invariant *)
*)

let empty_state lkm km = {
  st_km   = km;
  st_lkm  = lkm;
  st_mem  = Hint.create 5;
  st_next = ref 0;
}

let next_point state =
  let res = !(state.st_next) in incr state.st_next; res

let make_value state ty =
  let get_p _ = next_point state in
  let new_cs cs = List.map get_p cs.ls_args in
  let add_cs m (cs,_) = Mls.add cs (new_cs cs) m in
  let csl = match ty.ty_node with
    | Tyapp (ts,_) -> Decl.find_constructors state.st_lkm ts
    | _ -> [] in
  List.fold_left add_cs Mls.empty csl

let match_point state ty p =
  try Hint.find state.st_mem p with Not_found ->
  let value = make_value state ty in
  if not (Mls.is_empty value) then
    Hint.replace state.st_mem p value;
  value

let rec open_pattern state names value p pat = match pat.pat_node with
  | Pwild -> names
  | Pvar vs -> Mvs.add vs p names
  | Papp (cs,patl) ->
      let add_pat names p pat =
        let value = match_point state pat.pat_ty p in
        open_pattern state names value p pat in
      List.fold_left2 add_pat names (Mls.find cs value) patl
  | Por _ ->
      let add_vs vs s = Mvs.add vs (next_point state) s in
      Svs.fold add_vs pat.pat_vars names
  | Pas (pat,vs) ->
      open_pattern state (Mvs.add vs p names) value p pat

let rec point_of_term state names t = match t.t_node with
  | Tvar vs ->
      Mvs.find vs names
  | Tapp (ls, tl) ->
      begin match Mid.find ls.ls_name state.st_lkm with
        | { Decl.d_node = Decl.Ddata tdl } ->
            let is_cs (cs,_) = ls_equal ls cs in
            let is_cs (_,csl) = List.exists is_cs csl in
            if List.exists is_cs tdl
            then point_of_constructor state names ls tl
            else point_of_projection state names ls (List.hd tl)
        | _ -> next_point state
      end
  | Tlet (t1, bt) ->
      let p1 = point_of_term state names t1 in
      let v, t2 = t_open_bound bt in
      let names = Mvs.add v p1 names in
      point_of_term state names t2
  | Tcase (t1,[br]) ->
      let pat, t2 = t_open_branch br in
      let p1 = point_of_term state names t1 in
      let value = match_point state pat.pat_ty p1 in
      let names = open_pattern state names value p1 pat in
      point_of_term state names t2
  | Tcase (t1,bl) ->
      (* we treat here the case of a value update: the value
         of each branch must be a distinct constructor *)
      let p = next_point state in
      let ty = Opt.get t.t_ty in
      let p1 = point_of_term state names t1 in
      let value = match_point state (Opt.get t1.t_ty) p1 in
      let branch acc br =
        let pat, t2 = t_open_branch br in
        let ls = match t2.t_node with
          | Tapp (ls,_) -> ls | _ -> raise Exit in
        let names = open_pattern state names value p1 pat in
        let p2 = point_of_term state names t2 in
        let v2 = match_point state ty p2 in
        Mls.add_new Exit ls (Mls.find_exn Exit ls v2) acc
      in
      begin try
        let value = List.fold_left branch Mls.empty bl in
        let value = Mls.set_union value (make_value state ty) in
        Hint.replace state.st_mem p value
      with Exit -> () end;
      p
  | Tconst _ | Tif _ | Teps _ -> next_point state
  | Tquant _ | Tbinop _ | Tnot _ | Ttrue | Tfalse -> assert false

and point_of_constructor state names ls tl =
  let p = next_point state in
  let pl = List.map (point_of_term state names) tl in
  let value = make_value state (Opt.get ls.ls_value) in
  let value = Mls.add ls pl value in
  Hint.replace state.st_mem p value;
  p

and point_of_projection state names ls t1 =
  let ty = Opt.get t1.t_ty in
  let csl = match ty.ty_node with
    | Tyapp (ts,_) -> Decl.find_constructors state.st_lkm ts
    | _ -> assert false in
  match csl with
    | [cs,pjl] ->
        let p1 = point_of_term state names t1 in
        let value = match_point state ty p1 in
        let rec find_p pjl pl = match pjl, pl with
          | Some pj::_, p::_ when ls_equal ls pj -> p
          | _::pjl, _::pl -> find_p pjl pl
          | _ -> assert false in
        find_p pjl (Mls.find cs value)
    | _ -> next_point state (* more than one, can't choose *)

let rec track_values state names lesson cond f = match f.t_node with
  | Tapp (ls, [t1]) when ls_equal ls ps_inv ->
      let p1 = point_of_term state names t1 in
      let condl = Mint.find_def [] p1 lesson in
      let contains c1 c2 = Mint.submap (fun _ -> ls_equal) c2 c1 in
      if List.exists (contains cond) condl then
        lesson, t_label_copy f t_true
      else
        let good c = not (contains c cond) in
        let condl = List.filter good condl in
        let l = Mint.add p1 (cond::condl) lesson in
        l, t_label_copy f (get_invariant state.st_km t1)
  | _ when (Slab.mem keep_on_simp_label f.t_label) ->
      lesson, f
  | Tbinop (Timplies, f1, f2) ->
      let l, f1 = track_values state names lesson cond f1 in
      let _, f2 = track_values state names l cond f2 in
      lesson, t_label_copy f (t_implies_simp f1 f2)
  | Tbinop (Tand, f1, f2) ->
      let l, f1 = track_values state names lesson cond f1 in
      let l, f2 = track_values state names l cond f2 in
      l, t_label_copy f (t_and_simp f1 f2)
  | Tbinop ((Tor|Tiff) as o, f1, f2) ->
      let _, f1 = track_values state names lesson cond f1 in
      let _, f2 = track_values state names lesson cond f2 in
      lesson, t_label_copy f (t_binary_simp o f1 f2)
  | Tnot f1 ->
      let _, f1 = track_values state names lesson cond f1 in
      lesson, t_label_copy f (t_not_simp f1)
  | Tif (fc, f1, f2) ->
      let _, f1 = track_values state names lesson cond f1 in
      let _, f2 = track_values state names lesson cond f2 in
      lesson, t_label_copy f (t_if_simp fc f1 f2)
  | Tcase (t1, bl) ->
      let p1 = point_of_term state names t1 in
      let value = match_point state (Opt.get t1.t_ty) p1 in
      let is_pat_var = function
        | { pat_node = Pvar _ } -> true | _ -> false in
      let branch l br =
        let pat, f1, cb = t_open_branch_cb br in
        let learn, cond = match bl, pat.pat_node with
          | [_], _ -> true, cond (* one branch, can learn *)
          | _, Papp (cs, pl) when List.for_all is_pat_var pl ->
              (try true, Mint.add_new Exit p1 cs cond (* can learn *)
              with Exit -> false, cond) (* contradiction, cannot learn *)
          | _, _ -> false, cond (* complex pattern, will not learn *)
        in
        let names = open_pattern state names value p1 pat in
        let m, f1 = track_values state names lesson cond f1 in
        let l = if learn then m else l in
        l, cb pat f1
      in
      let l, bl = Lists.map_fold_left branch lesson bl in
      l, t_label_copy f (t_case_simp t1 bl)
  | Tlet (t1, bf) ->
      let p1 = point_of_term state names t1 in
      let v, f1, cb = t_open_bound_cb bf in
      let names = Mvs.add v p1 names in
      let l, f1 = track_values state names lesson cond f1 in
      l, t_label_copy f (t_let_simp t1 (cb v f1))
  | Tquant (q, qf) ->
      let vl, trl, f1, cb = t_open_quant_cb qf in
      let add_vs s vs = Mvs.add vs (next_point state) s in
      let names = List.fold_left add_vs names vl in
      let l, f1 = track_values state names lesson cond f1 in
      l, t_label_copy f (t_quant_simp q (cb vl trl f1))
  | Tapp _ | Ttrue | Tfalse -> lesson, f
  | Tvar _ | Tconst _ | Teps _ -> assert false

let track_values lkm km f =
  let state = empty_state lkm km in
  let _, f = track_values state Mvs.empty Mint.empty Mint.empty f in
  f

(** Weakest preconditions *)

let rec wp_expr env e q xq =
  let f = wp_desc env e q xq in
  if Debug.test_flag debug then begin
    Format.eprintf "@[--------@\n@[<hov 2>e = %a@]@\n" Mlw_pretty.print_expr e;
    Format.eprintf "@[<hov 2>q = %a@]@\n" Pretty.print_term q;
    Format.eprintf "@[<hov 2>f = %a@]@\n----@]@." Pretty.print_term f;
  end;
  f

and wp_desc env e q xq = match e.e_node with
  | Elogic t ->
      let v, q = open_post q in
      let t = wp_label e t in
      (* NOTE: if you replace this t_subst by t_let or anything else,
         you must handle separately the case "let mark = 'now in ...",
         which requires 'now to be substituted for mark in q *)
      if ty_equal v.vs_ty ty_mark then
        t_subst_single v (to_term t) q
      else
        t_let_close_simp v (to_term t) q
  | Evalue pv ->
      let v, q = open_post q in
      let t = wp_label e (t_var pv.pv_vs) in
      t_subst_single v t q
  | Earrow _ ->
      let q = open_unit_post q in
      (* wp_label e *) q (* FIXME? *)
  | Elet ({ let_sym = LetV v; let_expr = e1 }, e2)
    when Opt.equal Loc.equal v.pv_vs.vs_name.id_loc e1.e_loc ->
    (* we push the label down, past the implicitly inserted "let" *)
      let w = wp_expr env (e_label_copy e e2) q xq in
      let q = create_post v.pv_vs w in
      wp_expr env e1 q xq
  | Elet ({ let_sym = LetV v; let_expr = e1 }, e2) ->
      let w = wp_expr env e2 q xq in
      let q = create_post v.pv_vs w in
      wp_label e (wp_expr env e1 q xq)
  | Elet ({ let_sym = LetA _; let_expr = e1 }, e2) ->
      let w = wp_expr env e2 q xq in
      let q = create_unit_post w in
      wp_label e (wp_expr env e1 q xq)
  | Erec (fdl, e1) ->
      let eff = match e1.e_vty with
        | VTarrow _ -> None
        | VTvalue _ -> Some e1.e_effect in
      let fr = wp_rec_defn ?eff env fdl in
      let fe = wp_expr env e1 q xq in
      let fr = wp_ands ~sym:true fr in
      wp_label e (wp_and ~sym:true fr fe)
  | Eif (e1, e2, e3) ->
      let res = vs_result e1 in
      let test = t_equ (t_var res) t_bool_true in
      (* if both branches are pure, do not split *)
      let w =
        let get_term e = match e.e_node with
          | Elogic t -> to_term t
          | Evalue v -> t_var v.pv_vs
          | _ -> raise Exit in
        try
          let r2 = wp_label e2 (get_term e2) in
          let r3 = wp_label e3 (get_term e3) in
          let v, q = open_post q in
          t_subst_single v (t_if_simp test r2 r3) q
        with Exit ->
          let w2 = wp_expr env e2 q xq in
          let w3 = wp_expr env e3 q xq in
          t_if_simp test w2 w3
      in
      let q = create_post res w in
      wp_label e (wp_expr env e1 q xq)
  (* optimization for the particular case let _ = e1 in e2 *)
  | Ecase (e1, [{ ppat_pattern = { pat_node = Term.Pwild }}, e2]) ->
      let w = wp_expr env e2 q xq in
      let q = create_post (vs_result e1) w in
      wp_label e (wp_expr env e1 q xq)
  (* optimization for the particular case let () = e1 in e2 *)
  | Ecase (e1, [{ ppat_pattern = { pat_node = Term.Papp (cs,[]) }}, e2])
    when ls_equal cs fs_void ->
      let w = wp_expr env e2 q xq in
      let q = create_unit_post w in
      wp_label e (wp_expr env e1 q xq)
  | Ecase (e1, bl) ->
      let res = vs_result e1 in
      let branch ({ ppat_pattern = pat }, e) =
        t_close_branch pat (wp_expr env e q xq) in
      let w = t_case_simp (t_var res) (List.map branch bl) in
      let q = create_post res w in
      wp_label e (wp_expr env e1 q xq)
  | Eghost e1 ->
      wp_label e (wp_expr env e1 q xq)
  | Eraise (xs, e1) ->
      let q = try Mexn.find xs xq with
        Not_found -> assert false in
      wp_label e (wp_expr env e1 q xq)
  | Etry (e1, bl) ->
      let branch (xs,v,e) acc =
        let w = wp_expr env e q xq in
        let q = create_post v.pv_vs w in
        Mexn.add xs q acc in
      let xq = List.fold_right branch bl xq in
      wp_label e (wp_expr env e1 q xq)
  | Eassert (Aassert, f) ->
      let q = open_unit_post q in
      let f = wp_expl expl_assert f in
      wp_and ~sym:false (wp_label e f) q
  | Eassert (Acheck, f) ->
      let q = open_unit_post q in
      let f = wp_expl expl_check f in
      wp_and ~sym:true (wp_label e f) q
  | Eassert (Aassume, f) ->
      let q = open_unit_post q in
      let f = wp_expl expl_assume f in
      wp_implies (wp_label e f) q
  | Eabsurd ->
      wp_label e (wp_expl expl_absurd t_absurd)
  | Eany spec ->
      let p = wp_label e (wp_expl expl_pre spec.c_pre) in
      let p = t_label ?loc:e.e_loc p.t_label p in
      (* TODO: propagate call labels into tyc.c_post *)
      let w = wp_abstract (create_model_data ?loc:e.e_loc "any") env spec.c_effect spec.c_post spec.c_xpost q xq in
      wp_and ~sym:false p w
  | Eapp (e1,_,spec) ->
      let p = wp_label e (wp_expl expl_pre spec.c_pre) in
      let p = t_label ?loc:e.e_loc p.t_label p in
      let d =
        if spec.c_letrec = 0 || spec.c_variant = [] then t_true else
        let olds = Mint.find_def [] spec.c_letrec env.letrec_var in
        if olds = [] then t_true (* we are out of letrec *) else
        decrease e.e_loc expl_variant env olds spec.c_variant in
      (* TODO: propagate call labels into tyc.c_post *)
      let md = create_model_data ?loc:e1.e_loc ~context_labels:e1.e_label "call" in
      let w = wp_abstract md env spec.c_effect spec.c_post spec.c_xpost q xq in
      let w = wp_and ~sym:true d (wp_and ~sym:false p w) in
      let q = create_unit_post w in
      wp_expr env e1 q xq (* FIXME? should (wp_label e) rather be here? *)
  | Eabstr (e1, spec) ->
      let p = wp_label e (wp_expl expl_pre spec.c_pre) in
      (* every exception uncovered in spec is passed to xq *)
      let c_xq = Mexn.set_union spec.c_xpost xq in
      let w1 = backstep (wp_expr env e1) spec.c_post c_xq in
      (* so that now we don't need to prove these exceptions again *)
      let lost = Mexn.set_diff (exns_of_raises e1.e_effect) spec.c_xpost in
      let c_eff = Sexn.fold_left eff_remove_raise e1.e_effect lost in
      let md = create_model_data ?loc:e1.e_loc ~context_labels:e1.e_label "abstract" in
      let w2 = wp_abstract md env c_eff spec.c_post spec.c_xpost q xq in
      wp_and ~sym:false p (wp_and ~sym:true (wp_label e w1) w2)
  | Eassign (pl, e1, reg, pv) ->
      (* if we create an intermediate variable npv to represent e1
         in the post-condition of the assign, the call to wp_abstract
         will have to update this variable separately (in addition to
         all existing variables in q that require update), creating
         duplication.  To avoid it, we try to detect whether the value
         of e1 can be represented by an existing pure term that can
         be reused in the post-condition. *)
      let rec get_term d = match d.e_node with
        | Eghost e | Elet (_,e) | Erec (_,e) -> get_term e
        | Evalue v -> vs_result e1, t_var v.pv_vs
        | Elogic t -> vs_result e1, t
        | _ ->
            let ity = ity_of_expr e1 in
            let id = id_fresh ?loc:e1.e_loc "o" in
            (* must be a pvsymbol or restore_pv will fail *)
            let npv = create_pvsymbol id ~ghost:e1.e_ghost ity in
            npv.pv_vs, t_var npv.pv_vs
      in
      let res, t = get_term e1 in
      let t = fs_app pl.pl_ls [t] pv.pv_vs.vs_ty in
      let c_q = create_unit_post (t_equ t (t_var pv.pv_vs)) in
      let eff = eff_write eff_empty reg in
      let md = create_model_data ?loc:e1.e_loc ~context_labels:e1.e_label "assign" in
      let w = wp_abstract md env eff c_q Mexn.empty q xq in
      let q = create_post res w in
      wp_label e (wp_expr env e1 q xq)
  | Eloop (inv, varl, e1) ->
      (* TODO: what do we do about well-foundness? *)
      let i = wp_expl expl_loop_keep inv in
      let olds = List.map (fun (t,r) -> t_at_old t , r) varl in
      let i = if varl = [] then i else
        let d = decrease e.e_loc expl_loopvar env olds varl in
        wp_and ~sym:true i d in
      let q = create_unit_post i in
      let w = backstep (wp_expr env e1) q xq in
      let regs = regs_of_writes e1.e_effect in
      let md = create_model_data ?loc:e1.e_loc ~context_labels:e1.e_label "loop" in
      let w = quantify md  env regs (wp_implies inv w) in
      let i = wp_expl expl_loop_init inv in
      wp_label e (wp_and ~sym:true i w)
  | Efor ({pv_vs = x}, ({pv_vs = v1}, d, {pv_vs = v2}), inv, e1) ->
      (* wp(for x = v1 to v2 do inv { I(x) } e1, Q, R) =
             v1 > v2  -> Q
         and v1 <= v2 ->     I(v1)
                         and forall S. forall i. v1 <= i <= v2 ->
                                                 I(i) -> wp(e1, I(i+1), R)
                                       and I(v2+1) -> Q *)
      let gt, le, incr = match d with
        | Mlw_expr.To     -> env.ps_int_gt, env.ps_int_le, env.fs_int_pl
        | Mlw_expr.DownTo -> env.ps_int_lt, env.ps_int_ge, env.fs_int_mn
      in
      let one = t_nat_const 1 in
      let v1_gt_v2 = ps_app gt [t_var v1; t_var v2] in
      let v1_le_v2 = ps_app le [t_var v1; t_var v2] in
      let q = open_unit_post q in
      let wp_init =
        wp_expl expl_loop_init (t_subst_single x (t_var v1) inv) in
      let wp_step =
        let next = fs_app incr [t_var x; one] ty_int in
        let post = wp_expl expl_loop_keep (t_subst_single x next inv) in
        wp_expr env e1 (create_unit_post post) xq in
      let wp_last =
        let v2pl1 = fs_app incr [t_var v2; one] ty_int in
        wp_implies (t_subst_single x v2pl1 inv) q in
      let md = create_model_data ?loc:e1.e_loc ~context_labels:e1.e_label "loop" in
      let wp_good = wp_and ~sym:true
        wp_init
        (quantify md env (regs_of_writes e1.e_effect)
           (wp_and ~sym:true
              (wp_forall [x] (wp_implies
                (wp_and ~sym:true (ps_app le [t_var v1; t_var x])
                                  (ps_app le [t_var x;  t_var v2]))
                (wp_implies inv wp_step)))
              wp_last))
      in
      let wp_full = wp_and ~sym:true
        (wp_implies v1_gt_v2 q)
        (wp_implies v1_le_v2 wp_good)
      in
      wp_label e wp_full

and wp_abstract md env c_eff c_q c_xq q xq =
  let regs = regs_of_writes c_eff in
  let exns = exns_of_raises c_eff in
  let quantify_post c_q q =
    let v, f = open_post q in
    let c_v, c_f = open_post c_q in
    let c_f = t_subst_single c_v (t_var v) c_f in
    let f = wp_forall_post v c_f f in
    quantify md env regs f
  in
  let quantify_xpost _ c_xq xq =
    Some (quantify_post c_xq xq) in
  let proceed c_q c_xq =
    let f = quantify_post c_q q in
    (* every xs in exns is guaranteed to be in c_xq and xq *)
    assert (Mexn.set_submap exns xq);
    assert (Mexn.set_submap exns c_xq);
    let xq = Mexn.set_inter xq exns in
    let c_xq = Mexn.set_inter c_xq exns in
    let mexn = Mexn.inter quantify_xpost c_xq xq in
    (* FIXME? This wp_ands is asymmetric in Pgm_wp *)
    wp_ands ~sym:true (f :: Mexn.values mexn)
  in
  backstep proceed c_q c_xq

and wp_fun_regs ps l = (* regions to refresh at the top of function WP *)
  let add_arg = let seen = ref Sreg.empty in fun sbs pv ->
    (* we only need to "havoc" the regions that occur twice in [l.l_args].
       If a region in an argument is shared with the context, then is it
       already frozen in [ps.ps_subst]. If a region in an argument is not
       shared at all, the last [wp_forall] over [args] will be enough. *)
    let rec down sbs ity =
      let rl = match ity.ity_node with
        | Ityapp (_,_,rl) -> rl | _ -> [] in
      ity_fold down (List.fold_left add_reg sbs rl) ity
    and add_reg sbs r =
      if Sreg.mem r !seen then reg_match sbs r r else
      (seen := Sreg.add r !seen; down sbs r.reg_ity) in
    down sbs pv.pv_ity in
  let sbs = List.fold_left add_arg ps.ps_subst l.l_args in
  Mreg.map (fun _ -> ()) sbs.ity_subst_reg

and wp_fun_defn ?eff env { fun_ps = ps ; fun_lambda = l } =
  let lab = fresh_mark () and c = l.l_spec in
  let args = List.map (fun pv -> pv.pv_vs) l.l_args in
  let env =
    if c.c_letrec = 0 || c.c_variant = [] then env else
    let lab = t_var lab in
    let t_at_lab (t,r) = t_app fs_at [t; lab] t.t_ty , r in
    let tl = List.map t_at_lab c.c_variant in
    let lrv = Mint.add c.c_letrec tl env.letrec_var in
    { env with letrec_var = lrv } in
  let q = old_mark lab (wp_expl expl_post c.c_post) in
  let conv p = old_mark lab (wp_expl expl_xpost p) in
  let f = wp_expr env l.l_expr q (Mexn.map conv c.c_xpost) in
  let f = wp_implies c.c_pre (erase_mark lab f) in
  let md = create_model_data "init" in
  let keep_reg eff r =
    Sreg.mem r eff.eff_writes || Sreg.mem r eff.eff_ghostw ||
    (* the test below is probably useless, since the surface language does
       not allow a function argument to be aliased with the context *)
    List.exists (fun v -> reg_occurs r v.pv_ity.ity_vars) l.l_args in
  let regs = wp_fun_regs ps l in
  let regs = match eff with
    | None -> regs
    | Some e -> Sreg.filter (keep_reg e) regs in
  wp_forall args (quantify md env regs f)

and wp_rec_defn ?eff env fdl = List.map (wp_fun_defn ?eff env) fdl

(***
let bool_to_prop env f =
  let ts_bool  = find_ts ~pure:true env "bool" in
  let ls_andb  = find_ls ~pure:true env "andb" in
  let ls_orb   = find_ls ~pure:true env "orb" in
  let ls_notb  = find_ls ~pure:true env "notb" in
  let ls_True  = find_ls ~pure:true env "True" in
  let ls_False = find_ls ~pure:true env "False" in
  let t_True   = fs_app ls_True [] (ty_app ts_bool []) in
  let is_bool ls = ls_equal ls ls_True || ls_equal ls ls_False in
  let rec t_iff_bool f1 f2 = match f1.t_node, f2.t_node with
    | Tnot f1, _ -> t_not_simp (t_iff_bool f1 f2)
    | _, Tnot f2 -> t_not_simp (t_iff_bool f1 f2)
    | Tapp (ps1, [t1; { t_node = Tapp (ls1, []) }]),
      Tapp (ps2, [t2; { t_node = Tapp (ls2, []) }])
      when ls_equal ps1 ps_equ && ls_equal ps2 ps_equ &&
           is_bool ls1 && is_bool ls2 ->
        if ls_equal ls1 ls2 then t_equ t1 t2 else t_neq t1 t2
    | _ ->
        t_iff_simp f1 f2
  in
  let rec t_btop t = t_label ?loc:t.t_loc t.t_label (* t_label_copy? *)
    (match t.t_node with
    | Tif (f,t1,t2) ->
        t_if_simp (f_btop f) (t_btop t1) (t_btop t2)
    | Tapp (ls, [t1;t2]) when ls_equal ls ls_andb ->
        t_and_simp (t_btop t1) (t_btop t2)
    | Tapp (ls, [t1;t2]) when ls_equal ls ls_orb ->
        t_or_simp (t_btop t1) (t_btop t2)
    | Tapp (ls, [t1]) when ls_equal ls ls_notb ->
        t_not_simp (t_btop t1)
    | Tapp (ls, []) when ls_equal ls ls_True ->
        t_true
    | Tapp (ls, []) when ls_equal ls ls_False ->
        t_false
    | _ ->
        t_equ_simp (f_btop t) t_True)
  and f_btop f = match f.t_node with
    | Tapp (ls, [{t_ty = Some {ty_node = Tyapp (ts, [])}} as l; r])
      when ls_equal ls ps_equ && ts_equal ts ts_bool ->
        t_label ?loc:f.t_loc f.t_label (t_iff_bool (t_btop l) (t_btop r))
    | _ ->
        t_map_simp f_btop f
  in
  f_btop f
***)

(* replace t_absurd with t_false *)
let rec unabsurd f = match f.t_node with
  | Tapp (ls, []) when ls_equal ls ls_absurd ->
      t_label_copy f (t_label_add keep_on_simp_label t_false)
  | _ ->
      t_map unabsurd f

let add_wp_decl km name f uc =
  (* prepare a proposition symbol *)
  let s = "WP_parameter " ^ name.id_string in
  let label =
    let label = name.id_label in
    if lab_has_expl label then label
    else
      (* set a proper explanation *)
      let n =
        try let _, _, l = restore_path name in
          String.concat "." l
        with Not_found -> name.id_string
      in
      let lab = Ident.create_label ("expl:VC for " ^ n) in
      Slab.add lab label
  in
  let id = id_fresh ~label ?loc:name.id_loc s in
  let pr = create_prsymbol id in
  (* prepare the VC formula *)
  let f = remove_at f in
  (* let f = bool_to_prop uc f in *)
  let f = unabsurd f in
  (* get a known map with tuples added *)
  let lkm = Theory.get_known uc in
  (* remove redundant invariants *)
  let f = if Debug.test_flag no_track then f else track_values lkm km f in
  (* simplify f *)
  let f = if Debug.test_flag no_eval then f else
    (* do preliminary checks on f to spare eval_match any surprises *)
    let _lkm = Decl.known_add_decl lkm (create_prop_decl Pgoal pr f) in
    Eval_match.eval_match ~inline:Eval_match.inline_nonrec_linear lkm f in
  (* printf "wp: f=%a@." print_term f; *)
  let d = create_prop_decl Pgoal pr f in
  Theory.add_decl uc d

let mk_env env km th =
  let th_int = Env.read_theory env ["int"] "Int" in
  { prog_known = km;
    pure_known = Theory.get_known th;
    global_env = env;
    ps_int_le  = Theory.ns_find_ls th_int.th_export ["infix <="];
    ps_int_ge  = Theory.ns_find_ls th_int.th_export ["infix >="];
    ps_int_lt  = Theory.ns_find_ls th_int.th_export ["infix <"];
    ps_int_gt  = Theory.ns_find_ls th_int.th_export ["infix >"];
    fs_int_pl  = Theory.ns_find_ls th_int.th_export ["infix +"];
    fs_int_mn  = Theory.ns_find_ls th_int.th_export ["infix -"];
    letrec_var = Mint.empty;
  }

let wp_let env km th { let_sym = lv; let_expr = e } =
  let env = mk_env env km th in
  let q, xq = default_post e.e_vty e.e_effect in
  let f = wp_expr env e q xq in
  let f = wp_forall (Mvs.keys (t_vars f)) f in
  let id = match lv with
    | LetV pv -> pv.pv_vs.vs_name
    | LetA ps -> ps.ps_name in
  add_wp_decl km id f th

let wp_rec env km th fdl =
  let env = mk_env env km th in
  let fl = wp_rec_defn env fdl in
  let add_one th d f =
    Debug.dprintf debug "wp %s = %a@\n----------------@."
      d.fun_ps.ps_name.id_string Pretty.print_term f;
    let f = wp_forall (Mvs.keys (t_vars f)) f in
    add_wp_decl km d.fun_ps.ps_name f th
  in
  List.fold_left2 add_one th fdl fl

let wp_val _env _km th _lv = th

(*****************************************************************************)

(* Efficient Weakest Preconditions

  Following Leino, see
  http://research.microsoft.com/apps/pubs/default.aspx?id=70052

  Roughly, the idea is the following. From a program expression e, we compute
  two formulas OK and N. Formula OK means ``the execution of e does not go
  wrong'' and formula N is an input-output relation between initial and
  final state of e's execution.

  Thus the weakest precondition of e is simply OK.
  N is involved in recursive computations, e.g.
  OK(fun x -> {p} e {q}) = forall x. p => OK(e) /\ (forall result. N(e) => q)
  And so on.

  In practice, this is a bit more involved, since execution of e may raise
  exceptions. So formula N comes with other formulas E(x), once for each
  exception x that is possibly raised by e. E(x) is the input-output relation
  that holds when exception x is raised.
*)

let fast_wp = Debug.register_flag "fast_wp"
  ~desc:"Efficient@ Weakest@ Preconditions.@ \
    Work@ in@ progress,@ not@ ready@ for@ use."

module Subst : sig
   (* A substitution, or state, represents the state at a given point in the
      program. It maps each region to the name that should be used to refer to
      the value of the region in the current state. *)

   type t
   (* the type of substitutions *)

   (* (* debugging code *)
   val print_state : Format.formatter -> t -> unit
   *)

   val init : Spv.t -> t
   (* the initial substitution for a program which mentions the given program
      variables *)

   val mark : t -> t

   val havoc : model_data option -> wp_env -> Sreg.t -> t -> t * term
   (* [havoc md env regions s] generates a new state in which all regions in
      [regions] are touched and all other regions unchanged. The result pair
      (s',f) is the new state [s'] and a formula [f] which defines the new
      values in [s'] with respect to the input state [s].
      The parameter md can be used to pass information about new
      variables created in the new state.
*)

   val extract_glue : wp_env -> Sreg.t -> t -> t -> term
   (* The formula [extract_glue env regs s1 s2] expresses what has not changed
      between [s1] and [s2], concerning program variables. The set of
    *)

   val merge : model_data option -> t -> t -> t -> t * term * term
   (* Given a start state and two states that parted from there, return a new
      "join" state and two formulas.  The first formula links the first branch
      state with the join state, the second formula links the second branch
      state with the join state.
      The parameter of type model_data can be used to pass information about new
      variables created in the new state.
   *)

   val merge_l : model_data option -> t -> t list -> t * term list
   (* same as merge, but merges n states *)

   val save_label : vsymbol -> t -> t
   (* [save_label vs s] registers the state s as being the one that corresponds
      to label [vs]. This mapping is preserved even after calls to [havoc] and
      [merge], so that any labeled previous state can be obtained *)

   val term : t -> term -> term
   (* [term s f] apply the state [s] to the term [f]. If [f] contains
      labeled subterms, these will be appropriately dealt with. *)

   val add_pvar : model_data option -> pvsymbol -> t -> t
   (* [add_pvar md v s] adds the variable v to s, if it is mutable.
      The parameter md can be used to pass information about new
      variables created in the new state. *)

end = struct

  type subst =
    { subst_regions : vsymbol Mreg.t;
      subst_vars    : term Mvs.t;
    }
  (* a substitution or state knows the current variables to use for each region
     and each mutable program variable. *)

  type t =
    { now       : subst;
      other     : subst Mvs.t;
      reg_names : vsymbol Mreg.t;
      marked    : bool;
    }
  (* the reg_names field is a simple name hint; a mapping reg |-> name means
     that [name] should be used as a base for new variables in region [reg].
     This mapping is not required to be complete for regions. *)
  (* the actual state knows not only the current state, but also all labeled
     past states. *)

  let mk_var name ity md = mk_var name (ty_of_ity ity) md

  let fresh_var_from_region md hints reg =
    let name =
      try (Mreg.find reg hints).vs_name
      with Not_found -> reg.reg_name
    in

    mk_var name reg.reg_ity md

  let fresh_var_from_var md vs =
    mk_var vs.vs_name (ity_of_vs vs) md

  let is_simple_var = get_single_region_of_var
  let is_simple_pvar pv = is_simple_var pv.pv_vs

  let add_pvar md pv s =
    (* register a single program variable in the state. Use the variable itself
       as its first name; for subsequent havocs this will change. All regions
       belonging to this program variable are also added to the state, if not
       already there. Note that [add_pvar] doesn't really change the state,
       only adds new knowledge. *)
    (* for simple variables (1 variable = 1 mutable region), we do not
       introduce a new program variable each time, instead we use directly the
       [update_var] term. See also [havoc]. This is a heuristics which assumes
       that in this case, the program variable would be an overhead. In
       particular for simple references it is an important optimization. *)
    let ity = pv.pv_ity in
    if ity_immutable ity then s
    else
      let vs = pv.pv_vs in
      let is_simple = is_simple_pvar pv in
      let vars = Mvs.add vs (t_var vs) s.now.subst_vars in
      let reg_names =
        match is_simple with
        | None -> s.reg_names
        | Some r -> Mreg.add r vs s.reg_names
      in
      { other      = s.other;
        reg_names  = reg_names;
        marked     = s.marked;
        now        =
          { subst_vars = vars;
            subst_regions =
              reg_fold (fun r acc ->
                if Mreg.mem r acc then acc
                else Mreg.add r (fresh_var_from_region md reg_names r) acc)
              ity.ity_vars s.now.subst_regions;
          }
      }

  let empty =
    { other         = Mvs.empty;
      reg_names     = Mreg.empty;
      marked        = false;
      now           = { subst_regions = Mreg.empty;
                        subst_vars    = Mvs.empty; }
    }

  let mark s = { s with marked = true }

  (* (* debugging code *)
  let print_state fmt s =
    Format.fprintf fmt "{ ";
    Mvs.iter (fun _ v -> Format.printf " %a " Pretty.print_term v) s.now.subst_vars;
    Format.fprintf fmt " }"
  *)

  let init pvs =
    (* init the state with the given program variables. *)
    Spv.fold (add_pvar None) pvs empty

  let save_label vs sub =
    (* simply store the "now" substitution in the map with the given label *)
    { sub with other = Mvs.add vs sub.now sub.other }

  let pv_is_touched_by_regions vs regset =
    (* decide whether a (logic) variable [vs] changes value when [regset] has
       been touched. *)
    reg_any (fun reg -> Sreg.mem reg regset) (restore_pv vs).pv_ity.ity_vars

  let havoc md env regset s =
    (* introduce new variables for all regions, and all program variables for a
       region. *)
    let regs =
      Sreg.fold (fun reg acc ->
        Mreg.add reg (fresh_var_from_region md s.reg_names reg) acc)
      regset s.now.subst_regions in
    let touched_regs = Mreg.set_inter regs regset in
    (* We special case simple variables: no new variable is introduced for the
     * program variable, we directly use the "update_var" term. *)
    let vars, f = Mvs.fold (fun vs _ ((acc_vars, acc_f) as acc) ->
      if pv_is_touched_by_regions vs regset then begin
        let new_term = update_var env touched_regs vs in
        if is_simple_var vs <> None then
          Mvs.add vs new_term acc_vars, acc_f
        else
          let var = t_var (fresh_var_from_var md vs) in
          Mvs.add vs var acc_vars,
          t_and_simp (t_equ_simp var new_term) acc_f
      end else begin
        acc
      end) s.now.subst_vars (s.now.subst_vars, t_true) in
    { s with now =
        { subst_regions = regs;
          subst_vars    = vars;
        };
        marked = s.marked }, f

  let rec term s t =
    (* apply a substitution to a formula. This is straightforward, we only need
       to take care of labels that may point to previous states. We update the
       "current" substitution accordingly. *)
    match t.t_node with
    | Tvar vs ->
        (* We simply replace the program variable [vs] by its "now" value. *)
        begin try Mvs.find vs s.now.subst_vars
        with Not_found -> t
        end
    | Tapp (ls, _) when ls_equal ls fs_old -> assert false
    | Tapp (ls, [subterm; mark]) when ls_equal ls fs_at ->
        let label =
          match mark.t_node with
          | Tvar vs when vs_equal vs vs_old -> assert false
          | Tvar vs -> vs
          | _ -> assert false
        in
        let subst =
          try
            { s with now = Mvs.find label s.other }
          with Not_found ->
            (* all labels should have been registered in the "others" map *)
            assert false
        in
        t_map (term subst) subterm
    | Tlet _ | Tcase _ | Teps _ | Tquant _ ->
        (* do not open unless necessary *)
        let mvs = Mvs.set_inter s.now.subst_vars (t_vars t) in
        if Mvs.is_empty mvs then t else
        t_map (term s) t
    | _ ->
        t_map (term s) t

  let extract_glue env regions s1 s2 =
    (* we are only interested in "now" program vars *)
    let touched_regions =
      Mreg.filter (fun r _ -> Sreg.mem r regions) s2.now.subst_regions in
    let s1 = s1.now.subst_vars and s2 = s2.now.subst_vars in
    (* We iterate over the first state, because the second one potentially
     * contains more variables *)
    Mvs.fold
      (fun var old_f acc ->
          let f = Mvs.find var s2 in
          if t_equal f old_f || is_simple_var var <> None then acc
          else
            let new_value = update_var env touched_regions var in
            t_and_simp acc (t_equ_simp f new_value)
      ) s1 t_true

  let subst_inter a b =
    (* compute the intersection of two substitutions. *)
    { subst_vars = Mvs.set_inter a.subst_vars b.subst_vars;
      subst_regions = Mreg.set_inter a.subst_regions b.subst_regions;
    }

  let rec first_different base eq l =
    match l with
    | [] -> None
    | x :: xs -> if eq base x then first_different base eq xs else Some x

  let first_different_vars base l = first_different base vs_equal l
  let first_different_terms base l = first_different base t_equal l

  let merge_vars md marked base domain mapl =
    Mvs.fold (fun k _ (map , fl) ->
        let all_terms = List.map (fun m -> Mvs.find k m) mapl in
        match first_different_terms (Mvs.find k base) all_terms with
        | None -> Mvs.add k (List.hd all_terms) map, fl
        | Some new_ ->
            let new_ =
              if marked then t_var (fresh_var_from_var md k) else new_ in
            Mvs.add k new_ map,
            List.map2 (fun old f ->
              t_and_simp (t_equ new_ old) f) all_terms fl)
    domain (Mvs.empty, List.map (fun _ -> t_true) mapl)

  let merge_regs md names marked base domain mapl =
    Mreg.fold (fun k _ (map, fl) ->
      let all_vars = List.map (fun m -> Mreg.find k m) mapl in
      match first_different_vars (Mreg.find k base) all_vars with
      | None -> Mreg.add k (List.hd all_vars) map, fl
      | Some new_ ->
          let new_ =
            if marked then fresh_var_from_region md names k else new_ in
          Mreg.add k new_ map,
          List.map2 (fun old f ->
            if vs_equal old new_ then f
            else t_and_simp (t_equ (t_var new_) (t_var old)) f) all_vars fl)
    domain (Mreg.empty, List.map (fun _ -> t_true) mapl)

  let merge_l md base sl =
    match sl with
    | [] -> assert false
    | [s] -> s, [t_true]
    | _ ->
        (* we can work on the intersection of the domains, because relevant
           program variables/regions should be present in all of them. *)
        let domain =
          List.fold_left (fun acc s -> subst_inter acc s.now) base.now sl in
        let marked = List.exists (fun x -> x.marked) sl in
        let vars, fl1 =
          merge_vars md marked base.now.subst_vars domain.subst_vars
            (List.map (fun x -> x.now.subst_vars) sl)
        in
        let regs, fl2 =
          merge_regs md base.reg_names marked base.now.subst_regions
                     domain.subst_regions
                     (List.map (fun x -> x.now.subst_regions) sl)
        in
        { base with now =
            { subst_vars = vars;
              subst_regions = regs };
            marked = marked;
        },
        List.map2 t_and_simp fl1 fl2

  let merge md base s1 s2 =
    let s, fl = merge_l md base [s1; s2] in
    match fl with
    | [f1; f2] -> s, f1, f2
    | _ -> assert false

end

let fastwp_or_label = Ident.create_label "fastwp:or"
let wp_or f1 f2 = t_label_add fastwp_or_label (t_or_simp f1 f2)

let xs_result xs = create_vsymbol (id_fresh "result") (ty_of_ity xs.xs_ity)
let result e =
  vs_result e, Mexn.mapi (fun xs _ -> xs_result xs) e.e_effect.eff_raises

let is_vty_unit = function
  | VTvalue ity -> ity_equal ity ity_unit
  | VTarrow _   -> false

(* The type for postconditions of expressions is the pair of the actual
   formula [ne], and a substitution [s] to be applied to [ne] to get the final
   postcondition. This allows delayed choice of names. *)
type fwp_post =
  { ne : term; s : Subst.t }

(* The type for postconditions in case of exceptions maps every exception to
   its postcondition. *)
type fast_wp_exn_map = fwp_post Mexn.t

(* The type for the result of fast weakest preconditions over expression e
   is a triple where
   - formula [ok] means ``e evaluates without any fault''
     (whatever the execution flow is)
   - postcondition [post] relates the input state and the output state, and
     it contains the output state.
   - exceptional postconditions [exn] relate relates the input state and
     the output state, and contain the output state, in case an exception is
     raised.
*)
type fast_wp_result = {
  ok   : term;
  post : fwp_post;
  exn  : fast_wp_exn_map
}

(* Create a formula expressing that "n" implies "q", and for each exception
   "xn" implies "xq", quantifying over the result names. *)
let wp_nimplies (n : term) (xn : fast_wp_exn_map) ((result, q), xq) =
  let f = wp_forall [result] (wp_implies n q) in
  assert (Mexn.cardinal xn = Mexn.cardinal xq);
  let x_implies _xs { ne = n } (xresult, q) f =
    t_and_simp f (wp_forall [xresult] (wp_implies n q)) in
  Mexn.fold2_inter x_implies xn xq f

type res_type = vsymbol * vsymbol Mexn.t

(* Take a [post], and place the postcondition [post.ne] in the
   poststate [post.s]. Also, open the postcondition and replace the result
   variable by [result_var]. In [post.s], [lab] is used to define the prestate.
*)
let apply_state_to_single_post glue lab expl result_var post =
  (* get the result var of the post *)
  let res, ne = open_post post.ne in
  (* substitute result_var and replace "old" label with new label *)
  let ne = t_subst_single res (t_var result_var) (old_mark lab ne) in
  (* apply the prestate = replace previously "old" variables *)
  { post with ne = t_and_simp glue (wp_expl expl (Subst.term post.s ne)) }

(* Given normal and exceptional [post,xpost], each with its
   own poststate, place all [(x)post.ne] in the state defined by [(x)post.s].*)
let apply_state_to_post glue lab result_vars post xpost =
  let result, xresult = result_vars in
  let f expl = apply_state_to_single_post glue lab expl in
  let a = f expl_post result post in
  let b = Mexn.mapi (fun ex post ->
                        f expl_xpost (Mexn.find ex xresult) post) xpost in
  a, b

let all_exns xmap_list =
  let add_elt k _ acc = Sexn.add k acc in
  List.fold_left (fun acc m -> Mexn.fold add_elt m acc) Sexn.empty xmap_list

let iter_exns exns f =
  Sexn.fold (fun x acc -> let v = f x in Mexn.add x v acc) exns Mexn.empty

let iter_all_exns xmap_list f =
  iter_exns (all_exns xmap_list) f

let merge_opt md s opt_sl =
  (* merge a list of optional states: all present states are merged together,
     and the merged state is returned, together with the glue formula for all
     states. For absent states, the glue formula "false" is returned *)
  let l = List.filter (fun x -> x <> None) opt_sl in
  let l = List.map Opt.get l in
  let s, fl = Subst.merge_l md s l in
  let rec merge_lists acc opt_sl fl =
    match opt_sl, fl with
    | None :: rest, _ -> merge_lists (t_false :: acc) rest fl
    | Some _ :: rest, f :: fl -> merge_lists (f :: acc) rest fl
    | [], [] -> List.rev acc
    | _, _ -> assert false
  in
  s, merge_lists [] opt_sl fl

let merge_opt_post_l md s opt_l =
  (* given a list of optional fwp_post states, merge them and return a tuple
       s, postl
     such that s is the merged state, and postl is the list of formulas that
     express each input fwp in the new state s.*)
  let opt_sl = List.map (fun x -> Opt.map (fun x -> x.s) x) opt_l in
  let s, fl = merge_opt md s opt_sl in
  s,
  List.map2 (fun opt f ->
    match opt with
    | None -> t_false
    | Some x -> t_and_simp f x.ne) opt_l fl

let merge_opt_post md s opt1 opt2 =
  (* wrapper for merge_opt_post_l for two input states *)
  let s, fl = merge_opt_post_l md s [opt1;opt2] in
  match fl with
  | [f1;f2] -> s, f1, f2
  | _ -> assert false

let merge_opt_post_3 md s opt_p1 opt_p2 opt_p3 =
  (* wrapper for merge_opt_post for three input states *)
  let s, fl = merge_opt_post_l md s [opt_p1;opt_p2;opt_p3] in
  match fl with
  | [f1;f2;f3] -> s, f1, f2, f3
  | _ -> assert false

(* Input
   - a state s: Subst.t
   - names r = (result: vsymbol, xresult: vsymbol Mexn.t)
   - an expression e
   with: dom(xresult) = XS, the set of exceptions possibly raised
   by a, that is e.e_effect.eff_raises

   Output is a triple (OK, ((NE, s), EX)) where
   - formula OK means ``e evaluates without any fault''
   (whatever the execution flow is)
   - formula NE means
   ``e terminates normally with final state s and output result''
   - for each exception x, EX(x) = (fx,sx), where formula fx means
   ``e raises exception x, with final state sx and value xresult(x) in sx''
*)
let rec fast_wp_expr (env : wp_env) (s : Subst.t) (r : res_type) (e : expr)
    : fast_wp_result =
  let res = fast_wp_desc env s r e in
  if Debug.test_flag debug then begin
    Format.eprintf "@[--------@\n@[<hov 2>e = %a@]@\n" Mlw_pretty.print_expr e;
    Format.eprintf "@[<hov 2>OK = %a@]@\n" Pretty.print_term res.ok;
  end;
  res

(* TODO: Should we make sure the label of [e] is always propagated to the
   result of fast wp? In that case, should it be put on [ok], on [ne], on
   both? *)

and fast_wp_desc (env : wp_env) (s : Subst.t) (r : res_type) (e : expr)
    : fast_wp_result =
  let result, xresult = r in
  match e.e_node with
  | Elogic t ->
      (* OK: true *)
      (* NE: result = t *)
      let t = wp_label e t in
      let t = Subst.term s (to_term t) in
      let ne = if is_vty_unit e.e_vty then t_true else t_equ (t_var result) t in
      { ok = t_true;
        post = { ne = ne; s = s };
        exn = Mexn.empty }
  | Evalue v ->
      (* OK: true *)
      (* NE: result = v *)
      let va = wp_label e (t_var v.pv_vs) in
      let ne = Subst.term s (t_equ (t_var result) va) in
      { ok = t_true;
        post = { ne = ne; s = s };
        exn = Mexn.empty }
  | Earrow _ ->
      (* OK: true *)
      (* NE: true *)
      { ok = t_true;
        post = { ne = t_true; s = s };
        exn = Mexn.empty }
  | Eabsurd ->
      (* OK: false *)
      (* NE: false *)
      { ok = wp_label e (wp_expl expl_absurd t_absurd);
        post = { ne = t_false ; s = s };
        exn = Mexn.empty }
  | Eassert (kind, f) ->
      (* assert: OK = f    / NE = f    *)
      (* check : OK = f    / NE = true *)
      (* assume: OK = true / NE = f    *)
      let f = wp_label e (Subst.term s f) in
      let expl =
        match kind with
        | Aassume -> expl_assume
        | Acheck  -> expl_check
        | Aassert -> expl_assert
      in
      let ok = wp_expl expl (if kind = Aassume then t_true else f) in
      let ne = if kind = Acheck then t_true else f in
      { ok = ok;
        post = { ne = ne; s = s };
        exn = Mexn.empty }
  | Eapp (e1, _, spec) ->
      (* OK: ok(e1) /\ (ne(e1) => spec.pre /\ variant) *)
      (* NE: ne(e1) /\ spec.post *)
      (* EX(x): ex(e1)(x) \/ (ne(e1) /\ spec.ex(x)) *)
      let arg_res = vs_result e1 in
      let wp1 = fast_wp_expr env s (arg_res, xresult) e1 in
      (* Next we have to deal with the call itself. *)
      let call_regs = regs_of_writes spec.c_effect in
      let pre_call_label = fresh_mark () in
      let state_before_call = Subst.save_label pre_call_label wp1.post.s in
      let pre =
        wp_label ~override:true e
          (wp_expl expl_pre (Subst.term state_before_call spec.c_pre)) in
      let md =
	create_model_data_opt ~loc:e1.e_loc ~context_labels:e1.e_label "call" in
      let state_after_call, call_glue =
        Subst.havoc md env call_regs state_before_call in
      let xpost = Mexn.map (fun p ->
        { s = state_after_call;
          ne = p }) spec.c_xpost in
      let call_post = { s = state_after_call; ne = spec.c_post } in
      let post, xpost =
        apply_state_to_post call_glue pre_call_label r call_post xpost in
      let variant =
        if spec.c_letrec = 0 || spec.c_variant = [] then t_true else
        let olds = Mint.find_def [] spec.c_letrec env.letrec_var in
        if olds = [] then t_true (* we are out of letrec *) else
        let news =
          List.map (fun (t,rel) ->
            Subst.term state_before_call t, rel) spec.c_variant in
        decrease e.e_loc expl_variant env olds news in
      let ok =
        t_and_simp wp1.ok (wp_implies wp1.post.ne (t_and_simp variant pre)) in
      let ne = wp_label e (t_and_simp wp1.post.ne post.ne) in
      let xne = iter_all_exns [xpost; wp1.exn] (fun ex ->
        let s, post1, post2 =
          merge_opt_post md s (Mexn.find_opt ex wp1.exn) (Mexn.find_opt ex xpost)
        in
        { s = s;
          ne = wp_label e (wp_or post1 (t_and_simp wp1.post.ne post2)) }) in
      { ok = ok;
        post = { ne = ne; s = state_after_call };
        exn = xne }

  | Elet ({ let_sym = LetV v; let_expr = _ }, e2)
  (* ??? can we really ignore the first expression? *)
      when ty_equal v.pv_vs.vs_ty ty_mark ->
        let s = Subst.save_label v.pv_vs s in
        fast_wp_expr env s r e2
  | Erec (fdl, e1) ->
      let fr = fast_wp_rec_defn env fdl in
      let wp1 = fast_wp_expr env s r e1 in
      let ok = wp_label e (wp_and ~sym:true (wp_ands ~sym:true fr) wp1.ok) in
      { ok   = ok;
        post = wp1.post;
        exn = wp1.exn;
      }
  | Elet ({ let_sym = sym; let_expr = e1 }, e2) ->
      (* OK: ok(e1) /\ (ne(e1) => ok(e2)) *)
      (* NE: ne(e1) /\ ne(e2) *)
      (* EX(x): ex(e1)(x) \/ (ne(e1) /\ ex(e2)(x)) *)
      let vs = match sym with | LetV v -> v.pv_vs | LetA _ -> vs_result e1 in
      let e2 =
         if Opt.equal Loc.equal vs.vs_name.id_loc e1.e_loc then
            e_label_copy e e2
         else e2 in
      let wp1 = fast_wp_expr env s (vs, xresult) e1 in
      let md = create_model_data_opt ~loc:e1.e_loc ~context_labels:e1.e_label "let" in
      let wp1posts =
        match sym with
        | LetV v -> Subst.add_pvar md v wp1.post.s
        | _ -> wp1.post.s in
      let wp2 = fast_wp_expr env wp1posts r e2 in
      let ok =
         t_and_simp wp1.ok (t_implies_subst vs wp1.post.ne wp2.ok) in
      let ok = wp_label e ok in
      let ne = wp_label e (t_and_subst vs wp1.post.ne wp2.post.ne) in
      let xne = iter_all_exns [wp1.exn; wp2.exn] (fun ex ->
        let s, post1, post2 =
          merge_opt_post md s (Mexn.find_opt ex wp1.exn) (Mexn.find_opt ex wp2.exn)
        in
        { s = s;
          ne = wp_label e (wp_or post1 (t_and_simp wp1.post.ne post2)) })
      in
      { ok = ok;
        post = { ne = ne; s = wp2.post.s };
        exn = xne }
  | Eif (e1, e2, e3) ->
      (* OK: ok(e1) /\ ne(e1) => (if e1=True then ok(e2) else ok(e3)) *)
      (* NE: ne(e1) /\ (if e1=True then ne(e2) else ne(e3)) *)
      (* EX(x): ex(e1)(x) \/ (ne(e1) /\ e1=True /\ ex(e2)(x))
                          \/ (ne(e1) /\ e1=False /\ ex(e3)(x)) *)
      (* First thing is the evaluation of e1 *)
      let cond_res = vs_result e1 in
      let wp1 = fast_wp_expr env s (cond_res, xresult) e1 in
      let wp2 = fast_wp_expr env wp1.post.s r e2 in
      let wp3 = fast_wp_expr env wp1.post.s r e3 in
      let test = t_equ (t_var cond_res) t_bool_true in
      let ok =
        t_and_simp wp1.ok
          (t_implies_subst cond_res wp1.post.ne
            (t_if_simp test wp2.ok wp3.ok)) in
      let ok = wp_label e ok in
      let md = create_model_data_opt ~loc:e1.e_loc ~context_labels:e1.e_label "if" in
      let state, f2, f3 = Subst.merge md wp1.post.s wp2.post.s wp3.post.s in
      let ne =
        t_and_subst cond_res wp1.post.ne
          (t_if test (t_and_simp wp2.post.ne f2)
                     (t_and_simp wp3.post.ne f3)) in
      let ne = wp_label e ne in
      let xne = iter_all_exns [wp1.exn; wp2.exn; wp3.exn]
        (fun ex ->
          let s, post1, post2, post3 =
            merge_opt_post_3 md s
                (Mexn.find_opt ex wp1.exn)
                (Mexn.find_opt ex wp2.exn)
                (Mexn.find_opt ex wp3.exn) in
          { s = s;
            ne =
              wp_label e (wp_or post1
                                (t_and_subst cond_res wp1.post.ne
                                             (t_if test post2 post3)))
          })
      in
      { ok = ok;
        post = { ne = ne; s = state };
        exn = xne }
  | Eraise (ex, e1) ->
      (* OK: ok(e1) *)
      (* NE: false *)
      (* EX(ex): (ne(e1) /\ xresult=e1) \/ ex(e1)(ex) *)
      (* EX(x): ex(e1)(x) *)
      let ex_res = vs_result e1 in
      let wp1 = fast_wp_expr env s (ex_res, xresult) e1 in
      let rpost =
        (* avoid to introduce useless equation between void terms *)
        if ty_equal (ty_of_vty e1.e_vty) (ty_tuple []) then t_true
        else t_equ (t_var ex_res) (t_var (Mexn.find ex xresult)) in
      let s, ne =
        try
          let p = Mexn.find ex wp1.exn in
	  let md = create_model_data_opt ~loc:e1.e_loc ~context_labels:e1.e_label "raise" in
          let s, r1, r2 = Subst.merge md s p.s wp1.post.s in
          let ne =
            wp_or (t_and_simp p.ne r1)
                  (t_and_simp_l [wp1.post.ne; r2; rpost]) in
          s, ne
        with Not_found ->
          wp1.post.s, t_and_simp wp1.post.ne rpost in
      let expost = { s = Subst.mark s; ne = wp_label e ne } in
      let xne = Mexn.add ex expost wp1.exn in
      { ok = wp1.ok;
        post = { ne = t_false; s = wp1.post.s };
        exn = xne }
  | Etry (e1, handlers) ->
      (* OK: ok(e1) /\ (forall x. ex(e1)(x) => ok(handlers(x))) *)
      (* NE: ne(e1) \/ (bigor x. ex(e1)(x) /\ ne(handlers(x))) *)
      (* EX(x): if x is captured in handlers
          (bigor y. ex(e1)(y) /\ ex(handlers(y))(x)) *)
      (* EX(x): if x is not captured in handlers
          ex(e1)(x) \/ (bigor y. ex(e1)(y) /\ ex(handlers(y))(x)) *)
      let handlers =
        List.fold_left (fun acc (ex,pv,expr) -> Mexn.add ex (pv,expr) acc)
           Mexn.empty handlers in
      let result, xresult = r in
      let xresult' =
         Mexn.fold (fun ex (pv,_) acc ->
            Mexn.add ex pv.pv_vs acc) handlers xresult in
      let wp1 = fast_wp_expr env s (result,xresult') e1 in
      let result =
        Mexn.fold (fun ex post acc -> try
          let _, e2 = Mexn.find ex handlers in
          let wp2 = fast_wp_expr env post.s r e2 in
	  let md = create_model_data_opt ~loc:e1.e_loc ~context_labels:e1.e_label "try" in
          let s,f1,f2 = Subst.merge md s wp1.post.s wp2.post.s in
          let ne =
             wp_or
                (t_and_simp acc.post.ne f1)
                (t_and_simp_l [post.ne; wp2.post.ne; f2]) in
          { ok = t_and_simp acc.ok (t_implies_simp post.ne wp2.ok);
            post = { s = s; ne = ne; };
            exn = Mexn.fold Mexn.add wp2.exn acc.exn
          }
        with Not_found ->
          { acc with exn = Mexn.add ex post acc.exn }
        )
        wp1.exn
        { ok = wp1.ok;
          post = wp1.post;
          exn = Mexn.empty
        }
      in
      result
  | Eabstr (e1, spec) ->
      (* OK: spec.pre /\ ok(e1) /\ (ne(e1) => spec.post)
             /\ (forall x. ex(e1)(x) => spec.xpost(x) *)
      (* NE: spec.post *)
      (* EX: spec.xpost *)
      let pre_abstr_label = fresh_mark () in
      let pre_abstr_state = Subst.save_label pre_abstr_label s in
      let wp1 = fast_wp_expr env pre_abstr_state r e1 in
      let xpost = Mexn.map (fun p ->
        { s = wp1.post.s;
          ne = p }) spec.c_xpost in
      let abstr_post = { s = wp1.post.s; ne = spec.c_post } in
      let post, xpost =
        apply_state_to_post t_true pre_abstr_label r abstr_post xpost in
      let ok_post =
        (* This is the formula which expresses that "abstract" indeed implies
           its normal and exceptional postcondition. Note that we only do this
           for the exceptions that are actually listed. *)
        let wp1_exn_filtered =
          Mexn.filter (fun ex _ -> Mexn.mem ex xpost) wp1.exn in
        let xq = Mexn.mapi (fun ex q -> Mexn.find ex xresult, q.ne) xpost in
        wp_nimplies wp1.post.ne wp1_exn_filtered ((result, post.ne), xq)
      in
      (* We now enrich the xpost used by the context to "leak" information
         about the exceptional exits that are *not* covered by the xpost of the
         abstract expression *)
      let xpost =
        Mexn.fold (fun ex post acc ->
          if Mexn.mem ex acc then acc
          else Mexn.add ex post acc)
        wp1.exn xpost in
      let regs = regs_of_writes e1.e_effect in
      let glue = Subst.extract_glue env regs pre_abstr_state wp1.post.s in
      let post = { post with ne = t_and_simp glue post.ne } in
      let pre = wp_expl expl_pre (Subst.term s spec.c_pre) in
      let ok = t_and_simp_l [wp1.ok; pre ; ok_post] in
      { ok = wp_label e ok;
        post = post;
        exn = xpost
      }
  | Eany spec ->
      (* OK: spec.pre *)
      (* NE: spec.post *)
      (* EX: spec.xpost *)
      let pre_any_label = fresh_mark () in
      let prestate = Subst.save_label pre_any_label s in
      let poststate, glue =
        Subst.havoc None env (regs_of_writes spec.c_effect) prestate in
      let post = { s = poststate; ne = spec.c_post } in
      let xpost =
        Mexn.map (fun p -> { s = poststate; ne = p }) spec.c_xpost in
      let post, xpost =
        apply_state_to_post glue pre_any_label r post xpost in
      let pre = wp_expl expl_pre (Subst.term s spec.c_pre) in
      { ok = wp_label e pre;
        post = post;
        exn = xpost;
      }
  | Eloop (inv, varl, e1) ->
      (* OK: inv /\ (forall r in writes(e1), replace r by fresh r' in
                       inv => (ok(e1) /\ (ne(e1) => inv' /\ var))) *)
      (* NE: inv[r -> r'] *)
      (* EX: ex(e1)[r -> r'] *)
      let md = create_model_data_opt ~loc:e1.e_loc ~context_labels:e1.e_label "loop" in
      let havoc_state, glue = Subst.havoc md env (regs_of_writes e1.e_effect) s in
      let init_inv = wp_expl expl_loop_init (Subst.term s inv) in
      let inv_hypo =
        t_and_simp glue (Subst.term havoc_state inv) in
      let wp1 = fast_wp_expr env havoc_state r e1 in
      let post_inv =
        wp_expl expl_loop_keep (Subst.term wp1.post.s inv) in
        (* preservation also includes the "OK" of the loop body, the overall
           form is:
           I => (OK /\ (NE => I' /\ V))
        *)
      let variant = if varl = []
        then t_true
        else let old_vars = List.map (fun (t,r) ->
            Subst.term havoc_state t,r) varl in
          let new_vars =
            List.map (fun (t,rel) -> Subst.term wp1.post.s t,rel) varl in
          decrease e.e_loc expl_loopvar env old_vars new_vars
      in
      let preserv_inv =
        t_implies_simp inv_hypo
          (t_and_simp wp1.ok
             (t_implies_simp wp1.post.ne (t_and_simp post_inv variant))) in
      let exn =
        Mexn.map (fun post ->
          { post with ne = t_and_simp inv_hypo post.ne }) wp1.exn in
      let ok = t_and_simp_l [init_inv; preserv_inv] in
      { ok = ok;
        post = { s = wp1.post.s; ne = t_false }; (* this is an infinite loop *)
        exn = exn
      }
  | Ecase (e1, bl) ->
      let cond_res = vs_result e1 in
      let wp1 = fast_wp_expr env s (cond_res, xresult) e1 in
      let wps = List.map (fun (_,e) -> fast_wp_expr env wp1.post.s r e) bl in
      let cond_t = t_var cond_res in
      let pats = List.map (fun ({ppat_pattern = pat}, _) -> pat) bl in
      let build_case f l =
        t_case_close_simp cond_t
          (List.map2 (fun pat x -> pat, (f x)) pats l) in
      let ok =
        t_and_simp
          wp1.ok
          (t_implies_subst cond_res wp1.post.ne
                           (build_case (fun wp -> wp.ok) wps))
      in
      let md = create_model_data_opt ~loc:e1.e_loc ~context_labels:e1.e_label "case" in
      let state, fl =
        Subst.merge_l md wp1.post.s (List.map (fun wp -> wp.post.s) wps) in
      let posts = List.map2 (fun f wp -> t_and_simp f wp.post.ne) fl wps in
      let ne =
        t_and_subst cond_res wp1.post.ne
                    (build_case (fun x -> x) posts) in
      let ok = wp_label e ok in
      let ne = wp_label e ne in
      let all_wps = wp1 :: wps in
      let exns = List.map (fun x -> x.exn) all_wps in
      let xne = iter_all_exns exns
        (fun ex ->
          let opt_postl = List.map (fun wp -> Mexn.find_opt ex wp) exns in
          let s, post_l = merge_opt_post_l md s opt_postl in
          match post_l with
          | cond_f :: branches ->
            { s = s;
              ne =
                wp_label e
                  (wp_or cond_f
                      (t_and_subst cond_res wp1.post.ne
                          (build_case (fun b -> b) branches)))
            }
          | _ -> assert false)
      in
      { ok = ok;
        post = { ne = ne; s = state };
        exn = xne
      }
  | Eghost e1 ->
      fast_wp_expr env s r e1
  | Efor ({pv_vs = x}, ({pv_vs = v1}, d, {pv_vs = v2}), inv, e1) ->
      let gt, le, incr = match d with
        | Mlw_expr.To     -> env.ps_int_gt, env.ps_int_le, env.fs_int_pl
        | Mlw_expr.DownTo -> env.ps_int_lt, env.ps_int_ge, env.fs_int_mn
      in
      let one = t_nat_const 1 in
      let v1_gt_v2 = ps_app gt [t_var v1; t_var v2] in
      let v1_le_v2 = ps_app le [t_var v1; t_var v2] in
      let init_inv =
        wp_expl expl_loop_init
          (Subst.term s (t_subst_single x (t_var v1) inv)) in
      let init_inv = t_implies_simp v1_le_v2 init_inv in
      let md = create_model_data_opt ~loc:e1.e_loc ~context_labels:e1.e_label "loop" in
      let havoc_state, glue = Subst.havoc md env (regs_of_writes e1.e_effect) s in
      let inv_hypo =
        t_and_simp_l
          [ps_app le [t_var v1; t_var x];
          ps_app le [t_var x;  t_var v2];
          t_and_simp glue (Subst.term havoc_state inv)]
      in
      let wp1 = fast_wp_expr env havoc_state r e1 in
      let post_inv =
        let next = fs_app incr [t_var x; one] ty_int in
        wp_expl expl_loop_keep
          (Subst.term wp1.post.s (t_subst_single x next inv)) in
      let preserv_inv =
        t_implies_simp inv_hypo
          (t_and_simp wp1.ok
            (t_implies_simp wp1.post.ne post_inv)) in
      let ok = wp_label e (t_and_simp init_inv preserv_inv) in
      let post_state, f1, f2 = Subst.merge md s s wp1.post.s in
      let v2pl1 = fs_app incr [t_var v2; one] ty_int in
      let ne =
        wp_label e
          (t_if_simp v1_le_v2
            (t_and_simp f2
              (Subst.term post_state (t_subst_single x v2pl1 inv)))
            (t_and_simp f1 v1_gt_v2)) in
      let exn =
        Mexn.map (fun post ->
          { post with ne = t_and_simp inv_hypo post.ne }) wp1.exn in
      { ok = ok;
        post = { s = post_state; ne = ne };
        exn = exn
      }
  | Eassign (pl, e1, reg, pv) ->
      let rec get_term d = match d.e_node with
        | Eghost e | Elet (_,e) | Erec (_,e) -> get_term e
        | Evalue v -> vs_result e1, t_var v.pv_vs
        | Elogic t -> vs_result e1, t
        | _ ->
            let ity = ity_of_expr e1 in
            let id = id_fresh ?loc:e1.e_loc "o" in
            (* must be a pvsymbol or restore_pv will fail *)
            let npv = create_pvsymbol id ~ghost:e1.e_ghost ity in
            npv.pv_vs, t_var npv.pv_vs
      in
      let res, t = get_term e1 in
      let t = fs_app pl.pl_ls [t] pv.pv_vs.vs_ty in
      let wp1 = fast_wp_expr env s (res, xresult) e1 in
      let md = create_model_data_opt ~loc:e1.e_loc ~context_labels:e1.e_label "assign" in
      let s2, glue = Subst.havoc md env (Sreg.singleton reg) wp1.post.s in
      let t = Subst.term s2 t in
      let ne =
        t_and_simp_l
          [wp1.post.ne;
           glue;
           t_equ t (t_var pv.pv_vs)]
      in
      {
        ok = wp_label e wp1.ok;
        exn = wp1.exn;
        post = { s = s2; ne = wp_label e ne }
      }

and fast_wp_fun_defn env { fun_lambda = l } =
  (* OK: forall bl. pl => ok(e)
     NE: true *)
  let lab = fresh_mark () and c = l.l_spec in
  let args = List.map (fun pv -> pv.pv_vs) l.l_args in
  let build_set svs =
    Mvs.fold (fun x _ acc -> Spv.add (restore_pv x) acc) svs Spv.empty in
  let pre_vars = build_set (t_vars c.c_pre) in
  let post_vars = build_set (t_vars c.c_post) in
  let all_vars = Spv.union l.l_expr.e_syms.syms_pv pre_vars in
  let all_vars = Spv.union all_vars post_vars in
  let prestate = Subst.init all_vars in
  let prestate = Subst.save_label lab prestate in
  let env =
    if c.c_letrec = 0 || c.c_variant = [] then env else
    let tl = List.map (fun (t,r) -> Subst.term prestate t,r) c.c_variant in
    let lrv = Mint.add c.c_letrec tl env.letrec_var in
    { env with letrec_var = lrv } in
  (* generate the initial state, using the overall effect of the function *)
  (* extract the result and xresult variables *)
  let result, _  = open_post c.c_post in
  let xresult = Mexn.map (fun x -> fst (open_post x)) c.c_xpost in
  (* call the fast wp, using the result variables *)
  let res = fast_wp_expr env prestate (result, xresult) l.l_expr in
  (* put the post of the function in the right format expected by
     adapt_post_to_state_pair. This is doen by wrapping everything in
    [fwp_post] records *)
  let xq =
    Mexn.mapi (fun ex q -> {ne = q; s = (Mexn.find ex res.exn).s }) c.c_xpost in
  let fun_post = { s = res.post.s ; ne = c.c_post } in
  let q, xq = apply_state_to_post t_true lab (result, xresult) fun_post xq in
  (* apply the prestate to the precondition *)
  let pre = Subst.term prestate c.c_pre in
  let xq = Mexn.mapi (fun ex q -> Mexn.find ex xresult, q.ne) xq in
  (* build the formula "forall variables, pre implies OK,
     and NE implies post" *)
  let f =
     t_and_simp res.ok
     (wp_nimplies res.post.ne res.exn ((result, q.ne), xq)) in
  let f = wp_implies pre f in
  let f = wp_forall args (t_forall_close (Mvs.keys (t_vars f)) [] f) in
  f

and fast_wp_rec_defn env fdl = List.map (fast_wp_fun_defn env) fdl

let fast_wp_let env km th { let_sym = lv; let_expr = e } =
  let env = mk_env env km th in
  let res =
    fast_wp_expr env (Subst.init e.e_syms.syms_pv) (result e) e in
  let f = wp_forall (Mvs.keys (t_vars res.ok)) res.ok in
  let id = match lv with
    | LetV pv -> pv.pv_vs.vs_name
    | LetA ps -> ps.ps_name in
  add_wp_decl km id f th

let fast_wp_rec env km th fdl =
  let env = mk_env env km th in
  let fl = fast_wp_rec_defn env fdl in
  let add_one th d f =
    Debug.dprintf debug "wp %s = %a@\n----------------@."
      d.fun_ps.ps_name.id_string Pretty.print_term f;
    let f = wp_forall (Mvs.keys (t_vars f)) f in
    add_wp_decl km d.fun_ps.ps_name f th
  in
  List.fold_left2 add_one th fdl fl

let fast_wp_val _env _km th _lv = th


(* Select either traditional or fast WP *)
let if_fast_wp f1 f2 x = if Debug.test_flag fast_wp then f1 x else f2 x
let wp_val = if_fast_wp fast_wp_val wp_val
let wp_let = if_fast_wp fast_wp_let wp_let
let wp_rec = if_fast_wp fast_wp_rec wp_rec


(* Lemma functions *)

let wp_val ~wp env kn th ls = if wp then wp_val env kn th ls else th
let wp_let ~wp env kn th ld = if wp then wp_let env kn th ld else th

let wp_rec ~wp env kn th fdl =
  let th = if wp then wp_rec env kn th fdl else th in
  let add_one th { fun_ps = ps; fun_lambda = l } =
    let name = ps.ps_name in
    if Slab.mem lemma_label name.id_label then
      let loc = name.id_loc in
      let spec = ps.ps_aty.aty_spec in
      if not (eff_is_empty spec.c_effect) then
        Loc.errorm ?loc "lemma functions can not have effects";
      if not (ity_equal (ity_of_expr l.l_expr) ity_unit) then
        Loc.errorm ?loc "lemma functions must return unit";
      let env = mk_env env kn th in
      let lab = fresh_mark () in
      let args = List.map (fun pv -> pv.pv_vs) l.l_args in
      let q = old_mark lab spec.c_post in
      let f = wp_expr env e_void q Mexn.empty in
      let f = wp_implies spec.c_pre (erase_mark lab f) in
      let md = create_model_data "lemma function" in
      let f = wp_forall args (quantify md  env (wp_fun_regs ps l) f) in
      let f = t_forall_close (Mvs.keys (t_vars f)) [] f in
      let lkn = Theory.get_known th in
      let f = if Debug.test_flag no_track then f else track_values lkn kn f in
      (*let f = if Debug.test_flag no_eval then f else
        Eval_match.eval_match ~inline:Eval_match.inline_nonrec_linear lkn f in*)
      let pr = create_prsymbol (id_clone name) in
      let d = create_prop_decl Paxiom pr f in
      Theory.add_decl ~warn:false th d
    else
      th
  in
  List.fold_left add_one th fdl
