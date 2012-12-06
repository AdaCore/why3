(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Stdlib
open Ident
open Ty
open Term
open Decl
open Theory
open Mlw_ty
open Mlw_ty.T
open Mlw_expr

let debug = Debug.register_info_flag "whyml_wp"
  ~desc:"Print@ details@ of@ verification@ conditions@ generation."

let no_track = Debug.register_flag "wp_no_track"
  ~desc:"Do@ not@ remove@ redundant@ type@ invariant@ conditions@ from@ VCs."

let no_eval = Debug.register_flag "wp_no_eval"
  ~desc:"Do@ not@ simplify@ pattern@ matching@ on@ record@ datatypes@ in@ VCs."

(** Marks *)

let ts_mark = create_tysymbol (id_fresh "'mark") [] None
let ty_mark = ty_app ts_mark []

let vtv_mark = vty_value (ity_pur ts_mark [])

let fresh_mark () = create_vsymbol (id_fresh "'mark") ty_mark

let fs_at =
  let ty = ty_var (create_tvsymbol (id_fresh "a")) in
  create_lsymbol (id_fresh "at") [ty; ty_mark] (Some ty)

let fs_old =
  let ty = ty_var (create_tvsymbol (id_fresh "a")) in
  create_lsymbol (id_fresh "old") [ty] (Some ty)

let th_mark_at =
  let uc = create_theory (id_fresh "WP builtins: at") in
  let uc = add_ty_decl uc ts_mark in
  let uc = add_param_decl uc fs_at in
  close_theory uc

let th_mark_old =
  let uc = create_theory (id_fresh "WP builtins: old") in
  let uc = use_export uc th_mark_at in
  let uc = add_param_decl uc fs_old in
  close_theory uc

let fs_now = create_lsymbol (id_fresh "%now") [] (Some ty_mark)
let t_now = fs_app fs_now [] ty_mark
let e_now = e_lapp fs_now [] (ity_pur ts_mark [])

(* [vs_old] appears in the postconditions given to the core API,
   which expects every vsymbol to be a pure part of a pvsymbol *)
let pv_old = create_pvsymbol (id_fresh "%old") vtv_mark
let vs_old = pv_old.pv_vs
let t_old  = t_var vs_old

let t_at_old t = t_app fs_at [t; t_old] t.t_ty

let ls_absurd = create_lsymbol (id_fresh "absurd") [] None
let t_absurd  = ps_app ls_absurd []

let mk_t_if f = t_if f t_bool_true t_bool_false
let to_term t = if t.t_ty = None then mk_t_if t else t

let vtv_of_vs (vs : vsymbol) =
  (* return the type of the program variable that corresponds to [vs] *)
  (* any vs in post/xpost is either a pvsymbol or a fresh mark *)
  try (restore_pv vs).pv_vtv with Not_found -> vtv_mark

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

(* replace ['old] by a fresh label in q and xq, and call the argument *)
let backstep fn (q : term) xq =
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

let wp_label e f =
  let loc = if f.t_loc = None then e.e_loc else f.t_loc in
  let lab = Ident.Slab.union e.e_label f.t_label in
  t_label ?loc lab f

let expl_pre       = Ident.create_label "expl:precondition"
let expl_post      = Ident.create_label "expl:postcondition"
let expl_xpost     = Ident.create_label "expl:exceptional postcondition"
let expl_assume    = Ident.create_label "expl:assumption"
let expl_assert    = Ident.create_label "expl:assertion"
let expl_check     = Ident.create_label "expl:check"
let expl_type_inv  = Ident.create_label "expl:type invariant"
let expl_loop_init = Ident.create_label "expl:loop invariant init"
let expl_loop_keep = Ident.create_label "expl:loop invariant preservation"
let expl_loopvar   = Ident.create_label "expl:loop variant decrease"
let expl_variant   = Ident.create_label "expl:variant decrease"

let rec wp_expl l f = match f.t_node with
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

let wp_forall_post v p f =
  (* we optimize for the case when a postcondition
     is of the form (... /\ result = t /\ ...) *)
  let rec down p = match p.t_node with
    | Tbinop (Tand,l,r) ->
        begin match down l with
          | None, _ ->
              let t, r = down r in
              t, t_label_copy p (t_and_simp l r)
          | t, l ->
              t, t_label_copy p (t_and_simp l r)
        end
    | Tapp (ps,[{t_node = Tvar u};t])
      when ls_equal ps ps_equ && vs_equal u v && not (Mvs.mem v t.t_vars) ->
        Some t, t_true
    | _ ->
        None, p
  in
  if ty_equal v.vs_ty ty_unit then
    t_subst_single v t_void (wp_implies p f)
  else match down p with
    | Some t, p -> wp_let v t (wp_implies p f)
    | _ -> wp_forall [v] (wp_implies p f)

let is_equality_for v t =
  (* check whether [t] is an equality defining variable [v], that is, of the
     form [ x = def] for some term [def]. If so, return [Some def], otherwise
     return [None] *)
  match t.t_node with
  | Tapp (ls, [ { t_node = Tvar eq_v } ; t2 ])
          when ls_equal ls ps_equ && vs_equal eq_v v ->
            Some t2
  | _ -> None

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

(* regs_of_reads, and therefore regs_of_effect, only take into account
   reads in program expressions and ignore the variables in specification *)
(* dead code
let regs_of_reads  eff = Sreg.union eff.eff_reads eff.eff_ghostr
*)
let regs_of_writes eff = Sreg.union eff.eff_writes eff.eff_ghostw
(* dead code
let regs_of_effect eff = Sreg.union (regs_of_reads eff) (regs_of_writes eff)
*)
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
  letrec_var : term list Mint.t;
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
  let add_arg acc fty =
    let fty = ty_inst sbs fty in
    if ty_equal fty nty then
      let vs = create_vsymbol (id_fresh "f") nty in
      t_or_simp acc (t_equ (t_var vs) t), pat_var vs
    else acc, pat_wild fty in
  let add_cs (cs,_) =
    let f, pl = Lists.map_fold_left add_arg t_false cs.ls_args in
    t_close_branch (pat_app cs pl oty) f in
  t_case old_t (List.map add_cs csl)

let decrease_rel ?loc env old_t t = function
  | Some ls -> ps_app ls [t; old_t]
  | None when ty_equal (t_type t) ty_int ->
      t_and
        (ps_app env.ps_int_le [t_nat_const 0; old_t])
        (ps_app env.ps_int_lt [t; old_t])
  | None -> decrease_alg ?loc env old_t t

let decrease loc lab env olds varl =
  let rec decr pr olds varl = match olds, varl with
    | [], [] -> (* empty variant *)
        t_true
    | [old_t], [t, rel] ->
        t_and_simp pr (decrease_rel ?loc env old_t t rel)
    | old_t::_, (t,_)::_ when not (oty_equal old_t.t_ty t.t_ty) ->
        Loc.errorm ?loc "cannot use lexicographic ordering"
    | old_t::olds, (t,rel)::varl ->
        let dt = t_and_simp pr (decrease_rel ?loc env old_t t rel) in
        let pr = t_and_simp pr (t_equ old_t t) in
        t_or_simp dt (decr pr olds varl)
    | _ -> assert false
  in
  t_label ?loc lab (decr t_true olds varl)

let expl_variant = Slab.add Split_goal.stop_split (Slab.singleton expl_variant)
let expl_loopvar = Slab.add Split_goal.stop_split (Slab.singleton expl_loopvar)

(** Reconstruct pure values after writes *)

let analyze_var fn_down fn_join lkm km vs ity =
   (* create a term of the form:
        match vs with
        (| Cons (x1 ... xn) -> fn_join x1' ... xn')*
      where the x1' are obtained by a call to fn_down (supposedly a recursive
      call) on x1 and its type *)
  let branch (cs,vtvl) =
    let mk_var vtv = create_vsymbol (id_fresh "y") (ty_of_ity vtv.vtv_ity) in
    let vars = List.map mk_var vtvl in
     let args = List.map2 fn_down vars vtvl in
    let t = fn_join cs args  vs.vs_ty in
    let pat = pat_app cs (List.map pat_var vars) vs.vs_ty in
    t_close_branch pat t in
  let constructors = Mlw_decl.inst_constructors lkm km ity in
  t_case (t_var vs) (List.map branch constructors)

let update_var env (mreg : vsymbol Mreg.t) (vs : vsymbol) : term =
   (* [mreg] is expected to contain fresh names for all to-be-updated regions.
      this function does nothing (ie returns the term [vs]) when [vs]
      corresponds to a program variable whose type does not contain any region
      in [mreg]. In the other case, this function builds a new term, replacing
      all touched regions by fresh variables. *)
  let rec update vs { vtv_ity = ity; vtv_mut = mut } =
    (* are we a mutable variable? *)
    let get_vs r = Mreg.find_def vs r mreg in
    let vs = Opt.fold (fun _ -> get_vs) vs mut in
    (* at this point, vs is either itself (vtv_mut is None, or the contained
     * region is not in the map), or the vsymbol in the map mreg *)
    (* should we update our value further? *)
    let check_reg r _ = reg_occurs r ity.ity_vars in
    if ity_pure ity || not (Mreg.exists check_reg mreg) then t_var vs
    else analyze_var update fs_app env.pure_known env.prog_known vs ity
  in
  update vs (vtv_of_vs vs)

let rec subst_at_now now (m : vsymbol Mvs.t) (t : term) =
   (* if [now] is true, apply the substitution, except when they are protected
      by labels other than [fs_now] *)
   match t.t_node with
  | Tvar vs when now ->
      begin try t_var (Mvs.find vs m) with Not_found -> t end
  | Tapp (ls, _) when ls_equal ls fs_old -> assert false
  | Tapp (ls, [_; mark]) when ls_equal ls fs_at ->
      let now = match mark.t_node with
        | Tvar vs when vs_equal vs vs_old -> assert false
        | Tapp (ls,[]) when ls_equal ls fs_now -> true
        | _ -> false in
      t_map (subst_at_now now m) t
  | Tlet _ | Tcase _ | Teps _ | Tquant _ ->
      (* do not open unless necessary *)
      let m = Mvs.set_inter m t.t_vars in
      if Mvs.is_empty m then t else
      t_map (subst_at_now now m) t
  | _ ->
      t_map (subst_at_now now m) t

let model1_lab = Slab.singleton (create_label "model:1")
let model2_lab = Slab.singleton (create_label "model:quantify(2)")
let model3_lab = Slab.singleton (create_label "model:cond")

let mk_var id label ty : vsymbol = create_vsymbol (id_clone ~label id) ty

let print_region_map mreg =
   Format.printf "{ ";
   Mreg.iter (fun k v ->
      Format.printf "%a |-> %a (%a)@ ;"
         Mlw_pretty.print_reg k
         Pretty.print_vs v
         Pretty.print_ty v.vs_ty) mreg;
   Format.printf " }@."

let mutable_substitute env (mreg : vsymbol Mreg.t) (f : term) =
  (* Replace every occurrence of a mutable variable in [f] by an appropriate
     "updating" term. The map [mreg] must already contain fresh variables for
     all regions. *)
  let update_var vs _ = match update_var env mreg vs with
    | { t_node = Tvar nv } when vs_equal vs nv -> None
    | t -> Some t in
  (*   print_region_map mreg; *)
  let vars = Mvs.mapi_filter update_var f.t_vars in
  (* [vars] now is a mapping from the relevant symbols of [f] to their
     "update" (see [update_var]) *)
  let new_var vs _ = mk_var vs.vs_name model2_lab vs.vs_ty in
  let vv' = Mvs.mapi new_var vars in
  (* [vv'] is now a mapping from the relevant symbols in f to fresh symbols *)
  let update v t f = wp_let (Mvs.find v vv') t f in
  Mvs.fold update vars (subst_at_now true vv' f)

let get_var_of_region reg f =
   (* If term [f] has a variable [v] that belongs to region [reg],
      return [Some v], else return [None]
   *)
    let test vs _ acc =
      if acc <> None then acc
      else
      (* this does the actual comparison *)
         match vtv_of_vs vs with
         | { vtv_ity = { ity_node = Ityapp (_,_,[r]) }}
         | { vtv_mut = Some r } when reg_equal r reg -> Some vs
         | _ -> acc
    in
    Mvs.fold test f.t_vars None

let quantify env (regs : Sreg.t) (f : term) =
   (* quantify formula [f] over all variables in the regions [regs] *)
   (* ??? refactor this first bit to use [get_var_of_region] *)
  let get_var reg () =
     (* for each free variable in [f], compare its region with [reg];
        if it matches, return the variable as the one that corresponds to the
        region *)
    let test vs _ id =
       (* this does the actual comparison *)
      match vtv_of_vs vs with
      | { vtv_ity = { ity_node = Ityapp (_,_,[r]) }}
      | { vtv_mut = Some r } when reg_equal r reg -> vs.vs_name
      | _ -> id in
    let id = Mvs.fold test f.t_vars reg.reg_name in
    mk_var id model1_lab (ty_of_ity reg.reg_ity)
  in
  let mreg = Mreg.mapi get_var regs in
  (* [mreg] now maps each region to a fresh variable *)
  let f = mutable_substitute env mreg f in
  wp_forall (List.rev (Mreg.values mreg)) f

(** Invariants *)

let get_invariant km t =
  let ty = t_type t in
  let ts = match ty.ty_node with
    | Tyapp (ts,_) -> ts
    | _ -> assert false in
  let rec find_td = function
    | (its,_,inv) :: _ when ts_equal ts its.its_pure -> inv
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
  let rec update vs { vtv_ity = ity } =
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
  update vs (vty_value ity)

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
        lesson, t_true
      else
        let good c = not (contains c cond) in
        let condl = List.filter good condl in
        let l = Mint.add p1 (cond::condl) lesson in
        l, get_invariant state.st_km t1
  | Tbinop (Timplies, f1, f2) ->
      let l, f1 = track_values state names lesson cond f1 in
      let _, f2 = track_values state names l cond f2 in
      lesson, t_label_copy f (t_implies_simp f1 f2)
  | Tbinop (Tand, f1, f2) ->
      let l, f1 = track_values state names lesson cond f1 in
      let l, f2 = track_values state names l cond f2 in
      l, t_label_copy f (t_and_simp f1 f2)
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
      l, t_label_copy f (t_case t1 bl)
  | Tlet (t1, bf) ->
      let p1 = point_of_term state names t1 in
      let v, f1, cb = t_open_bound_cb bf in
      let names = Mvs.add v p1 names in
      let l, f1 = track_values state names lesson cond f1 in
      l, t_label_copy f (t_let_simp t1 (cb v f1))
  | Tquant (Tforall, qf) ->
      let vl, trl, f1, cb = t_open_quant_cb qf in
      let add_vs s vs = Mvs.add vs (next_point state) s in
      let names = List.fold_left add_vs names vl in
      let l, f1 = track_values state names lesson cond f1 in
      l, t_label_copy f (t_forall_simp (cb vl trl f1))
  | Tbinop ((Tor|Tiff),_,_) | Tquant (Texists,_)
  | Tapp _ | Tnot _ | Ttrue | Tfalse -> lesson, f
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
      t_subst_single v (to_term t) q
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
      let fr = wp_rec_defn env fdl in
      let fe = wp_expr env e1 q xq in
      let fr = wp_ands ~sym:true fr in
      wp_label e (wp_and ~sym:true fr fe)
  | Eif (e1, e2, e3) ->
      let res = vs_result e1 in
      let test = t_equ (t_var res) t_bool_true in
      let test = t_label ?loc:e1.e_loc model3_lab test in
      (* if both branches are pure, do not split *)
      let w =
        let get_term e = match e.e_node with
          | Elogic t -> to_term t
          | Evalue v -> t_var v.pv_vs
          | _ -> raise Exit in
        try
          let r2 = get_term e2 in
          let r3 = get_term e3 in
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
      let w = t_case (t_var res) (List.map branch bl) in
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
      wp_label e t_absurd
  | Eany spec ->
      let p = wp_label e (wp_expl expl_pre spec.c_pre) in
      let p = t_label ?loc:e.e_loc p.t_label p in
      (* TODO: propagate call labels into tyc.c_post *)
      let w = wp_abstract env spec.c_effect spec.c_post spec.c_xpost q xq in
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
      let w = wp_abstract env spec.c_effect spec.c_post spec.c_xpost q xq in
      let w = wp_and ~sym:true d (wp_and ~sym:false p w) in
      let q = create_unit_post w in
      wp_expr env e1 q xq (* FIXME? should (wp_label e) rather be here? *)
  | Eabstr (e1, spec) ->
      let p = wp_label e (wp_expl expl_pre spec.c_pre) in
      let w1 = backstep (wp_expr env e1) spec.c_post spec.c_xpost in
      let w2 = wp_abstract env e1.e_effect spec.c_post spec.c_xpost q xq in
      wp_and ~sym:false p (wp_and ~sym:true (wp_label e w1) w2)
  | Eassign (e1, reg, pv) ->
      let rec get_term d = match d.e_node with
        | Elogic t -> t
        | Evalue v -> t_var v.pv_vs
        | Eghost e | Elet (_,e) | Erec (_,e) -> get_term e
        | _ -> Loc.errorm ?loc:e.e_loc
            "Cannot compute the WP for this assignment"
      in
      let f = t_equ (get_term e1) (t_var pv.pv_vs) in
      let c_q = create_unit_post f in
      let eff = eff_write eff_empty reg in
      let w = wp_abstract env eff c_q Mexn.empty q xq in
      let q = create_post (vs_result e1) w in
      wp_label e (wp_expr env e1 q xq)
  | Eloop (inv, varl, e1) ->
      (* TODO: what do we do about well-foundness? *)
      let i = wp_expl expl_loop_keep inv in
      let olds = List.map (fun (t,_) -> t_at_old t) varl in
      let d = decrease e.e_loc expl_loopvar env olds varl in
      let q = create_unit_post (wp_and ~sym:true i d) in
      let w = backstep (wp_expr env e1) q xq in
      let regs = regs_of_writes e1.e_effect in
      let w = quantify env regs (wp_implies inv w) in
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
      let wp_good = wp_and ~sym:true
        wp_init
        (quantify env (regs_of_writes e1.e_effect)
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

and wp_abstract env c_eff c_q c_xq q xq =
  let regs = regs_of_writes c_eff in
  let exns = exns_of_raises c_eff in
  let quantify_post c_q q =
    let v, f = open_post q in
    let c_v, c_f = open_post c_q in
    let c_f = t_subst_single c_v (t_var v) c_f in
    let f = wp_forall_post v c_f f in
    quantify env regs f
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

and wp_fun_defn env { fun_ps = ps ; fun_lambda = l } =
  let lab = fresh_mark () and c = l.l_spec in
  let add_arg sbs pv = ity_match sbs pv.pv_vtv.vtv_ity pv.pv_vtv.vtv_ity in
  let subst = List.fold_left add_arg ps.ps_subst l.l_args in
  let regs = Mreg.map (fun _ -> ()) subst.ity_subst_reg in
  let args = List.map (fun pv -> pv.pv_vs) l.l_args in
  let env =
    if c.c_letrec = 0 || c.c_variant = [] then env else
    let lab = t_var lab in
    let t_at_lab (t,_) = t_app fs_at [t; lab] t.t_ty in
    let tl = List.map t_at_lab c.c_variant in
    let lrv = Mint.add c.c_letrec tl env.letrec_var in
    { env with letrec_var = lrv } in
  let q = old_mark lab (wp_expl expl_post c.c_post) in
  let conv p = old_mark lab (wp_expl expl_xpost p) in
  let f = wp_expr env l.l_expr q (Mexn.map conv c.c_xpost) in
  let f = wp_implies c.c_pre (erase_mark lab f) in
  wp_forall args (quantify env regs f)

and wp_rec_defn env fdl = List.map (wp_fun_defn env) fdl

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
      t_label_copy f t_false
  | _ ->
      t_map unabsurd f

let add_wp_decl km name f uc =
  (* prepare a proposition symbol *)
  let s = "WP_parameter " ^ name.id_string in
  let lab = Ident.create_label ("expl:VC for " ^ name.id_string) in
  let label = Slab.add lab name.id_label in
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
  let th_int = Env.find_theory env ["int"] "Int" in
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
  let f = wp_forall (Mvs.keys f.t_vars) f in
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
    let f = wp_forall (Mvs.keys f.t_vars) f in
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

   val init : effect -> t
   (* the initial substitution for a program with given effects *)

   val init_reg : Sreg.t -> t
   (* the initial substitution given a set of regions *)

   val empty : t
   (* the empty substitution *)

   val refresh : Sreg.t -> t -> t
   (* refresh the state, ie, generate new names for all variables in the region
      set *)

   val term : wp_env -> t -> term -> term
   (* In the given term, substitute the variables that refer to the current
      state by the symbols that stand for the value of these variables at this
      point in execution, as recorded in subtitution [t]. *)

   val merge_states : t -> Sreg.t * t -> Sreg.t * t -> t * term * term
   (* Given a base state and two branches (represented by written regions in
      each branch, and a state), return the state of the join point of the
      branches, and two formulas. The first formula links the first branch
      state with the join state, the second formula links the second branch
      state with the join state. *)

end = struct

  type t = vsymbol option ref Mreg.t
  (* Each region is mapped to a reference, which represents the name of the
     region. At beginning, this reference points to [None], meaning that the
     name of the region is not yet decided. When needed, the value under the
     reference is changed to [Some v], with [v] a fresh variable symbol, to fix
     the name of the region. This delayed choice of name allows getting better
     names for regions, so a region for variable [x] ends up called something
     like [x1] instead of the generic [rho1]. *)

  let name_from_region ?hint ?id reg =
    let id = match id with
      | Some x ->
          (* an id was provided, take it *)
          x
      | None ->
          (* none was provided, maybe there was a hint state *)
          begin match hint with
            | None ->
                (* no hint, return default *)
                reg.reg_name
            | Some s ->
                begin try match !(Mreg.find reg s) with
                  | None ->
                      (* the hint state also contains no id, return default *)
                      reg.reg_name
                  | Some x ->
                      (* the hint state contains something, take it *)
                      x.vs_name
                  with Not_found ->
                    (* the hint state has no entry for that region,
                       return default *)
                    reg.reg_name
                end
          end
    in
    mk_var id Slab.empty (ty_of_ity reg.reg_ity)

  let init_reg reg =
    Mreg.map (fun () -> ref None) reg

  let init effect =
    init_reg effect.eff_writes

  let empty = Mreg.empty

  let refresh regset s =
     Sreg.fold (fun reg acc -> Mreg.add reg (ref None) acc) regset s

  let get_region v =
    match vtv_of_vs v with
      | {vtv_ity = {ity_node = Ityapp (_,_,[r]) }}
      | { vtv_mut = Some r} -> Some r
      | _ -> None

  let term env sub t =
     let mreg = Mreg.mapi_filter (fun reg vr ->
        match !vr with
        | Some _ -> !vr
        | None ->
              match get_var_of_region reg t with
              | Some v ->
                    let v' = name_from_region ~id:v.vs_name reg in
                    vr := Some v';
                    !vr
              | None -> None) sub in
     let r = mutable_substitute env mreg t in
     r

  let show_state fmt s =
     Format.fprintf fmt "{ ";
     Mreg.iter (fun k rv ->
        match !rv with
        | Some v ->
            Format.fprintf fmt " %a |-> %a; @ "
              Mlw_pretty.print_reg k Pretty.print_vs v;

        | None ->
            Format.fprintf fmt " %a |-> _; @  "
              Mlw_pretty.print_reg k) s;
     Format.fprintf fmt "}"

  (* Update the name of region [reg] in substitution [s], possibly based on
     the provided [hint], and return a variable of that name. *)
  let region_name ?hint reg s =
    let rv = Mreg.find reg s in
    match !rv with
      | Some x -> t_var x
      | None ->
          let new_name = name_from_region ?hint reg in
          rv := Some new_name;
          t_var (new_name)

  let merge_states base (reg1,s1) (reg2,s2) =
    let all_regs = Sreg.union reg1 reg2 in
    Sreg.fold
      (fun reg (s, f1, f2) ->
         (* If both branches modify region [reg], pick the name from [s2], and
            add the necessary equations to [f1]. Otherwise, pick the name from
            the branch that modifies [reg], and add the necessary equations to
            the formula for the other branch.*)
         if Sreg.mem reg reg1 && Sreg.mem reg reg2 then begin
           Mreg.add reg (Mreg.find reg s2) s,
           t_and_simp f1 (t_equ (region_name reg s2) (region_name reg s1)),
           f2
         end else if Sreg.mem reg reg2 then begin
           Mreg.add reg (Mreg.find reg s2) s,
           t_and_simp f1 (t_equ (region_name reg s2)
                            (region_name ~hint:s2 reg base)),
           f2
         end else begin
           Mreg.add reg (Mreg.find reg s1) s,
           f1,
           t_and_simp f2 (t_equ (region_name reg s1)
                            (region_name ~hint:s1 reg base))
         end) all_regs (base, t_true, t_true)

end

let fastwp_or_label = Ident.create_label "fastwp:or"
let wp_or f1 f2 = t_label_add fastwp_or_label (t_or_simp f1 f2)
let wp_ors l = List.fold_left wp_or t_false l

let xs_result xs = create_vsymbol (id_fresh "result") (ty_of_ity xs.xs_ity)
let result e =
  vs_result e, Mexn.mapi (fun xs _ -> xs_result xs) e.e_effect.eff_raises

let is_vty_unit = function
  | VTvalue vtv -> ity_equal vtv.vtv_ity ity_unit
  | VTarrow _   -> false

let map_exns e f = Mexn.mapi (fun xs _ -> f xs) e.e_effect.eff_raises

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
type fast_wp_result =
   { ok   : term;
     post : fwp_post;
     exn  : fast_wp_exn_map }

let wp_nimplies (n : term) (xn : fast_wp_exn_map) ((result, q), xq) =
  let f = wp_forall [result] (wp_implies n q) in
  assert (Mexn.cardinal xn = Mexn.cardinal xq);
  let x_implies _xs { ne = n } (xresult, q) f =
    wp_forall [xresult] (t_and_simp f (wp_implies n q)) in
  Mexn.fold2_inter x_implies xn xq f

type res_type = vsymbol * vsymbol Mexn.t

(* Take a [post], and place the postcondition [post.ne] in the
   prestate/poststate pair defined by ([prestate], [post.s]). Also, open the
   postcondition and replace the result variable by [result_var]. Internally, a
   label is used to deal with 'old; if "lab" is given, use that label instead
   of creating one. *)
let adapt_single_post_to_state_pair ?lab env prestate result_var post =
  let lab = match lab with | None -> fresh_mark () | Some lab -> lab in
  (* get the result var of the post *)
  let res, ne = open_post post.ne in
  (* substitute for given result var, and replace 'old *)
  let ne = t_subst_single res (t_var result_var) (old_mark lab ne) in
  (* apply the poststate *)
  let ne = Subst.term env post.s ne in
  (* remove the label that protected "old" variables *)
  let ne = erase_mark lab ne in
  (* apply the prestate = replace previously "old" variables *)
  { post with ne = Subst.term env prestate ne }

(* Given normal and exceptional [post,xpost], each with its
   own poststate, place all [(x)post.ne] in the prestate/poststate pair defined
   by [prestate] and [(x)post.s].*)
let adapt_post_to_state_pair ?lab
   env prestate result_vars post (xpost : fast_wp_exn_map)
   : fwp_post * fast_wp_exn_map =
  let result, xresult = result_vars in
  let f = adapt_single_post_to_state_pair ?lab env prestate in
  f result post,
  Mexn.mapi (fun ex post -> f (Mexn.find ex xresult) post) xpost

let either_state base (reg1, s1, f1) (reg2, s2, f2) =
  (* Starting from a base state, and two branches identified by their
     effects, state and postcondition, return a merged state and two formulas;
     the first formula improves the first postcondition, the second one the
     second postcondition. *)
  let s, eq1, eq2 = Subst.merge_states base (reg1, s1) (reg2, s2) in
  s, t_and_simp f1 eq1, t_and_simp f2 eq2

let get_exn reg ex xmap =
  try Mexn.find ex xmap
  with Not_found -> { s = Subst.init_reg reg; ne = t_false }

let all_exns xmap_list =
  let add_elt k _ acc = Sexn.add k acc in
  List.fold_left (fun acc map ->
    Mexn.fold add_elt map acc)
    Sexn.empty
    xmap_list

let iter_exns exns f =
  Sexn.fold (fun x acc ->
    let v = f x in
    Mexn.add x v acc) exns Mexn.empty

let iter_all_exns xmap_list f =
  iter_exns (all_exns xmap_list) f

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
   ``e raises exception x, with final state sw and value xresult(x) in x''
*)
let rec fast_wp_expr (env : wp_env) (s : Subst.t) (r : res_type) (e : expr)
    : fast_wp_result =
  let res = fast_wp_desc env s r e in
  if Debug.test_flag debug then begin
    Format.eprintf "@[--------@\n@[<hov 2>e = %a@]@\n" Mlw_pretty.print_expr e;
    Format.eprintf "@[<hov 2>OK = %a@]@\n" Pretty.print_term res.ok;
  end;
  res

(* In every case of this function, we have to (potentially) deal with:
   "old"
   exceptions
   effects
   result variable
   tracability
*)

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
      let t = Subst.term env s (to_term t) in
      let ne = if is_vty_unit e.e_vty then t_true else t_equ (t_var result) t in
      { ok = t_true;
        post = { ne = ne; s = s };
        exn = Mexn.empty }
  | Evalue v ->
      (* OK: true *)
      (* NE: result = v *)
      let va = wp_label e (t_var v.pv_vs) in
      let ne = Subst.term env s (t_equ (t_var result) va) in
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
      { ok = t_false;
        post = { ne = t_false ; s = s };
        exn = Mexn.empty }
  | Eassert (kind, f) ->
      (* assert: OK = f    / NE = f    *)
      (* check : OK = f    / NE = true *)
      (* assume: OK = true / NE = f    *)
      let f = wp_label e (Subst.term env s f) in
      let ok = if kind = Aassume then t_true else f in
      let ne = if kind = Acheck then t_true else f in
      { ok = ok;
        post = { ne = ne; s = s };
        exn = Mexn.empty }
  | Eapp (e1, _, spec) ->
      (* OK: ok(e1) /\ (ne(e1) => spec.pre) *)
      (* NE: ne(e1) /\ spec.post *)
      (* EX(x): ex(e1)(x) \/ (ne(e1) /\ spec.ex(x)) *)
      (* The first thing that happens, before the call, is the evaluation of
         [e1]. This translates as a recursive call to the fast_wp. *)
      let arg_res = create_vsymbol (id_fresh "tmp") (ty_of_vty e1.e_vty) in
      let wp1 = fast_wp_expr env s (arg_res, xresult) e1 in
      (* Next we have to deal with the call itself. *)
      let e1_regs = regs_of_writes e1.e_effect in
      let call_regs = regs_of_writes spec.c_effect in
      let state_after_call = Subst.refresh call_regs wp1.post.s in
      let pre = wp_label e (Subst.term env wp1.post.s spec.c_pre) in
      let xpost = Mexn.map (fun p ->
        { s = state_after_call;
          ne = p }) spec.c_xpost in
      let call_post = { s = state_after_call; ne = spec.c_post } in
      let post, xpost =
        adapt_post_to_state_pair
          env
          wp1.post.s
          r
          call_post
          xpost in
        let ok = wp_and ~sym:false wp1.ok (wp_implies wp1.post.ne pre) in
        let ne = t_and_simp wp1.post.ne post.ne in
        let xne = iter_all_exns [xpost; wp1.exn] (fun ex ->
          let p2_effect = Sreg.union e1_regs call_regs in
          let p1 = get_exn e1_regs ex wp1.exn in
          let p2 = get_exn p2_effect ex xpost in
          let s, r1, r2 =
            Subst.merge_states s (e1_regs, p1.s) (p2_effect, p2.s) in
          { s = s;
            ne =
              wp_or (t_and_simp p1.ne r1)
                    (t_and_simp_l [p2.ne; r2; wp1.post.ne])
          }) in
        { ok = ok;
          post = { ne = ne; s = state_after_call };
          exn = xne }
  | Elet ({ let_sym = LetV v; let_expr = e1 }, e2) ->
      (* OK: ok(e1) /\ (ne(e1) => ok(e2)) *)
      (* NE: ne(e1) /\ ne(e2) *)
      (* EX(x): ex(e1)(x) \/ (ne(e1) /\ ex(e2)(x)) *)
      let v = v.pv_vs in
      let e2 =
         if Opt.equal Loc.equal v.vs_name.id_loc e1.e_loc then
            e_label_copy e e2
         else e2 in
      let wp1 = fast_wp_expr env s (v, xresult) e1 in
      let wp2 = fast_wp_expr env wp1.post.s r e2 in
      let ok =
         wp_and ~sym:false wp1.ok (t_implies_subst v wp1.post.ne wp2.ok) in
      let ok = wp_label e ok in
      let e1_regs = regs_of_writes e1.e_effect in
      let e2_regs = regs_of_writes e2.e_effect in
      let ne = wp_label e (t_and_subst v wp1.post.ne wp2.post.ne) in
      let xne = iter_all_exns [wp1.exn; wp2.exn] (fun ex ->
        let p2_effect = Sreg.union e1_regs e2_regs in
        let p1 = get_exn e1_regs ex wp1.exn in
        let p2 = get_exn p2_effect ex wp2.exn in
        let s, r1, r2 =
           Subst.merge_states s (e1_regs, p1.s)
                                (p2_effect, p2.s) in
        { s = s;
          ne =
            wp_or (t_and_simp p1.ne r1)
                  (t_and_simp_l [p2.ne; r2; wp1.post.ne])
        }) in
      { ok = ok;
        post = { ne = ne; s = wp2.post.s };
        exn = xne }
  | Eif (e1, e2, e3) ->
      (* OK: ok(e1) /\ ne(e1) => (if e1=True then ok(e2) else ok(e3)) *)
      (* NE: ne(e1) /\ (if e1=True then ne(e2) else ne(e3)) *)
      (* EX(x): ex(e1)(x) \/ (ne(e1) /\ e1=True /\ ex(e2)(x))
                          \/ (ne(e1) /\ e1=False /\ ex(e3)(x)) *)
      (* First thing is the evaluation of e1 *)
      let cond_res = create_vsymbol (id_fresh "c") (ty_of_vty e1.e_vty) in
      let wp1 = fast_wp_expr env s (cond_res, xresult) e1 in
      let wp2 = fast_wp_expr env wp1.post.s r e2 in
      let wp3 = fast_wp_expr env wp1.post.s r e3 in
      let e1_regs = regs_of_writes (e1.e_effect) in
      let e2_regs = regs_of_writes (e2.e_effect) in
      let e3_regs = regs_of_writes (e3.e_effect) in
      let test = t_equ (t_var cond_res) t_bool_true in
      let ok =
        t_and_simp wp1.ok
          (t_implies_subst cond_res wp1.post.ne
            (t_if_simp test wp2.ok wp3.ok)) in
      let ok = wp_label e ok in
      let state, f1, f2 =
        either_state wp1.post.s
           (e2_regs, wp2.post.s, wp2.post.ne)
           (e3_regs, wp3.post.s, wp3.post.ne) in
      let ne =
        t_and_subst cond_res wp1.post.ne (t_if test f1 f2) in
      let ne = wp_label e ne in
      let xne = iter_all_exns [wp1.exn; wp2.exn; wp3.exn]
        (fun ex ->
          let post2 = get_exn e2_regs ex wp2.exn in
          let post3 = get_exn e3_regs ex wp3.exn in
          let s23, r2, r3 =
            Subst.merge_states wp1.post.s (e2_regs, post2.s)
                                          (e3_regs, post3.s) in
          let post1 = get_exn e1_regs ex wp1.exn in
          let s', q1, q23 =
            Subst.merge_states s
              (e1_regs, post1.s)
              (Sreg.union e1_regs (Sreg.union e2_regs e3_regs), s23) in
          let first_case = t_and_simp q1 post1.ne in
          let second_case =
            t_and_subst cond_res wp1.post.ne
               (t_and_simp_l [test; post2.ne; q23; r2]) in
          let third_case =
            t_and_subst cond_res wp1.post.ne
                (t_and_simp_l [t_not test; post3.ne; q23; r3]) in
          let ne = wp_ors [first_case; second_case; third_case] in
          { ne = ne; s = s' }) in
      { ok = ok;
        post = { ne = ne; s = state };
        exn = xne }
  | Eraise (ex, e1) ->
      (* OK: ok(e1) *)
      (* NE: false *)
      (* EX(ex): (ne(e1) /\ xresult=e1) \/ ex(e1)(ex) *)
      (* EX(x): ex(e1)(x) *)
      let ex_res = create_vsymbol (id_fresh "x") (ty_of_vty e1.e_vty) in
      let wp1 = fast_wp_expr env s (ex_res, xresult) e1 in
      let e1_regs = regs_of_writes e1.e_effect in
      let p = get_exn e1_regs ex wp1.exn in
      let s, r1, r2 =
        Subst.merge_states s (e1_regs, p.s)
          (e1_regs, wp1.post.s) in
      let r3 = t_equ (t_var ex_res) (t_var (Mexn.find ex xresult)) in
      let ne =
        wp_or (t_and_simp p.ne r1)
              (t_and_simp_l [wp1.post.ne; r2; r3]) in
      let ne = wp_label e ne in
      let xpost = { s = s; ne = ne } in
      let xne = Mexn.add ex xpost wp1.exn in
      { ok = wp1.ok;
        post = { ne = t_false; s = wp1.post.s }; (* Should s be Subst.empty??? *)
        exn = xne }
  | Etry (e1, handlers) ->
      (* OK: ok(e1) /\ (forall x. ex(e1)(x) => ok(handlers(x))) *)
      (* NE: ne(e1) \/ (bigor x. ex(e1)(x) /\ ne(handlers(x))) *)
      (* EX(x): *)
      let handlers =
        List.fold_left (fun acc (ex,pv,expr) -> Mexn.add ex (pv,expr) acc)
           Mexn.empty handlers in
      let result, xresult = r in
      let xresult' =
         Mexn.fold (fun ex (pv,_) acc ->
            Mexn.add ex pv.pv_vs acc) handlers xresult in
      let wp1 = fast_wp_expr env s (result,xresult') e1 in
      let e1_regs = regs_of_writes e1.e_effect in
      Mexn.fold (fun ex post acc ->
        try
          let _, e2 = Mexn.find ex handlers in
          let wp2 = fast_wp_expr env post.s r e2 in
          let e2_regs = regs_of_writes e2.e_effect in
          let s,f1,f2 =
            Subst.merge_states s (e1_regs, wp1.post.s)
                                 (Sreg.union e1_regs e2_regs, wp2.post.s) in
          let ne =
             wp_or
                (t_and_simp acc.post.ne f1)
                (t_and_simp_l [post.ne; wp2.post.ne; f2]) in
          { ok = t_and_simp acc.ok (t_implies_simp post.ne wp2.ok);
            post = { s  = s; ne = ne ; };
            exn =
              Mexn.fold Mexn.add wp2.exn acc.exn
          }
        with Not_found ->
          { acc with exn = Mexn.add ex post acc.exn }
         )
        wp1.exn
        { ok = wp1.ok;
          post = wp1.post;
          exn = Mexn.empty
        }
  | Eabstr (e1, spec) ->
        let wp1 = fast_wp_expr env s r e1 in
        let xpost = Mexn.map (fun p ->
          { s = wp1.post.s;
            ne  = p}) spec.c_xpost in
        let abstr_post = { ne = spec.c_post; s = wp1.post.s } in
        let post, xpost =
           adapt_post_to_state_pair env s r abstr_post xpost in
        let xq = Mexn.mapi (fun ex q -> Mexn.find ex xresult, q.ne) xpost in
        let ok =
           t_and_simp_l
              [wp1.ok; (Subst.term env s spec.c_pre);
               wp_nimplies wp1.post.ne wp1.exn ((result, post.ne), xq)] in
        let ok = wp_label e ok in
        { ok = ok ;
          post = post;
          exn  = xpost
        }
  | Eany spec ->
        let poststate = Subst.refresh (regs_of_writes spec.c_effect) s in
        let post = { ne = spec.c_post; s = poststate } in
        let xpost =
           Mexn.map (fun p -> { s = poststate; ne = p}) spec.c_xpost in
        let post, xpost =
           adapt_post_to_state_pair env s r post xpost in
        let pre = Subst.term env s spec.c_pre in
        { ok = wp_label e pre;
          post = post;
          exn = xpost;
        }
  | Eloop (inv, _, e1) ->
        let havoc_state = Subst.refresh (regs_of_writes e1.e_effect) s in
        let init_inv = t_label_add expl_loop_init (Subst.term env s inv) in
        let inv_hypo = Subst.term env havoc_state inv in
        let wp1 = fast_wp_expr env havoc_state r e1 in
        let post_inv =
           t_label_add expl_loop_keep (Subst.term env wp1.post.s inv) in
        let loop_body_ok = t_implies_simp inv_hypo wp1.ok in
        let preserv_inv =
           t_implies_simp (t_and_simp inv_hypo wp1.post.ne) post_inv in
        let exn =
           Mexn.map (fun post ->
              { post with ne = t_and_simp inv_hypo post.ne }) wp1.exn in
        let ok = t_and_simp_l [init_inv; preserv_inv; loop_body_ok] in
        (* TODO variant proof *)
        { ok = ok;
          post = { s = wp1.post.s; ne = t_false };
          exn = exn
        }
  | Eassign _ -> assert false
  | Efor (_, _, _, _) -> assert false (*TODO*)
  | Eghost _ -> assert false (*TODO*)
  | Ecase (_, _) -> assert false (*TODO*)
  | Erec (_, _) -> assert false (*TODO*)
      (* TODO exceptional case *)
  | Elet (_, _) -> assert false (*TODO*)

and fast_wp_fun_defn env { fun_ps = ps ; fun_lambda = l } =
  (* OK: forall bl. pl => ok(e)
     NE: true *)
  let lab = fresh_mark () and c = l.l_spec in
  let add_arg sbs pv = ity_match sbs pv.pv_vtv.vtv_ity pv.pv_vtv.vtv_ity in
  let subst = List.fold_left add_arg ps.ps_subst l.l_args in
  let regs = Mreg.map (fun _ -> ()) subst.ity_subst_reg in
  let args = List.map (fun pv -> pv.pv_vs) l.l_args in
  let env =
    if c.c_letrec = 0 || c.c_variant = [] then env else
    let lab = t_var lab in
    let t_at_lab (t,_) = t_app fs_at [t; lab] t.t_ty in
    let tl = List.map t_at_lab c.c_variant in
    let lrv = Mint.add c.c_letrec tl env.letrec_var in
    { env with letrec_var = lrv } in
  let prestate = Subst.init c.c_effect in
  let result, _  = open_post c.c_post in
  let xresult = Mexn.map (fun x -> fst (open_post x)) c.c_xpost in
  let res = fast_wp_expr env prestate (result, xresult) l.l_expr in
  let xq =
    Mexn.mapi (fun ex q -> {ne = q; s = (Mexn.find ex res.exn).s }) c.c_xpost in
  let fun_post = { s = res.post.s ; ne = c.c_post } in
  let q, xq =
    adapt_post_to_state_pair ~lab env prestate (result, xresult) fun_post xq in
  let pre = Subst.term env prestate c.c_pre in
  let xq = Mexn.mapi (fun ex q -> Mexn.find ex xresult, q.ne) xq in
  let f =
     t_and_simp res.ok
     (wp_nimplies res.post.ne res.exn ((result, q.ne), xq)) in
  let f = wp_implies pre f in
  wp_forall args (quantify env regs f)

and fast_wp_rec_defn env fdl = List.map (fast_wp_fun_defn env) fdl

let fast_wp_let env km th { let_sym = lv; let_expr = e } =
  let env = mk_env env km th in
  let res = fast_wp_expr env (Subst.init e.e_effect) (result e) e in
  let f = wp_forall (Mvs.keys res.ok.t_vars) res.ok in
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
    let f = wp_forall (Mvs.keys f.t_vars) f in
    add_wp_decl km d.fun_ps.ps_name f th
  in
  List.fold_left2 add_one th fdl fl

let fast_wp_val _env _km th _lv = th
