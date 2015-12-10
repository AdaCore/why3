(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2015   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ident
open Ty
open Term
open Decl

type split = {
  right_only : bool;
  byso_split : bool;
  side_split : bool;
  stop_split : bool;
  asym_split : bool;
  comp_match : known_map option;
}

(* Represent monoid of formula interpretation for conjonction and disjunction *)
module M = struct

  (* Multiplication tree *)
  type comb = Base of term | Op of comb * comb

  (* zero: false for /\, true for \/
     unit: true for /\, false for \/ *)
  type monoid = Zero of term | Unit | Comb of comb

  (* inject formula into monoid. *)
  let (!+) a = Comb (Base a)

  (* monoid law. *)
  let (++) a b = match a, b with
    | Zero _, _ | _, Unit -> a
    | _, Zero _ | Unit, _ -> b
    | Comb ca, Comb cb -> Comb (Op (ca, cb))

  (* (base -> base) morphism application. *)
  let rec cmap f = function
    | Base a -> Base (f a)
    | Op (a,b) -> Op (cmap f a, cmap f b)

  (* (base -> general) morphism application *)
  let rec cbind f = function
    | Base a -> f a
    | Op (a,b) -> Op (cbind f a, cbind f b)

  (* Apply morphism phi from monoid 1 to monoid 2
     (law may change)
     Implicit morphism phi must respect:
     phi(zero_1) = f0 (term representing the zero)
     phi(unit_1) = unit_2
     phi(x `law_1` y) = phi(x) `law_2` phi(y)
     phi(a) = f a (for base values, and f a is a base value)
     Intended: monotone context closure, negation *)
  let map f0 f = function
    | Zero t -> f0 t
    | Unit -> Unit
    | Comb c -> Comb (cmap f c)

  (* Apply bimorphism phi from monoids 1 and 2 to monoid 3
     Implicit bimorphism phi must respect:
     - partial applications of phi (phi(a,_) and phi(_,b)) are morphisms
     - phi(zero,b) = f0_ 'term for zero' b (for b a base value,
                                            f0_ _ b is a base value)
     - phi(a,zero) = f_0 'term for zero' a (for a a base value,
                                            f_0 a _ is a base value)
     - phi(zero,zero) = f00 'term for first zero' 'term for second zero'
     - phi(a,b) = f a b (for a,b base value, and f a b is a base value)
     Intended: /\, \/ and ->
   *)
  let bimap f00 f0_ f_0 f a b = match a, b with
    | Unit, _ | _, Unit -> Unit
    | Zero t1, Zero t2 -> f00 t1 t2
    | Zero t1, Comb cb ->  Comb (cmap (f0_ t1) cb)
    | Comb ca, Zero t2 -> Comb (cmap (f_0 t2) ca)
    | Comb ca, Comb cb -> Comb (cbind (fun x -> cmap (f x) cb) ca)

  let rec to_list m acc = match m with
    | Base a -> a :: acc
    | Op (a,b) -> to_list a (to_list b acc)

  let to_list = function
    | Zero t -> [t]
    | Unit -> []
    | Comb c -> to_list c []

end

type split_ret = {
  pos : M.monoid;
  neg : M.monoid;
  bwd : term;
  fwd : term;
  side : M.monoid;
}


let stop_split = Ident.create_label "stop_split"

let stop f = Slab.mem stop_split f.t_label
let asym f = Slab.mem Term.asym_label f.t_label
let keep f = Slab.mem Term.keep_on_simp_label f.t_label

let unstop f =
  t_label ?loc:f.t_loc (Slab.remove stop_split f.t_label) f

let rec drop_byso f = match f.t_node with
  | Tbinop (Timplies,{ t_node = Tbinop (Tor,_,{ t_node = Ttrue }) },f) ->
      drop_byso f
  | Tbinop (Tand,f,{ t_node = Tbinop (Tor,_,{ t_node = Ttrue }) }) ->
      drop_byso f
  | _ -> t_map drop_byso f

let rec split_core sp f =
  let rc = split_core sp in
  let (~-) = t_label_copy f in
  let ro = sp.right_only in
  let alias fo1 unop f1 = if fo1 == f1 then f else - unop f1 in
  let alias2 fo1 fo2 binop f1 f2 =
    if fo1 == f1 && fo2 == f2 then f else - binop f1 f2 in
  let open M in
  let bimap = bimap (fun t _ -> Zero t) in
  let neg _ a = t_not a and cpy _ a = a in
  let iclose fw ng ps =
    if ro
    then map (fun _ -> !+ (t_not fw)) (t_implies fw) ps
    else bimap cpy neg t_implies ng ps
  in
  let fclose vsl trl ps = map (fun t -> Zero t) (t_forall_close vsl trl) ps in
  let ret pos neg bwd fwd side = { pos; neg; bwd; fwd; side } in
  let r = match f.t_node with
  | _ when sp.stop_split && stop f ->
      let f = unstop f in
      let df = drop_byso f in
      ret !+f !+df f df Unit
  | Ttrue -> ret (if keep f then !+f else Unit) (Zero f) f f Unit
  | Tfalse -> ret (Zero f) (if keep f then !+f else Unit) f f Unit
  | Tapp _ -> ret !+f !+f f f Unit
    (* f1 so f2 *)
  | Tbinop (Tand,f1,{ t_node = Tbinop (Tor,f2,{ t_node = Ttrue }) }) ->
      if not (sp.byso_split && asym f2) then rc f1 else
      let (&&&) f1 f2 = - t_and f1 f2 in
      let sf1 = rc f1 and sf2 = rc f2 in
      let fwd = sf1.fwd &&& sf2.fwd in
      let neg = if ro then !+fwd else bimap cpy cpy (&&&) sf1.neg sf2.neg in
      let close = iclose sf1.fwd sf1.neg in
      let lside =
        if sp.side_split
        then close sf2.pos
        else !+(t_implies sf1.fwd sf2.bwd)
      in
      ret sf1.pos neg sf1.bwd fwd (sf1.side ++ lside ++ close sf2.side)
  | Tbinop (Tand,f1,f2) ->
      let (&&&) = alias2 f1 f2 t_and in
      let sf1 = rc f1 and sf2 = rc f2 in
      let fwd = sf1.fwd &&& sf2.fwd and bwd = sf1.bwd &&& sf2.bwd in
      let neg = if ro then !+fwd else bimap cpy cpy (&&&) sf1.neg sf2.neg in
      (* If asymetric, must close f2 & f2 side-condition by f1 in context. *)
      let close =
        if sp.asym_split && asym f1
        then iclose sf1.fwd sf1.neg
        else fun x -> x
      in
      ret (sf1.pos ++ close sf2.pos) neg bwd fwd (sf1.side ++ close sf2.side)
  (* f1 by f2 *)
  | Tbinop (Timplies,{ t_node = Tbinop (Tor,f2,{ t_node = Ttrue }) },f1) ->
      if not (sp.byso_split && asym f2) then rc f1 else
      let sf1 = rc f1 and sf2 = rc f2 in
      let close = iclose sf2.fwd sf2.neg in
      let lside =
        if sp.side_split
        then close sf1.pos
        else !+(t_implies sf2.fwd sf1.bwd)
      in
      ret sf2.pos sf1.neg sf2.bwd sf1.fwd (sf2.side ++ lside ++ close sf1.side)
  | Tbinop (Timplies,f1,f2) ->
      let (>->) = alias2 f1 f2 t_implies in
      let sf1 = rc f1 and sf2 = rc f2 in
      let fwd = sf1.bwd >-> sf2.fwd and bwd = sf1.fwd >-> sf2.bwd in
      let close =
        if ro
        then map (fun _ -> !+ (- t_not sf1.fwd)) ((>->) sf1.fwd)
        else bimap cpy (fun _ a -> - t_not a) (>->) sf1.neg
      in
      let neg1 = map (fun t -> !+(t_label_copy t t_true)) t_not sf1.pos in
      let neg2 = if not (sp.asym_split && asym f1) then sf2.neg else
        if ro
        then map (fun _ -> !+(sf1.fwd)) (t_and sf1.fwd) sf2.neg
        else bimap cpy cpy t_and sf1.neg sf2.neg
      in
      let neg = neg1 ++ neg2 in
      ret (close sf2.pos) neg bwd fwd (sf1.side ++ close sf2.side)
  | Tbinop (Tor,f1,f2) ->
      let (|||) = alias2 f1 f2 t_or in
      let sf1 = rc f1 and sf2 = rc f2 in
      let fwd = sf1.fwd ||| sf2.fwd and bwd = sf1.bwd ||| sf2.bwd in
      let pos = if ro then !+bwd else bimap cpy cpy (|||) sf1.pos sf2.pos in
      let side2, neg2 =
        if sp.asym_split && asym f1
        then if ro
          then
            let n1 = t_not sf1.bwd in
            map (fun _ -> !+(sf1.bwd)) ((|||) sf1.bwd) sf2.side,
            map (fun _ -> !+n1) (t_and n1) sf2.neg
          else
            let n1 =
              map (fun t -> Zero (t_label_copy t t_true)) t_not sf1.pos in
            bimap cpy cpy (|||) sf1.pos sf2.side,
            bimap neg cpy t_and n1 sf2.neg
        else sf2.side, sf2.neg
      in
      ret pos (sf1.neg ++ neg2) bwd fwd (sf1.side ++ side2)
  | Tbinop (Tiff,f1,f2) ->
      let sf1 = rc f1 and sf2 = rc f2 in
      let df = if sf1.fwd == sf1.bwd && sf2.fwd == sf2.bwd
        then alias2 f1 f2 t_iff sf1.fwd sf2.fwd else drop_byso f in
      let pos = iclose sf1.fwd sf1.neg sf2.pos
                ++ iclose sf2.fwd sf2.neg sf1.pos in
      let conj f f1 n1 f2 n2 =
        let (&&&) f1 f2 = t_and (f f1) (f f2) in
        if ro then !+(f1 &&& f2) else let f_ _ = f in bimap f_ f_ (&&&) n1 n2 
      in
      let neg_top = conj (fun x -> x) sf1.fwd sf1.neg sf2.fwd sf2.neg in
      let neg_bot = conj t_not sf1.bwd sf1.pos sf2.bwd sf2.pos in
      ret pos (neg_top ++ neg_bot) df df (sf1.side ++ sf2.side)
  | Tif (fif,fthen,felse) ->
      let sfi = rc fif and sft = rc fthen and sfe = rc felse in
      let dfi = if sfi.fwd == sfi.bwd then sfi.fwd else drop_byso fif in
      let rebuild fif2 fthen2 felse2 =
        if fif == fif2 && fthen == fthen2 && felse == felse2 then f else
        t_if fif2 fthen2 felse2
      in
      let fwd = rebuild dfi sft.fwd sfe.fwd in
      let bwd = rebuild dfi sft.bwd sfe.bwd in
      let pos, neg, side_branch =
        if ro
        then
          let negated = t_not sfi.bwd in
          let pthen_close =
            map (fun _ -> !+(t_not sfi.fwd)) (t_implies sfi.fwd) in
          let pelse_close = map (fun _ -> !+(sfi.bwd)) (t_implies negated) in
          let pos = pthen_close sft.pos ++ pelse_close sfe.pos in
          let side = pthen_close sft.side ++ pelse_close sfe.side in
          let neg_then = map (fun _ -> !+(sfi.fwd)) (t_and sfi.fwd) sft.neg in
          let neg_else = map (fun _ -> !+(negated)) (t_and negated) sfe.neg in
          pos, neg_then ++ neg_else, side
        else
          let negated =
            map (fun t -> Zero (t_label_copy t t_true)) t_not sfi.pos in
          let pos_close = bimap cpy neg t_implies in
          let pos = pos_close sfi.neg sft.pos ++ pos_close negated sfe.pos in
          let side = pos_close sfi.neg sft.side ++ pos_close negated sfe.side in
          let neg_close = bimap cpy cpy t_and in
          let neg = neg_close sfi.neg sft.neg ++ neg_close negated sfe.neg in
          pos, neg, side
      in
      ret pos neg bwd fwd (sfi.side ++ side_branch)
  | Tnot f1 ->
      let sf = rc f1 in
      let (!) f = - t_not f in
      let (|>) zero = map (fun t -> !+(t_label_copy t zero)) (!) in
      ret (t_false |> sf.neg) (t_true |> sf.pos) !(sf.fwd) !(sf.bwd) sf.side
  | Tlet (t, fb) ->
      let vs, f1, close = t_open_bound_cb fb in
      let (!) f = alias fb (t_let t) (close vs f) in
      let sf = rc f1 in
      let (!!) = map (fun t -> Zero t) (!) in
      ret !!(sf.pos) !!(sf.neg) !(sf.bwd) !(sf.fwd) !!(sf.side)
  | Tcase _ -> assert false (* TODO: handle pattern-matching. *)
  | Tquant (qn,fq) ->
      let vsl, trl, f1, close = t_open_quant_cb fq in
      let close f = alias fq (t_quant qn) (close vsl trl f) in
      let sf = rc f1 in
      let bwd = close sf.bwd and fwd = close sf.fwd in
      let pos, neg = match qn with
        | Tforall -> map (fun t -> Zero t) close sf.pos, !+fwd
        | Texists -> !+bwd, map (fun t -> Zero t) close sf.neg
      in
      ret pos neg bwd fwd (fclose vsl trl sf.side)
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)
  in
  match r with
  | { side = M.Zero _ as side } ->
      { pos = Unit; neg = Unit; fwd = t_false; bwd = t_true; side }
  | _ -> r


let full_split kn = {
  right_only = false;
  byso_split = false;
  side_split = false;
  stop_split = false;
  asym_split = true;
  comp_match = kn;
}

let right_split kn = { (full_split kn) with right_only = true }
let wp_split kn    = { (right_split kn) with stop_split = true }
let intro_split kn = { (wp_split kn) with asym_split = false }
let proof_split kn = { (wp_split kn) with byso_split = true }
let total_split kn = { (proof_split kn) with right_only = false }

let split_pos sp f = M.to_list (split_core sp f).pos
let split_neg sp f = M.to_list (split_core sp f).neg
let split_proof sp f =
  let core = split_core sp f in M.to_list (M.(++) core.pos core.side)

let split_pos_full ?known_map f = split_pos (full_split known_map) f
let split_neg_full ?known_map f = split_neg (full_split known_map) f

let split_pos_right ?known_map f = split_pos (right_split known_map) f
let split_neg_right ?known_map f = split_neg (right_split known_map) f

let split_pos_wp ?known_map f = split_pos (wp_split known_map) f
let split_neg_wp ?known_map f = split_neg (wp_split known_map) f

let split_pos_intro ?known_map f = split_pos (intro_split known_map) f
let split_neg_intro ?known_map f = split_neg (intro_split known_map) f

let split_goal sp pr f =
  let make_prop f = [create_prop_decl Pgoal pr f] in
  List.map make_prop (split_proof sp f)

let split_axiom sp pr f =
  let make_prop f =
    let pr = create_prsymbol (id_clone pr.pr_name) in
    create_prop_decl Paxiom pr f in
  let sp = { sp with asym_split = false; byso_split = false } in
  match split_pos sp f with
    | [f] -> [create_prop_decl Paxiom pr f]
    | fl  -> List.map make_prop fl

let split_all sp d = match d.d_node with
  | Dprop (Pgoal, pr,f) ->  split_goal  sp pr f
  | Dprop (Paxiom,pr,f) -> [split_axiom sp pr f]
  | _ -> [[d]]

let split_premise sp d = match d.d_node with
  | Dprop (Paxiom,pr,f) ->  split_axiom sp pr f
  | _ -> [d]

let prep_goal split = Trans.store (fun t ->
  let split = split (Some (Task.task_known t)) in
  let trans = Trans.goal_l (split_goal split) in
  Trans.apply trans t)

let prep_all split = Trans.store (fun t ->
  let split = split (Some (Task.task_known t)) in
  let trans = Trans.decl_l (split_all split) None in
  Trans.apply trans t)

let prep_premise split = Trans.store (fun t ->
  let split = split (Some (Task.task_known t)) in
  let trans = Trans.decl (split_premise split) None in
  Trans.apply trans t)

let split_goal_full  = prep_goal full_split
let split_goal_right = prep_goal right_split
let split_goal_wp    = prep_goal wp_split
let split_proof      = prep_goal proof_split
let split_proof_full = prep_goal total_split

let split_all_full  = prep_all full_split
let split_all_right = prep_all right_split
let split_all_wp    = prep_all wp_split

let split_premise_full  = prep_premise full_split
let split_premise_right = prep_premise right_split
let split_premise_wp    = prep_premise wp_split

let () = Trans.register_transform_l "split_goal_full" split_goal_full
  ~desc:"Put@ the@ goal@ in@ a@ conjunctive@ form,@ \
  returns@ the@ corresponding@ set@ of@ subgoals.@ The@ number@ of@ subgoals@ \
  generated@ may@ be@ exponential@ in@ the@ size@ of@ the@ initial@ goal."
let () = Trans.register_transform_l "split_all_full" split_all_full
  ~desc:"Same@ as@ split_goal_full,@ but@ also@ split@ premises."
let () = Trans.register_transform "split_premise_full" split_premise_full
  ~desc:"Same@ as@ split_all_full,@ but@ split@ only@ premises."

let () = Trans.register_transform_l "split_goal_right" split_goal_right
  ~desc:"@[<hov 2>Same@ as@ split_goal_full,@ but@ don't@ split:@,\
      - @[conjunctions under disjunctions@]@\n\
      - @[conjunctions on the left of implications.@]@]"
let () = Trans.register_transform_l "split_all_right" split_all_right
  ~desc:"Same@ as@ split_goal_right,@ but@ also@ split@ premises."
let () = Trans.register_transform "split_premise_right" split_premise_right
  ~desc:"Same@ as@ split_all_right,@ but@ split@ only@ premises."

let () = Trans.register_transform_l "split_goal_wp" split_goal_wp
  ~desc:"Same@ as@ split_goal_right,@ but@ stops@ at@ \
    the@ `stop_split'@ label@ and@ removes@ the@ label."
let () = Trans.register_transform_l "split_all_wp" split_all_wp
  ~desc:"Same@ as@ split_goal_wp,@ but@ also@ split@ premises."
let () = Trans.register_transform "split_premise_wp" split_premise_wp
  ~desc:"Same@ as@ split_all_wp,@ but@ split@ only@ premises."

let () = Trans.register_transform_l "split_goal_wp_old"
  (Trans.goal_l (split_goal (wp_split None)))
  ~desc:"transitional, to be removed as soon as all sessions migrate"

let () = Trans.register_transform_l "split_proof" split_proof
  ~desc:"experimental"
let () = Trans.register_transform_l "split_proof_full" split_proof_full
  ~desc:"experimental"

let ls_of_var v =
  create_fsymbol (id_fresh ("spl_" ^ v.vs_name.id_string)) [] v.vs_ty

let split_intro known_map pr f =
  let rec split_intro dl acc f =
    let rsp = split_intro dl in
    match f.t_node with
    | Ttrue when not (keep f) -> acc
    | Tbinop (Tand,f1,f2) when asym f1 ->
        rsp (rsp acc (t_implies f1 f2)) f1
    | Tbinop (Tand,f1,f2) ->
        rsp (rsp acc f2) f1
    | Tbinop (Timplies,f1,f2) ->
        let pp = create_prsymbol (id_fresh (pr.pr_name.id_string ^ "_spl")) in
        let dl = create_prop_decl Paxiom pp f1 :: dl in
        split_intro dl acc f2
    | Tbinop (Tiff,f1,f2) ->
        rsp (rsp acc (t_implies f2 f1)) (t_implies f1 f2)
    | Tif (fif,fthen,felse) ->
        rsp (rsp acc (t_implies (t_not fif) felse)) (t_implies fif fthen)
    | Tlet (t,fb) -> let vs,f = t_open_bound fb in
        let ls = ls_of_var vs in
        let f  = t_subst_single vs (fs_app ls [] vs.vs_ty) f in
        let dl = create_logic_decl [make_ls_defn ls [] t] :: dl in
        split_intro dl acc f
    | Tquant (Tforall,fq) -> let vsl,_,f = t_open_quant fq in
        let lls = List.map ls_of_var vsl in
        let add s vs ls = Mvs.add vs (fs_app ls [] vs.vs_ty) s in
        let f = t_subst (List.fold_left2 add Mvs.empty vsl lls) f in
        let add dl ls = create_param_decl ls :: dl in
        let dl = List.fold_left add dl lls in
        split_intro dl acc f
    | _ ->
        let goal f = List.rev (create_prop_decl Pgoal pr f :: dl) in
        List.rev_append (List.rev_map goal (split_pos_wp ~known_map f)) acc
  in
  split_intro [] [] f

let split_intro = Trans.store (fun t ->
  Trans.apply (Trans.goal_l (split_intro (Task.task_known t))) t)

let () = Trans.register_transform_l "split_intro" split_intro
  ~desc:"Same@ as@ split_goal_wp,@ but@ moves@ \
    the@ implication@ antecedents@ to@ premises."
