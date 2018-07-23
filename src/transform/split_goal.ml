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

open Ident
open Ty
open Term
open Decl

type split = {
  right_only : bool;
  byso_split : bool;
  side_split : bool;
  stop_split : bool;
  cpos_split : bool;
  cneg_split : bool;
  asym_split : bool;
  intro_mode : bool;
  comp_match : known_map option;
}

let stop f = Sattr.mem Term.stop_split f.t_attrs
let asym f = Sattr.mem Term.asym_split f.t_attrs

let case_split = Ident.create_attribute "case_split"
let case f = Sattr.mem case_split f.t_attrs

let compiled = Ident.create_attribute "split_goal: compiled match"

let unstop f =
  t_attr_set ?loc:f.t_loc (Sattr.remove stop_split f.t_attrs) f

(* Represent monoid of formula interpretation for conjonction and disjunction *)
module M = struct

  (* Multiplication tree *)
  type comb = Base of term | Op of comb * comb

  (* zero: false for /\, true for \/
     unit: true for /\, false for \/ *)
  type monoid = Zero of term | Unit | Comb of comb

  (* Triviality degree. *)
  let degree = function Unit -> 0 | Zero _ | Comb (Base _) -> 1 | _ -> 2

  (* inject formula into monoid. *)
  let (!+) a = Comb (Base a)

  (* monoid law. *)
  let (++) a b =
    match a, b with
    | _, Unit | Zero _, _ -> a
    | Unit, _ | _, Zero _ -> b
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
     Intended: mainly /\, \/ and ->
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
  (* implications are equivalences when byso_split is off *)
  (* Conjunctive decomposition of formula: /\ pos -> f *)
  pos : M.monoid;
  (* Disjunctive decomposition of formula: f -> \/ pos *)
  neg : M.monoid;
  (* Backward pull of formula: bwd -> f (typically from by) *)
  bwd : term;
  (* Forward pull of formula: f -> fwd (typically from so) *)
  fwd : term;
  (* Side-condition (generated from by/so occurrences when byso_split is on) *)
  side : M.monoid;
  (* Indicate whether positive/negative occurrences of formula
     force decomposition. *)
  cpos : bool;
  cneg : bool;
}

let rec drop_byso f = match f.t_node with
  | Tbinop (Timplies,{ t_node = Tbinop (Tor,_,{ t_node = Ttrue }) },f) ->
      drop_byso f
  | Tbinop (Tand,f,{ t_node = Tbinop (Tor,_,{ t_node = Ttrue }) }) ->
      drop_byso f
  | _ -> t_map drop_byso f


open M

let pat_condition kn tv cseen p =
  match p.pat_node with
  | Pwild ->
      let csl,sbs = match p.pat_ty.ty_node with
        | Tyapp (ts,_) ->
            Decl.find_constructors kn ts,
            let ty = ty_app ts (List.map ty_var ts.ts_args) in
            ty_match Mtv.empty ty p.pat_ty
        | _ -> assert false in
      let csall = Sls.of_list (List.rev_map fst csl) in
      let csnew = Sls.diff csall cseen in
      assert (not (Sls.is_empty csnew));
      let add_cs cs g =
        let mk_v ty = create_vsymbol (id_fresh "w") (ty_inst sbs ty) in
        let vl = List.map mk_v cs.ls_args in
        let f = t_equ tv (fs_app cs (List.map t_var vl) p.pat_ty) in
        g ++ !+ (t_exists_close_simp vl [] f) in
      let g = Sls.fold add_cs csnew Unit in
      csall, [], g
  | Papp (cs, pl) ->
      let vl = List.map (function
        | {pat_node = Pvar v} -> v | _ -> assert false) pl in
      let g = t_equ tv (fs_app cs (List.map t_var vl) p.pat_ty) in
      Sls.add cs cseen, vl, !+g
  | _ -> assert false

let rec fold_cond = function
  | Base a -> a
  | Op (a,b) -> t_or (fold_cond a) (fold_cond b)

let fold_cond = function
  | Comb c -> !+ (fold_cond c)
  | x -> x

let rec split_core sp f =
  let (~-) = t_attr_copy f in
  let ro = sp.right_only in
  let alias fo1 unop f1 =
    if fo1 == f1 then f else - unop f1 in
  let alias2 fo1 fo2 binop f1 f2 =
    if fo1 == f1 && fo2 == f2 then f else - binop f1 f2 in
  let rec trivial n = function
    | x :: q -> let m = n + degree x in (m <= 1 && trivial m q)
    | [] -> true in
  let trivial bs = trivial 0 bs in
  let pcaset bs sf =
    let test = not ro || (sf.cpos && trivial bs) in
    (if test then sf.pos else !+(sf.bwd)), test in
  let pcase bs sf = let x, _ = pcaset bs sf in x in
  let ncaset bs sf =
    let test = not ro || (sf.cneg && trivial bs) in
    (if test then sf.neg else !+(sf.fwd)), test in
  let ncase bs sf = let x, _ = ncaset bs sf in x in
  let ps_csp sp = { sp with cpos_split = false } in
  let ng_csp sp = { sp with cneg_split = false } in
  let no_csp sp = { sp with cpos_split = false;
                            cneg_split = false } in
  let in_csp sp = { sp with cpos_split = sp.cneg_split;
                            cneg_split = sp.cpos_split } in
  let ngt _ a = t_not a and cpy _ a = a in
  let bimap = bimap (fun _ t -> Zero t) cpy in
  let iclose = bimap ngt t_implies in
  let aclose = bimap cpy t_and in
  let nclose ps = map (fun t -> Zero (t_attr_copy t t_true)) t_not ps in
  let ret pos neg bwd fwd side cpos cneg =
      { pos; neg; bwd; fwd; side; cpos; cneg } in
  let r = match f.t_node with
  | _ when sp.stop_split && stop f ->
      let df = drop_byso f in
      ret !+(unstop f) !+(unstop df) f df Unit false false
  | Tbinop (Tiff,_,_) | Tif _ | Tcase _ | Tquant _ when sp.intro_mode ->
      let df = drop_byso f in
      ret !+f !+df f df Unit false false
  | Ttrue -> ret Unit (Zero f) f f Unit false false
  | Tfalse -> ret (Zero f) Unit f f Unit false false
  | Tapp _ -> let uf = !+f in ret uf uf f f Unit false false
    (* f1 so f2 *)
  | Tbinop (Tand,f1,{ t_node = Tbinop (Tor,f2,{ t_node = Ttrue }) }) ->
      if not (sp.byso_split && asym f2) then split_core sp f1 else
      let (&&&) f1 f2 = - t_and f1 f2 in
      let rc = split_core (no_csp sp) in
      let sf1 = rc f1 and sf2 = rc f2 in
      let fwd = sf1.fwd &&& sf2.fwd in
      let nf2, cn2 = ncaset [] sf2 in
      let nf1, cn1 = ncaset [nf2;sf2.side;sf2.pos] sf1 in
      let neg = bimap cpy (&&&) nf1 nf2 in
      let close = iclose nf1 in
      let lside = if sp.side_split then close sf2.pos else
        !+(t_implies sf1.fwd sf2.bwd) in
      let side = sf1.side ++ lside ++ close sf2.side in
      ret sf1.pos neg sf1.bwd fwd side sf1.cpos (cn1 || cn2)
  | Tbinop (Tand,f1,f2) ->
      let (&&&) = alias2 f1 f2 t_and in
      let rc = split_core (ps_csp sp) in
      let sf1 = rc f1 and sf2 = rc f2 in
      let fwd = sf1.fwd &&& sf2.fwd and bwd = sf1.bwd &&& sf2.bwd in
      let asym = sp.asym_split && asym f1 in
      let nf2, cn2 = ncaset [] sf2 in
      let sd = if asym then [sf2.side] else [] in
      let dp = nf2::sd in
      let nf1, cn1 = ncaset dp sf1 in
      let neg = bimap cpy (&&&) nf1 nf2 in
      let pos2 = if not asym then sf2.pos else
        let nf1 = ncase (sf2.pos::sd) sf1 in iclose nf1 sf2.pos in
      let pos = sf1.pos ++ pos2 in
      let side = sf1.side ++ if not asym then sf2.side else
        let nf1 = ncase (sf2.pos::dp) sf1 in iclose nf1 sf2.side in
      ret pos neg bwd fwd side false (cn1 || cn2)
    (* f1 by f2 *)
  | Tbinop (Timplies,{ t_node = Tbinop (Tor,f2,{ t_node = Ttrue }) },f1) ->
      if not (sp.byso_split && asym f2) then split_core sp f1 else
      let rc = split_core (no_csp sp) in
      let sf1 = rc f1 and sf2 = rc f2 in
      let close = iclose (ncase [sf1.pos;sf1.side] sf2) in
      let lside = if sp.side_split then close sf1.pos else
        !+(t_implies sf2.fwd sf1.bwd) in
      let side = sf2.side ++ lside ++ sf1.side in
      ret sf2.pos sf1.neg sf2.bwd sf1.fwd side sf2.cpos sf1.cneg
  | Tbinop (Timplies,f1,f2) ->
      let (>->) = alias2 f1 f2 t_implies in
      let sp2 = ng_csp sp in let sp1 = in_csp sp2 in
      let sf1 = split_core sp1 f1 and sf2 = split_core sp2 f2 in
      let fwd = sf1.bwd >-> sf2.fwd and bwd = sf1.fwd >-> sf2.bwd in
      let asym = sp.asym_split && asym f1 in
      let sd = [sf2.side] in
      let neg1 = nclose sf1.pos in
      let neg2 = if not asym then sf2.neg else
        let nf1 = ncase (sf2.neg::sd) sf1 in
        aclose nf1 sf2.neg in
      let neg = neg1 ++ neg2 in
      let dp = sf2.pos::sd in
      let nf1, cn1 = ncaset dp sf1 in
      let pos = bimap (fun _ a -> - t_not a) (>->) nf1 sf2.pos in
      let nf1 = ncase (if asym then sf2.neg::dp else dp) sf1 in
      let side = sf1.side ++ iclose nf1 sf2.side in
      ret pos neg bwd fwd side (cn1 || sf2.cpos) false
  | Tbinop (Tor,f1,f2) ->
      let (|||) = alias2 f1 f2 t_or in
      let rc = split_core (ng_csp sp) in
      let sf1 = rc f1 and sf2 = rc f2 in
      let fwd = sf1.fwd ||| sf2.fwd and bwd = sf1.bwd ||| sf2.bwd in
      let asym = sp.asym_split && asym f1 in
      let sd = if asym then [sf2.side] else [] in
      let pf2, cp2 = pcaset [] sf2 in
      let dp = sf2.pos::sd in
      let pf1, cp1 = pcaset dp sf1 in
      let pos = bimap cpy (|||) pf1 pf2 in
      let neg2 = if not asym then sf2.neg else
        let pf1 = pcase (sf2.neg::sd) sf1 in aclose (nclose pf1) sf2.neg in
      let side2 = if not asym then sf2.side else
        let pf1 = pcase (sf2.neg::dp) sf1 in
        bimap cpy (|||) pf1 sf2.side in
      ret pos (sf1.neg ++ neg2) bwd fwd (sf1.side ++ side2) (cp1 || cp2) false
  | Tbinop (Tiff,f1,f2) ->
      let rc = split_core (no_csp sp) in
      let sf1 = rc f1 and sf2 = rc f2 in
      let df = if sf1.fwd == sf1.bwd && sf2.fwd == sf2.bwd
        then alias2 f1 f2 t_iff sf1.fwd sf2.fwd else drop_byso f in
      let nf1 = ncase [sf2.pos] sf1 and nf2 = ncase [sf1.pos] sf2 in
      let pos = iclose nf1 sf2.pos ++ iclose nf2 sf1.pos in
      let nf2 = ncase [] sf2 and pf2 = pcase [] sf2 in
      let nf1 = ncase [nf2] sf1 and pf1 = pcase [pf2] sf1 in
      let neg_top = aclose nf1 nf2 in
      let neg_bot = aclose (nclose pf1) (nclose pf2) in
      ret pos (neg_top ++ neg_bot) df df (sf1.side ++ sf2.side) false false
  | Tif (fif,fthen,felse) ->
      let rc = split_core (no_csp sp) in
      let sfi = rc fif and sft = rc fthen and sfe = rc felse in
      let dfi = if sfi.fwd == sfi.bwd then sfi.fwd else drop_byso fif in
      let rebuild fif2 fthen2 felse2 =
        if fif == fif2 && fthen == fthen2 && felse == felse2 then f else
        - t_if fif2 fthen2 felse2
      in
      let fwd = rebuild dfi sft.fwd sfe.fwd in
      let bwd = rebuild dfi sft.bwd sfe.bwd in
      let sdt = [sft.side] and sde = [sfe.side] in
      let spt = sft.pos::sdt and spe = sfe.pos::sde in
      let nfi = ncase spt sfi and pfi = pcase spe sfi in
      let pos = iclose nfi sft.pos ++ iclose (nclose pfi) sfe.pos in
      let nfi = ncase (sft.neg::sdt) sfi and pfi = pcase (sfe.neg::sde) sfi in
      let neg = aclose nfi sft.neg ++ aclose (nclose pfi) sfe.neg in
      let nfi = ncase (sft.neg::spt) sfi and pfi = pcase (sfe.neg::spe) sfi in
      let eside = iclose (nclose pfi) sfe.side in
      let side = sfi.side ++ iclose nfi sft.side ++ eside in
      ret pos neg bwd fwd side false false
  | Tnot f1 ->
      let sf = split_core (in_csp sp) f1 in
      let (!) = alias f1 t_not in
      let (|>) zero = map (fun t -> !+(t_attr_copy t zero)) (!) in
      let pos = t_false |> sf.neg and neg = t_true |> sf.pos in
      ret pos neg !(sf.fwd) !(sf.bwd) sf.side sf.cneg sf.cpos
  | Tlet (t,fb) ->
      let vs, f1 = t_open_bound fb in
      let (!) = alias f1 (t_let_close vs t) in
      let sf = split_core sp f1 in
      let (!!) = map (fun t -> Zero t) (!) in
      ret !!(sf.pos) !!(sf.neg) !(sf.bwd) !(sf.fwd) !!(sf.side) sf.cpos sf.cneg
  | Tcase (t,bl) ->
      let rc = match bl with
        | [_] -> split_core sp
        | _   -> split_core (no_csp sp) in
      let k join =
        let case_close bl2 =
          if Lists.equal (==) bl bl2 then f else - t_case t bl2 in
        let sbl = List.map (fun b ->
          let p, f, close = t_open_branch_cb b in
          p, close, rc f) bl in
        let blfwd = List.map (fun (p, close, sf) -> close p sf.fwd) sbl in
        let fwd = case_close blfwd in
        let blbwd = List.map (fun (p, close, sf) -> close p sf.bwd) sbl in
        let bwd = case_close blbwd in
        let pos, neg, side = join sbl in
        ret pos neg bwd fwd side false false
      in
      begin match sp.comp_match with
      | None ->
          let join sbl =
            let rec zip_all bf_top bf_bot = function
              | [] -> Unit, Unit, Unit, [], []
              | (p, close, sf) :: q ->
                let c_top = close p t_true and c_bot = close p t_false in
                let dp_top = c_top :: bf_top and dp_bot = c_bot :: bf_bot in
                let pos, neg, side, af_top, af_bot = zip_all dp_top dp_bot q in
                let fzip bf af mid =
                  - t_case t (List.rev_append bf (close p mid::af)) in
                let zip bf mid af =
                  map (fun t -> !+(fzip bf af t)) (fzip bf af) mid in
                zip bf_top sf.pos af_top ++ pos,
                zip bf_bot sf.neg af_bot ++ neg,
                zip bf_top sf.side af_top ++ side,
                c_top :: af_top,
                c_bot :: af_bot
            in
            let pos, neg, side, _, _ = zip_all [] [] sbl in
            pos, neg, side
          in
          k join
      | Some kn ->
          if Sattr.mem compiled f.t_attrs
          then
            (* keep the attributes for single-case match *)
            let attrs = match bl with
              | [_] -> Sattr.remove case_split
                    (Sattr.remove compiled f.t_attrs)
              | _ -> Sattr.empty in
            let join sbl =
              let vs = create_vsymbol (id_fresh "q") (t_type t) in
              let tv = t_var vs in
              let (~-) fb =
                t_attr_set ?loc:f.t_loc attrs (t_let_close_simp vs t fb) in
              let _, pos, neg, side =
                List.fold_left (fun (cseen, pos, neg, side) (p, _, sf) ->
                  let cseen, vl, cond = pat_condition kn tv cseen p in
                  let cond = if ro then fold_cond cond else cond in
                  let fcl t = - t_forall_close_simp vl [] t in
                  let ecl t = - t_exists_close_simp vl [] t in
                  let ps cond f = fcl (t_implies cond f) in
                  let ng cond f = ecl (t_and cond f) in
                  let ngt _ a = fcl (t_not a) and tag _ a = ecl a in
                  let pos  = pos  ++ bimap ngt ps cond sf.pos  in
                  let neg  = neg  ++ bimap tag ng cond sf.neg  in
                  let side = side ++ bimap ngt ps cond sf.side in
                  cseen, pos, neg, side
                ) (Sls.empty, Unit, Unit, Unit) sbl
              in
              pos, neg, side
            in
            k join
          else
            let mk_let = t_let_close_simp in
            let mk_case t bl = t_attr_add compiled (t_case_close t bl) in
            let mk_b b = let p, f = t_open_branch b in [p], f in
            let bl = List.map mk_b bl in
            rc (- Pattern.compile_bare ~mk_case ~mk_let [t] bl)
      end
  | Tquant (qn,fq) ->
      let vsl, trl, f1 = t_open_quant fq in
      let close = alias f1 (t_quant_close qn vsl trl) in
      let sf = split_core sp f1 in
      let bwd = close sf.bwd and fwd = close sf.fwd in
      let pos, neg, cpos, cneg = match qn with
        | Tforall ->
            map (fun t -> Zero t) close sf.pos, !+fwd,
            sf.cpos, false
        | Texists ->
            !+bwd, map (fun t -> Zero t) close sf.neg,
            false, sf.cneg
      in
      let side = map (fun t -> Zero t) (t_forall_close vsl trl) sf.side in
      ret pos neg bwd fwd side cpos cneg
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)
  in
  let r = if case f then
    { r with cpos = sp.cpos_split; cneg = sp.cneg_split } else r in
  match r with
  | { side = M.Zero _ } ->
      { r with pos = Unit; neg = Unit; fwd = t_false; bwd = t_true }
  | _ -> r


let full_split kn = {
  right_only = false;
  byso_split = false;
  side_split = true;
  stop_split = false;
  cpos_split = true;
  cneg_split = true;
  asym_split = true;
  intro_mode = false;
  comp_match = kn;
}

let right_split kn = { (full_split kn) with right_only = true }
let full_proof  kn = { (full_split kn) with stop_split = true;
                                            byso_split = true }
let right_proof kn = { (full_proof kn) with right_only = true }
let full_intro  kn = { (full_split kn) with asym_split = false;
                                            intro_mode = true;
                                            stop_split = true }
let right_intro kn = { (full_intro kn) with right_only = true }

let split_pos sp f =
  let core = split_core sp f in
  assert (core.side = Unit);
  to_list core.pos

let split_neg sp f =
  let core = split_core sp f in
  assert (core.side = Unit);
  to_list core.neg

let split_proof sp f =
  let core = split_core sp f in
  to_list (core.pos ++ core.side)

let split_pos_full  ?known_map f = split_pos (full_split known_map)  f
let split_pos_right ?known_map f = split_pos (right_split known_map) f

let split_neg_full  ?known_map f = split_neg (full_split known_map)  f
let split_neg_right ?known_map f = split_neg (right_split known_map) f

let split_proof_full  ?known_map f = split_proof (full_proof known_map)  f
let split_proof_right ?known_map f = split_proof (right_proof known_map) f

let split_intro_full  ?known_map f = split_pos (full_intro known_map)  f
let split_intro_right ?known_map f = split_pos (right_intro known_map) f

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

let split_goal_full  = prep_goal full_proof
let split_goal_right = prep_goal right_proof

let split_all_full  = prep_all full_proof
let split_all_right = prep_all right_proof

let split_premise_full  = prep_premise full_proof
let split_premise_right = prep_premise right_proof

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
