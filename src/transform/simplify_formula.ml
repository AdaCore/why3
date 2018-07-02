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
open Term
open Decl

let attrset = Sattr.of_list [Term.asym_split]

let rec fmla_simpl f =
  let f = if Sattr.disjoint f.t_attrs attrset then f else
    t_attr_set ?loc:f.t_loc (Sattr.diff f.t_attrs attrset) f in
  TermTF.t_map_simp t_fmla_simpl fmla_simpl f

and t_fmla_simpl t = TermTF.t_map t_fmla_simpl fmla_simpl t

let decl_l d =
  match d.d_node with
    | Dprop (k,pr,f) ->
        let f = fmla_simpl f in
        begin match f.t_node, k with
          | Ttrue, Paxiom -> [[]]
          | Tfalse, Paxiom -> []
          | Ttrue, Pgoal -> []
          | _ -> [[create_prop_decl k pr f]]
        end
    | _ -> [[DeclTF.decl_map t_fmla_simpl fmla_simpl d]]

let simplify_formula = Trans.rewriteTF t_fmla_simpl fmla_simpl None

let simplify_formula_and_task = Trans.decl_l decl_l None

let () = Trans.register_transform
  "simplify_formula" simplify_formula
  ~desc:"Simplify@ the@ formulas@ using@ propositional@ simplifications."

let () = Trans.register_transform_l
  "simplify_formula_and_task" simplify_formula_and_task
  ~desc:"Same as simplify_formula, but also@ \
         remove@ axioms@ and@ goals@ that@ become@ trivial."

(** remove_trivial_quantification
    Original version in the alt-ergo prover by Sylvain Conchon *)

(** transform \exists x. x == y /\ F into F[y/x] *)
(** transform \forall x. x <> y \/ F into F[y/x] *)

(** test if the freevariable of a term
    are included in a given set *)
let t_boundvars_in fvars t =
  try
    t_v_fold (fun () u -> if Svs.mem u fvars then raise Exit) () t;
    false
  with Exit -> true

exception Subst_found of term

let rec fmla_find_subst boundvars var sign f =
  let fnF = fmla_find_subst boundvars var in
  let test ls vs t tv =
    sign && ls_equal ls ps_equ && vs_equal vs var &&
      not (t_equal t tv) && not (t_boundvars_in boundvars t) in
  match f.t_node with
    | Tapp (ls,[{t_node=Tvar vs} as tv;t])
        when test ls vs t tv -> raise (Subst_found t)
    | Tapp (ls,[t;{t_node=Tvar vs} as tv])
        when test ls vs t tv -> raise (Subst_found t)
    | Tbinop (Tor, f1, f2)  when not sign -> (fnF sign f1); (fnF sign f2)
    | Tbinop (Tand, f1, f2) when sign ->  (fnF sign f1); (fnF sign f2)
    | Tbinop (Timplies, f1, f2) when not sign ->
        (fnF (not sign) f1); (fnF sign f2)
    | Tnot f1 -> fnF (not sign) f1
    | Tquant (_,fb) ->
        let vsl,trl,f' = t_open_quant fb in
        if trl = []
        then
          let boundvars =
            List.fold_left (fun s v -> Svs.add v s) boundvars vsl in
          fmla_find_subst boundvars var sign f'
    | Tlet (_,fb) ->
        let vs,f' = t_open_bound fb in
        let boundvars = Svs.add vs boundvars in
        fmla_find_subst boundvars var sign f'
    | Tbinop (_, _, _) | Tif ( _, _, _)  | Tcase (_, _)
    | Tapp _ | Tfalse | Ttrue -> ()
    | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)

(* Simplify out equalities that could be selected. *)
let rec equ_simp f = t_attr_copy f (match f.t_node with
  | Tbinop (op, f1, f2) ->
       begin match op, equ_simp f1, equ_simp f2 with
       | Tor, { t_node = Tfalse }, f
       | Tor, f, { t_node = Tfalse }
       | Tand, { t_node = Ttrue }, f
       | Tand, f, { t_node = Ttrue }
       | Timplies, { t_node = Ttrue }, f -> f
       | op, f1, f2 -> t_binary op f1 f2
       end
  | Tapp (p,[f1;f2]) when ls_equal p ps_equ ->
       t_equ_simp (equ_simp f1) (equ_simp f2)
  | _ -> t_map equ_simp f)

let rec fmla_quant ~keep_model_vars sign f = function
  | [] -> [], f
  | vs::l ->
     let vsl, f = fmla_quant ~keep_model_vars sign f l in
     if keep_model_vars && has_a_model_attr vs.vs_name then
      vs::vsl, f
     else if t_v_occurs vs f = 0 then
      vsl, f
     else
      try
        fmla_find_subst (Svs.singleton vs) vs sign f;
        vs::vsl, f
      with Subst_found t ->
        let f = t_subst_single vs t f in
        vsl, equ_simp f

let rec fmla_remove_quant ~keep_model_vars f =
  match f.t_node with
    | Tquant (k,fb) ->
        let vsl,trl,f',close = t_open_quant_cb fb in
          if trl <> []
          then f
          else
            let sign = match k with
              | Tforall -> false | Texists -> true in
            let vsl, f' = fmla_quant ~keep_model_vars sign f' vsl in
            let f' = fmla_remove_quant ~keep_model_vars f' in
            t_attr_copy f (t_quant k (close vsl [] f'))
    | _ -> Term.t_map (fmla_remove_quant ~keep_model_vars) f

(*let fmla_remove_quant f =
  Format.eprintf "@[<hov>%a =>|@\n" Pretty.print_fmla f;
  let f = fmla_remove_quant f in
  Format.eprintf "|=>%a@]@.@." Pretty.print_fmla f;
  Pretty.forget_all ();
  f
*)

let simplify_trivial_quantification =
  Trans.rewrite (fmla_remove_quant ~keep_model_vars:false) None

let simplify_trivial_wp_quantification =
  Trans.rewrite (fmla_remove_quant ~keep_model_vars:true) None

let () = Trans.register_transform
  "simplify_trivial_quantification" simplify_trivial_quantification
  ~desc:"@[Simplify@ trivial@ quantifications:@]@\n  \
    @[\
     - @[transform \\exists x. x == y /\\ F@ into F[y/x],@]@\n\
     - @[transform \\forall x. x <> y \\/ F@ into F[y/x].@]@]"

let simplify_trivial_quantification_in_goal =
  Trans.goal
    (fun pr f ->
     [create_prop_decl Pgoal pr (fmla_remove_quant ~keep_model_vars:false f)])

let () = Trans.register_transform
  "simplify_trivial_quantification_in_goal"
   simplify_trivial_quantification_in_goal
  ~desc:"Same@ as@ simplify_trivial_quantification, but@ only@ in@ goals."

(** linearize all the subformulas with the given connector (conj/disj);
    the returned array also contains the sign of each subformula *)
let fmla_flatten conj f =
  let terms = ref [] in
  let rec aux sign f =
    match f.t_node with
    | Tnot f -> aux (not sign) f
    | Tbinop (Tor, f1, f2) when sign <> conj ->
        aux sign f2; aux sign f1
    | Tbinop (Tand, f1, f2) when sign = conj ->
        aux sign f2; aux sign f1
    | Tbinop (Timplies, f1, f2) when sign <> conj ->
        aux sign f2; aux (not sign) f1
    | _ -> terms := (f, sign)::!terms in
  aux true f;
  Array.of_list !terms

(** recreate the structure of a given formula with linearized subformulas *)
let fmla_unflatten conj f formulas =
  let i = ref 0 in
  let rec aux sign f = t_attr_copy f (match f.t_node with
    | Tnot f -> t_not (aux (not sign) f)
    | Tbinop (Tor, f1, f2) when sign <> conj ->
        let f1' = aux sign f1 in t_or f1' (aux sign f2)
    | Tbinop (Tand, f1, f2) when sign = conj ->
        let f1' = aux sign f1 in t_and f1' (aux sign f2)
    | Tbinop (Timplies, f1, f2) when sign <> conj ->
        let f1' = aux (not sign) f1 in t_implies f1' (aux sign f2)
    | _ ->
        let (t, s) = formulas.(!i) in
        assert (sign = s);
        incr i;
        t) in
  aux true f

(** substitute all the terms that appear as a side of an equality/disequality
    and that match the given filter

    equal terms can be substituted in all the terms of surrounding
    conjunctions, while disequal terms can be substituted in all the terms
    of surrounding disjunctions

    substitutions are not exported outside quantifiers (even if their free
    variables are untouched), so the transformation is possibly incomplete
    (but still correct) on formulas that have inner quantifiers *)
let fmla_cond_subst filter f =
  let rec aux f =
    match f.t_node with
    | Tbinop (o, _, _) when o <> Tiff ->
        let conj = match o with
          Tand -> true | Tor | Timplies -> false | Tiff -> assert false in
        let subf = fmla_flatten conj f in
        let subl = Array.length subf in
        for i = 0 to subl - 1 do
          let (f, s) = subf.(i) in
          subf.(i) <- (aux f, s);
        done;
        for i = 0 to subl - 1 do
          let do_subst t1 t2 =
            for j = 0 to subl - 1 do
              if j <> i then
                let (f, s) = subf.(j) in
                subf.(j) <- (t_replace t1 t2 f, s);
            done in
          let (f, s) = subf.(i) in
          match f.t_node with
          | Tapp (ls,[t1;t2]) when ls_equal ls ps_equ && s = conj ->
              if filter t1 t2 then do_subst t1 t2 else
              if filter t2 t1 then do_subst t2 t1
          | _ -> ()
        done;
        fmla_unflatten conj f subf
    | _ -> t_map aux f in
  aux f
