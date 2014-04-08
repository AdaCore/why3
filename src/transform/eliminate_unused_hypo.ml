open Decl
open Term

type hypothesis = {
  h           : term;
  depend_vars : Svs.t;
}

(* Default callback for Mvs.union *)
let map_union_cb _ a _ = Some a

(* Separate [hypo_list] into a pair of list, the first element of the pair
   being the needed hypothesis and the second being the remaining ones.
   And returns and Mvs of the variables becoming used due to the needed
   hypothesis *)
let rec part_needed_hypothesis vs_map hypo_list =
  let (need, rem, need_vars) =
    List.fold_left (fun (need, rem, vars) hypo ->
      let updated =
        { hypo with depend_vars =
          Svs.filter (fun elt -> not (Mvs.mem elt vs_map)) hypo.depend_vars}
      in
      if Svs.is_empty updated.depend_vars then
        (updated :: need, rem,
         Mvs.union map_union_cb vars (t_freevars Mvs.empty hypo.h))
      else (need, updated :: rem, vars))
  ([], [], Mvs.empty) hypo_list in
  if need <> [] then
    let (need2, rem, new_vars) = part_needed_hypothesis need_vars rem in
    (need @ need2, rem, Mvs.union map_union_cb need_vars new_vars)
  else
    ([], rem, Mvs.empty)

(* create a new term where hypothesis in [hypo_list] imply the term [term] *)
let put_hypothesis_back hypo_list term =
  List.fold_left (fun acc x -> t_implies x.h acc) term hypo_list

(* Compute the depend_vars for an hypothesis. If depend_vars is
   empty then it means that the hypothesis cannot be removed. *)
let rec hypo_deps hypo_term used_vars =
  match hypo_term.t_node with
  | Tapp (ls, tlist) ->
     if ls_equal ps_equ ls then
       let cond_add vs s =
         if Mvs.mem vs used_vars then s
         else Svs.add vs s
       in
       match tlist with
       | [{ t_node = Tvar vs1 }; { t_node = Tvar vs2 }] ->
          cond_add vs2 (cond_add vs1 Svs.empty)
       | { t_node = Tvar vs } :: _
       | _ :: { t_node = Tvar vs } :: _ ->
          cond_add vs Svs.empty
       | _ ->  Svs.empty
     else
       Svs.empty
  | Tbinop (Tor, t1, t2) ->
     Svs.inter (hypo_deps t1 used_vars) (hypo_deps t2 used_vars)
  | Tbinop (Tand, t1, t2) ->
     Svs.union (hypo_deps t1 used_vars) (hypo_deps t2 used_vars)
  | _ -> Svs.empty

(* Called a the level of a binary Timplies node, hypo_term should be the
  right operand and imp_term the left one.
  The function first checks if some of the hypothesis candidate to removal
  are needed given the current hypothesis and puts them back in the term
  tree.
  Then we check if the current hypothesis is candidate to removal.  *)
let check_hypothesis used_vars hypo_list hypo_term imp_term =
  let hypo_vars = t_freevars (Mvs.empty) hypo_term in
  let (needed, hypo_list, new_vars) =
    part_needed_hypothesis hypo_vars hypo_list in
  let imp_term = put_hypothesis_back needed imp_term in
  let old_term = t_implies hypo_term imp_term in
  let used_vars = Mvs.union map_union_cb new_vars used_vars in
  let deps = hypo_deps hypo_term used_vars in
  if Svs.is_empty deps then
    Mvs.union map_union_cb used_vars hypo_vars, hypo_list, old_term
  else
    used_vars, { h = hypo_term; depend_vars = deps } :: hypo_list, imp_term

(* This function simplifies the term [hypo_term] as possible. *)
let rec simpl_hypo hypo_term vsl inside_vars =
  let var_map term =
    (Mvs.union map_union_cb inside_vars (t_freevars Mvs.empty term))
  in
  match hypo_term.t_node with
  | Tbinop (Tor, tl, tr) ->
     let tl = simpl_hypo tl vsl inside_vars in
     let tr = simpl_hypo tr vsl inside_vars in
     (match (tl, tr) with
      | ({t_node = Ttrue}, _) | (_, {t_node = Ttrue}) -> t_true
      | ({t_node = Tfalse}, t) | (t, {t_node = Tfalse}) -> t
      | _ -> t_binary Tor tl tr)
  | Tbinop (Tand, tl, tr) ->
     let tl = simpl_hypo tl vsl (var_map tr) in
     let tr = simpl_hypo tr vsl (var_map tl) in
     (match (tl, tr) with
      | ({t_node = Ttrue}, t) | (t, {t_node = Ttrue}) -> t
      | ({t_node = Tfalse}, _) | (_, {t_node = Tfalse}) -> t_false
      | _ -> t_binary Tand tl tr)
  | Tapp (ls, tlist) ->
     if ls_equal ls ps_equ then
       match tlist with
       | [{t_node = Tvar vs1}; { t_node = Tvar vs2}] ->
          if (Svs.mem vs1 vsl && not (Mvs.mem vs1 inside_vars))
             || (Svs.mem vs2 vsl && not (Mvs.mem vs2 inside_vars)) then
            t_true
          else hypo_term
       | {t_node = Tvar var} :: _ | _ :: {t_node = Tvar var} :: _ ->
          if Svs.mem var vsl && not (Mvs.mem var inside_vars) then
            t_true
          else hypo_term
       | _ -> hypo_term
     else
       hypo_term
  | _ -> hypo_term


(* This function removes hypothesis depending on variable that will no longer
   exists since we met it's quantifier as we ascend through the tree.
   It also simplifies disjunctions of conjunction depending on quantfified
   variables and puts back needed hypothesis on the current term *)
let clear_hypothesis_on_quant qvars used_vars hypo_list qterm =
  let hypo_list =
    List.map (fun hy ->
      match hy.h.t_node with
      | Tapp _ -> hy
      | _ -> let (inter, diff) = Svs.partition (fun elt ->
                                                List.mem elt qvars)
                                               hy.depend_vars in
             { h = simpl_hypo hy.h inter Mvs.empty;
               depend_vars = diff }) hypo_list in
  let (need, rem, newvars) = part_needed_hypothesis Mvs.empty hypo_list in
  let used = List.filter (fun hy ->
    List.for_all (fun x -> not (Svs.mem x hy.depend_vars)) qvars) rem in
  Mvs.union map_union_cb used_vars newvars, used,
  put_hypothesis_back need qterm

(* Flatten a serie of conjunctions as hypothesis into a series of
   implications.
   Here, tl -> tr with tl being a serie of conjunctions *)
let rec flatten_conjunction tl tr =
  match tl.t_node with
  | Tbinop (Tand, { t_node = Ttrue; _ }, t2) -> flatten_conjunction t2 tr
  | Tbinop (Tand, { t_node = Tfalse; _ }, _) -> t_false , tr
  | Tbinop (Tand, t1, t2) ->
     let t2l, t2r = flatten_conjunction t2 tr in
     flatten_conjunction t1 (t_binary Timplies t2l t2r)
  | _ -> tl, tr

(* Descends in the tree, collect used variables as it ascends, collects
   quantifiers node and hypothesis candidate to removal. *)
let rec descend_to_goal term =
  match term.t_node with
  | Tquant (q, tq) ->
     (match q with
     | Texists -> [], t_freevars (Mvs.empty) term, [], term
     | _ ->
     let vsl, trig, qterm = t_open_quant tq in
     if trig <> [] then [], Mvs.empty, [], term
     else
       let qlist, used_vars, hypo_list, qterm = descend_to_goal qterm in
       let used_vars, hypo_list, qterm =
         clear_hypothesis_on_quant vsl used_vars hypo_list qterm in
       vsl @ qlist, used_vars, hypo_list, qterm)
  | Tbinop (Timplies, tl, tr) ->
     let tl, tr = flatten_conjunction tl tr in
     let qlist, used_vars, hypos, tr = descend_to_goal tr in
     let used_vars, hypo_list, term = check_hypothesis used_vars hypos tl tr in
     qlist, used_vars, hypo_list, term
 |_ -> [], t_freevars (Mvs.empty) term, [], term


let put_quantifiers_top term vsl used_vars =
  (* Seem to improve speed for alt-ergo *)
  let vsl = List.filter (fun vs -> Mvs.mem vs used_vars) vsl in
  t_quant Tforall (t_close_quant vsl [] term)

let rm_useless_vars term =
  let qlist, used_vars, _, cleaned_term = descend_to_goal term in
  put_quantifiers_top cleaned_term qlist used_vars


let goalcb psym term = let newterm = rm_useless_vars term in
                       [create_prop_decl Decl.Pgoal psym (newterm)]

let eliminate_unused_hypo = Trans.goal goalcb

let () = Trans.register_transform "eliminate_unused_hypo" eliminate_unused_hypo
                                  ~desc:"Eliminates@ useless@ hypothesis in a \
                                         goal, like introductions of \
                                         unnecessary variables."
