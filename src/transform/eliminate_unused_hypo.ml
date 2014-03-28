open Decl
open Term

type hypothesis = {
  h           : term;
  depend_vars : Svs.t;
}

(* Separate [hypo_list] into a pair of list, the first element of the pair
   being the needed hypothesis and the second being the remaining ones.  *)
let part_needed_hypothesis vs_map hypo_list =
  List.fold_left (fun (need,rem) hypo ->
      let updated =
        { hypo with depend_vars =
            Svs.filter (fun elt -> not (Mvs.mem elt vs_map)) hypo.depend_vars}
      in
      if Svs.is_empty updated.depend_vars then (updated :: need, rem)
      else (need, updated :: rem))
  ([], []) hypo_list

(* Default callback for Mvs.union *)
let map_union_cb _ a _ = Some a

(* create a new term where hypothesis in [hypo_list] imply the term [term] *)
let put_hypothesis_back hypo_list term =
  List.fold_left (fun acc x -> t_implies x.h acc) term hypo_list


(* Called a the level of a binary Timplies node, hypo_term should be the
  right operand and imp_term the left one.
  The function first checks if some of the hypothesis candidate to removal
  are needed given the current hypothesis and puts them back in the term
  tree.
  Then we check if the current hypothesis is candidate to removal.  *)
let check_hypothesis used_vars hypo_list hypo_term imp_term =
  let hypo_vars = t_freevars (Mvs.empty) hypo_term in
  let (needed, hypo_list) = part_needed_hypothesis hypo_vars hypo_list in
  let imp_term = put_hypothesis_back needed imp_term in
  let old_term = t_implies hypo_term imp_term in
  let used_vars =
    List.fold_left (fun m nh ->
      Mvs.union map_union_cb m (t_freevars (Mvs.empty) nh.h)) used_vars needed
  in
  match hypo_term.t_node with
  | Tapp (ls, tlist) ->
     if ls_equal ps_equ ls then
       let cond_add vs s =
         if Mvs.mem vs used_vars then s
         else Svs.add vs s
       in
       let hypo = {
         h = hypo_term;
         depend_vars =
           match tlist with
           | [{ t_node = Tvar vs1; _ } ; { t_node = Tvar vs2; _ } ] ->
              cond_add vs2 (cond_add vs1 Svs.empty)
           | { t_node = Tvar vs; _ } :: _
           | _ :: { t_node = Tvar vs; _ } :: _ -> cond_add vs Svs.empty
           | _ -> Svs.empty }
       in
       if Svs.is_empty hypo.depend_vars then
         Mvs.union map_union_cb used_vars hypo_vars, hypo_list, old_term
       else
         used_vars, hypo :: hypo_list, imp_term
     else
       Mvs.union map_union_cb used_vars hypo_vars, hypo_list, old_term
  | _ -> Mvs.union map_union_cb used_vars hypo_vars, hypo_list, old_term


(* This function removes hypothesis depending on variable that will no longer
   exists since we met it's quantifier as we ascend through the tree.  *)
let clear_hypothesis_on_quant vsl hypo_list =
  List.filter (fun h ->
    List.for_all (fun vs ->
      not (Mvs.mem vs h.depend_vars)) vsl) hypo_list

(* Flatten a serie of conjunctions as hypothesis into a series of
   implications *)
let rec flatten_conjunction tl tr =
  match tl.t_node with
  | Tbinop (Tand, { t_node = Ttrue; _ }, t2) -> flatten_conjunction t2 tr
  | Tbinop (Tand, { t_node = Tfalse; _ }, _) -> t_false , tr
  | Tbinop (Tand, tl1, tl2) ->
     let t2l, t2r = flatten_conjunction tl2 tr in
     flatten_conjunction tl1 (t_binary Timplies t2l t2r)
  | _ -> tl, tr

(* Descends in the tree, collect used variables as it ascends, collects
   quantifiers node and hypothesis candidate to removal.  *)
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
       vsl @ qlist, used_vars, clear_hypothesis_on_quant vsl hypo_list, qterm)
  | Tbinop (Timplies, tl, tr) ->
     let tl, tr = flatten_conjunction tl tr in
     let qlist, used_vars, hypos, tr = descend_to_goal tr in
     let used_vars, hypo_list, term = check_hypothesis used_vars hypos tl tr in
     qlist, used_vars, hypo_list, term
 |_ -> [], t_freevars (Mvs.empty) term, [], term

let put_quantifiers_top term vsl used_vars=
  (* Seem to improve speed for alt-ergo *)
  let vsl = List.filter (fun vs -> Mvs.mem vs used_vars) vsl in
  t_quant Tforall (t_close_quant vsl [] term)

let rm_useless_vars term =
  let qlist, used_vars, _, cleaned_term = descend_to_goal term in
  put_quantifiers_top cleaned_term qlist used_vars


let goalcb psym term =
  [create_prop_decl Decl.Pgoal psym (rm_useless_vars term)]

let eliminate_unused_hypo = Trans.goal goalcb

let () = Trans.register_transform "eliminate_unused_hypo" eliminate_unused_hypo
                                  ~desc:"Eliminates@ useless@ hypothesis in a \
                                         goal, like introductions of \
                                         unnecessary variables."
