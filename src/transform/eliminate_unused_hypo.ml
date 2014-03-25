open Decl
open Term

type hypothesis = {
  h           : term;
  depend_vars : Svs.t;
}


let rm_useless_vars term =

  (*
   * Descends in the tree, collect used variables as it ascends,
   * collects quantifiers node and hypothesis candidate to removal.
   *)
  let rec descend_to_goal term =

    let part_needed_hypothesis vs_map hypo_list =
      let hypo_list =
        List.map (fun hypo ->
                  {
                    h = hypo.h ;
                    depend_vars = Svs.filter (fun elt ->
                                              not (Mvs.mem elt vs_map))
                                             hypo.depend_vars
                 }) hypo_list
      in
      List.partition (fun hypo -> Svs.is_empty hypo.depend_vars) hypo_list
    in


    (*
     * create a new term where hypothesis in [hypo_list]
     * imply the term [term]
     *)
    let rec put_hypothesis_back hypo_list term =
      match hypo_list with
      | [] -> term
      | h :: t -> t_binary Timplies h.h (put_hypothesis_back t term)
    in

    (*
     * Default callback for Mvs.union
     *)
    let map_union_cb _ a _ = Some a in

    (*
     * Called a the level of a binary Timplies node, hypo_term should be the
     * right operand and imp_term the left one.
     * The function first checks if some of the hypothesis candidate to removal
     * are needed given the current hypothesis and puts them back in the term
     * tree.
     * Then we check if the current hypothesis is candidate to removal.
     *)
    let check_hypothesis used_vars hypo_list hypo_term imp_term =
      let hypo_vars = t_freevars (Mvs.empty) hypo_term in
      let (needed, hypo_list) =  part_needed_hypothesis hypo_vars hypo_list in
      let imp_term = put_hypothesis_back needed imp_term in
      let old_term = t_binary Timplies hypo_term imp_term in
      let used_vars = List.fold_left (fun m nh ->
                                      Mvs.union map_union_cb m
                                                (t_freevars (Mvs.empty) nh.h))
                                     used_vars needed
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
             depend_vars = match ((List.nth tlist 0).t_node,
                                  (List.nth tlist 1).t_node) with
                           | (Tvar vs1, Tvar vs2) ->
                              cond_add vs2 (cond_add vs1
                                                     (Svs.empty))
                           | (Tvar vs, _) | (_, Tvar vs) -> cond_add vs (Svs.empty)
                           | _ -> Svs.empty }
           in
           if Svs.is_empty hypo.depend_vars then
             used_vars, hypo_list, old_term
           else
             used_vars, hypo :: hypo_list, imp_term
         else
           Mvs.union map_union_cb used_vars hypo_vars, hypo_list, old_term
      | _ -> Mvs.union map_union_cb used_vars hypo_vars, hypo_list, old_term
    in

    (*
     * This function removes hypothesis depending on variable
     * that will no longer exists since we met it's quantifier
     * as we ascend through the tree.
     *)
    let clear_hypothesis_on_quant vsl hypo_list =
      let (_, cleared) = List.partition (fun h ->
                                         List.exists (fun vs ->
                                                      Mvs.mem vs
                                                              h.depend_vars)
                                                     vsl)
                                        hypo_list
      in
      cleared
    in
    match term.t_node with
    | Tquant (q, tq) ->
       let vsl, trig, qterm = t_open_quant tq in
       if trig <> [] then
         ([], Mvs.empty, [], term)
       else
         let (qlist, used_vars, hypo_list, qterm) = descend_to_goal qterm in
         ((q, vsl) :: qlist, used_vars,
          clear_hypothesis_on_quant vsl hypo_list, qterm)
    | Tbinop (Timplies, tl, tr) ->
       let (qlist, used_vars, hypos, tr) = descend_to_goal tr in
       let (used_vars, hypo_list, term) = check_hypothesis used_vars
                                                           hypos tl tr in
       qlist, used_vars, hypo_list, term
    |_ -> [], t_freevars (Mvs.empty) term, [], term

  in

  let put_quantifiers_top =
    List.fold_left (fun t qpair -> let (quant, vsl) = qpair in
                                   t_quant quant (t_close_quant vsl [] t))

  in

  let (qlist, _, _, cleaned_term) = descend_to_goal term in
  put_quantifiers_top cleaned_term (List.rev qlist)


let goalcb psym term = [create_prop_decl Decl.Pgoal psym
                                         (rm_useless_vars term)]

let eliminate_unused_hypo = Trans.goal goalcb

let () = Trans.register_transform "eliminate_unused_hypo" eliminate_unused_hypo
                                  ~desc:"Eliminates@ useless@ hypothesis in a \
                                         goal, like introductions of \
                                         unnecessary variables."
