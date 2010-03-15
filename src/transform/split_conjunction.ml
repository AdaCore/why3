open Term
open Theory

let list_fold_product f acc l1 l2 =
  List.fold_left 
    (fun acc e1 ->
       List.fold_left 
         (fun acc e2 -> f acc e1 e2) 
         l2 acc) 
    acc l1

let rec split_pos split_neg acc f =
  let split_pos = split_pos split_neg in
  match f.f_node with
    | Ftrue -> acc
    | Ffalse -> f::acc
    | Fapp _ -> f::acc
    | Fbinop (Fand,f1,f2) -> split_pos (split_pos acc f2) f1
    | Fbinop (Fimplies,f1,f2) -> 
        list_fold_product 
          (fun acc f1 f2 ->  (f_implies f1 f2)::acc) 
          acc (split_neg [] f1) (split_pos [] f2)
    | Fbinop (Fiff,f1,f2) -> 
        split_pos (split_pos acc (f_implies f1 f2)) (f_implies f2 f1)
    | Fbinop (For,f1,f2) -> 
        list_fold_product 
          (fun acc f1 f2 ->  (f_or f1 f2)::acc) 
          acc (split_pos [] f1) (split_pos [] f2)
    | Fnot _ -> List.fold_left (fun acc f -> f_not f::acc) acc (split_neg acc f)
    | Fif (fif,fthen,felse) -> 
        split_pos 
          (split_pos acc (f_implies fif fthen)) 
          (f_implies (f_not fif) felse)
    | Flet (t,fb) ->
        let vs,f = f_open_bound fb in
        List.fold_left (fun acc f -> (f_let vs t f)::acc) acc (split_pos [] f)
    | Fcase _ -> (* TODO better *) f::acc
    | Fquant (Fforall,fmlaq) ->
        let vsl,trl,fmla = f_open_quant fmlaq in
        List.fold_left (fun acc f -> 
                          (* TODO : Remove unused variable*)
                          (f_forall vsl trl f)::acc) acc (split_pos [] fmla)
    | Fquant (Fexists,_) -> f::acc

let rec split_neg split_pos acc f =
  let split_neg = split_neg split_pos in
  match f.f_node with
    | Ftrue -> f::acc
    | Ffalse -> acc
    | Fapp _ -> f::acc
    | Fbinop (Fand,f1,f2) -> 
        list_fold_product 
          (fun acc f1 f2 ->  (f_and f1 f2)::acc) 
          acc (split_neg [] f1) (split_neg [] f2)
    | Fbinop (Fimplies,f1,f2) ->
        split_pos (split_neg acc f2) f1
    | Fbinop (Fiff,f1,f2) -> 
        (* TODO plus directe? *)
        split_neg acc (f_and (f_implies f1 f2) (f_implies f2 f1))
    | Fbinop (For,f1,f2) -> split_neg (split_neg acc f2) f1
    | Fnot _ -> split_neg acc f
    | Fif (fif,fthen,felse) -> 
          (split_neg acc 
             (f_and (f_implies fif fthen) 
                (f_implies (f_not fif) felse)))
    | Flet (t,fb) ->
        let vs,f = f_open_bound fb in
        List.fold_left (fun acc f -> (f_let vs t f)::acc) acc (split_neg [] f)
    | Fcase _ -> (* TODO better *) f::acc
    | Fquant (Fexists,fmlaq) ->
        let vsl,trl,fmla = f_open_quant fmlaq in
        List.fold_left (fun acc f -> 
                          (* TODO : Remove unused variable*)
                          (f_exists vsl trl f)::acc) acc (split_neg [] fmla)
    | Fquant (Fforall,_) -> f::acc

let split_pos = split_pos (fun acc x -> x::acc)

let elt d =
  match d.d_node with
    | Dprop (Pgoal,pr,f) ->
        begin
          try
            let l = split_pos [] f in
            List.map (fun p -> create_prop_decl Pgoal pr p) l
          with Exit -> [d]
        end
    | _ -> [d]

let t () = Transform.elt elt

let () = Driver.register_transform "split_conjunction" t
