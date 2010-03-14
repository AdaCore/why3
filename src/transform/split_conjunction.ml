open Term
open Theory

let split_pos = 
  let rec rf acc f =
    match f.f_node with
      | Ftrue -> acc
      | Ffalse -> f::acc
      | Fapp _ -> f::acc
      | Fbinop (Fand,f1,f2) -> rf (rf acc f2) f1
      | Fbinop (Fimplies,f1,f2) -> 
          List.fold_left (fun acc f -> (f_implies f1 f)::acc) 
          acc (rf [] f2)
      | Fbinop (Fiff,f1,f2) -> rf (rf acc (f_implies f1 f2)) (f_implies f2 f1)
      | Fbinop (For,_,_) -> f::acc
      | Fnot _ -> f::acc
      | Fif (fif,fthen,felse) -> 
          rf 
            (rf acc (f_implies fif fthen)) 
            (f_implies (f_not fif) felse)
      | Flet (t,fb) ->
          let vs,f = f_open_bound fb in
          List.fold_left (fun acc f -> (f_let vs t f)::acc) acc (rf [] f)
      | Fcase _ -> (* TODO better *) f::acc
      | Fquant (Fforall,fmlaq) ->
          let vsl,trl,fmla = f_open_quant fmlaq in
          List.fold_left (fun acc f -> 
                            (* Remove unused variable*)
                         (f_forall vsl trl f)::acc) acc (rf [] fmla)
      | Fquant (Fexists,_) -> f::acc in
  rf []


let elt d =
  match d.d_node with
    | Dprop (Pgoal,pr) ->
        begin
          try
            let l = split_pos pr.pr_fmla in
            List.map (fun p ->
                        create_prop_decl Pgoal
                          (create_prop (Ident.id_clone pr.pr_name) p)) l
          with Exit -> [d]
        end
    | _ -> [d]

let t () = Transform.elt elt

let () = Driver.register_transform "split_conjunction" t
