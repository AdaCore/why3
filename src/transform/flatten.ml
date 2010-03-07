open Theory

let elt a =
  let rec aux first_level acc d = match first_level, d.d_node with
    | _,Duse t -> Context.ctxt_fold (aux false) acc t.th_ctxt
    | false,Dprop (Pgoal,_) -> acc
    | false,Dprop (Plemma,pr) -> create_prop_decl Paxiom pr::acc
    | _ -> d::acc 
  in
  let r =  (aux true [] a) in
  (*Format.printf "flat %a : %a@\n" Pretty.print_decl a Pretty.print_decl_list r;*)
  r


let t = Transform.elt elt
