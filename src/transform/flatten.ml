open Theory

let elt a =
  let rec aux first_level acc d = match first_level, d.d_node with
    | _,Duse t -> Context.ctxt_fold (aux false) (d::acc) t.th_ctxt
    | false,Dprop (Pgoal,_,_) -> acc
    | false,Dprop (Plemma,i,f) -> (create_prop Paxiom (Ident.id_dup i) f)::acc
    | _ -> d::acc 
  in
  (* Pourquoi ce rev? *)
  let r =  (aux true [] a) in
  Format.printf "flat %a : %a@\n" Pretty.print_decl a Pretty.print_decl_list r;
  r


let t = Transform.elt elt
