open Theory

(* Il faut supprimer les goals et transformer les lemmes en axioms *)

let elt a =
  let rec aux acc d = match d.d_node with
    | Duse t -> Context.ctxt_fold aux (d::acc) t.th_ctxt
    | _ -> d::acc 
  in List.rev (aux [] a)


let t = Transform.TDecl.elt elt
