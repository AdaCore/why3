open Theory

let elt a =
  let rec aux acc = function
    | Decl a -> a::acc
    | Use t -> List.fold_left aux acc t.th_decls in
  List.rev (aux [] a)


let t = Transform.TDecl_or_Use_Decl.elt elt
