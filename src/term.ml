include Termbase

let map f t = 
  let rec aux t =
    let t = match t.node with
    | BVar _ -> assert false
    | Var _ -> t
    | App (t1,t2) -> app (aux t1) (aux t2)
    | Tuple (t1,t2) -> tuple (aux t1) (aux t2)
    | Case (t,c) -> 
        let p,nl,t = open_case c in
        case t p nl (aux t)
    | Lam (ty,b) -> 
        let n,t = open_lam b in
        lam n ty (aux t) in
    f t in
  aux t

