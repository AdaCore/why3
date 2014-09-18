open Term
open Decl


let rec curry t = match t.t_node with
  | Tbinop (Timplies, lhs, rhs) -> expand t lhs (curry rhs)
  | _ -> t_map curry t

and expand orig l r = match l.t_node with
  | Tbinop (Tand, a, b) -> expand orig a (expand orig b r)
  | _  -> t_label_copy orig (t_implies (curry l) r)


let curry = Trans.goal (fun pr t -> [create_prop_decl Pgoal pr (curry t)])



let () =
  Trans.register_transform "curry" curry
    ~desc:"Currify."
