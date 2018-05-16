open Term
open Decl

let rec elim_quant pol f =
  match f.t_node with
  | Tquant _ ->
    if pol then t_true else t_false
  | _ ->
    try
      t_map_sign elim_quant pol f
    with
      Failure _ -> f

let elim_less (d:decl) =
  match d.d_node with
  | Dprop (Paxiom,_,t) ->
    let t = elim_quant true t in
    if t_equal t t_true then []
    else
      [decl_map (fun _ -> t) d]
  | _ -> [d]

let () =
  Trans.register_transform "abstract_quantifiers" (Trans.decl elim_less None)
    ~desc:"abstract@ quantifiers@ in@ the@ axioms@ of@ the@ context@."
