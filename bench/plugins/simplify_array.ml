open Term
open Theory
open Env

let prelude = ["prelude"]
let array = "Array"
let store = ["store"]
let select = ["select"]

let make_rt_rf env =
  let array  = find_theory env prelude array in
  let store  = (ns_find_ls array.th_export store).ls_name in
  let select = (ns_find_ls array.th_export select).ls_name in
  let rec rt t =
    let t = t_map rt rf t in
    match t.t_node with
      | Tapp (lselect,[{t_node=Tapp(lstore,[_;a1;b])};a2])
          when lselect.ls_name == select &&
            lstore.ls_name == store &&
            t_equal_alpha a1 a2 -> b
      | _ -> t
  and rf f = f_map rt rf f  in
  rt,rf
  
let t =
  Register.store_env
  (fun () env ->
     let rt,rf = make_rt_rf env in
     Trans.rewrite rt rf None)

let () = Driver.register_transform "simplify_array" t
