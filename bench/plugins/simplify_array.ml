open Term
open Termlib
open Theory

open Transform

let prelude = ["prelude"]
let array = "Array"
let store = ["store"]
let select = ["select"]

let make_rt_rf =
  let rec rt ctxt t =
    let t = t_map (rt ctxt) (rf ctxt) t in
    let array  = find_theory ctxt.ctxt_env prelude array in
    let store  = (find_l array.th_export store).ls_name in
    let select = (find_l array.th_export select).ls_name in
    match t.t_node with
      | Tapp (lselect,[{t_node=Tapp(lstore,[_;a1;b])};a2])
          when cloned_from ctxt lselect.ls_name select &&
            cloned_from ctxt lstore.ls_name store &&
            t_equal_alpha a1 a2 -> b
      | _ -> t
  and rf ctxt f = f_map (rt ctxt) (rf ctxt) f  in
  rt,rf
  
let t () =
  let rt,rf = make_rt_rf in
  Transform.rewrite_map rt rf

let () = Driver.register_transform "simplify_array" t
