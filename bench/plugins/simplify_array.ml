open Term
open Termlib
open Theory

let prelude = ["prelude"]
let array = "Array"
let store = ["store"]
let select = ["select"]

let make_rt_rf h =
  let rec rt env t =
    let t = t_map (rt env) (rf env) t in
    let array  = find_theory env prelude array in
    let store  = (ns_find_ls array.th_export store).ls_name in
    let select = (ns_find_ls array.th_export select).ls_name in
    match t.t_node with
      | Tapp (lselect,[{t_node=Tapp(lstore,[_;a1;b])};a2])
          when lselect.ls_name == select &&
            lstore.ls_name == store &&
            t_equal_alpha a1 a2 -> b
      | _ -> t
  and rf ctxt f = f_map (rt ctxt) (rf ctxt) f  in
  rt,rf
  
let t () =
  let h = Hashtbl.create 5 in
  let rt,rf = make_rt_rf h in
  Transform.rewrite_env rt rf

let () = Driver.register_transform "simplify_array" t
