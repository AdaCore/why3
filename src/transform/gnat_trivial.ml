open Term

let rec is_trivial fml =
   (* Check wether the formula is trivial.  *)
   match fml.t_node with
   | Ttrue -> true
   | Tquant (_,tq) ->
         let _,_,t = t_open_quant tq in
         is_trivial t
   | Tlet (_,tb) ->
         let _, t = t_open_bound tb in
         is_trivial t
   | Tbinop (Timplies,_,t2) ->
         is_trivial t2
   | Tcase (_,tbl) ->
         List.for_all (fun b ->
            let _, t = t_open_branch b in
            is_trivial t) tbl
   | _ -> false

let is_trivial_trans =
  Trans.goal_l (fun _pr t ->
      if is_trivial t then
        [] (* Goal is proved *)
      else
        (* Fail to be clean. Should be equivalent to rebuilding the goal (it
           would raise the NoProgress error) *)
        raise Exit)

let () = Args_wrapper.wrap_and_register ~desc:"Prove goals whose positive part is just [true]"
    "trivial_true"
    Args_wrapper.Ttrans_l is_trivial_trans
