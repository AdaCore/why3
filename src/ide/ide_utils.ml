(********************)
(* Terminal history *)
(********************)

module History = struct
  type 'a hole_list = 'a list * 'a list

  (* TODO this looks like we can make it more efficient either with imperative
     feature or by being more clever.  With DLlists, we could have added a
     command in O(1). *)
  let add e l =
    match l with
    | ll, lr ->  [], e :: (List.rev ll) @ lr

  let next l =
    match l with
    | ll, [] -> ll, []
    | ll, [hd] -> ll, [hd]
    (* Get acts on the right list so we never empty right list *)
    | ll, cur :: lr -> cur :: ll, lr

  let prev l =
    match l with
    | hd :: ll, lr -> ll, hd :: lr
    | [], lr -> [], lr

  let get l =
    match l with
    | _, hd :: _ -> Some hd
    | _, [] -> None

  type history = {mutable lc : string hole_list;
                   mutable tr : bool}
(* tr is used to know what was the last query from user because cases for the
   first element of the history and other elements is not the same *)

  let create_history () : history =
    {lc = [], [];
     tr = false}

  let get_current h =
    get h.lc

  let print_next_command h =
    if h.tr then
      begin
        h.lc <- next h.lc;
        get_current h
      end
    else
      begin
        let s = get_current h in
        h.tr <- true;
        s
      end

  let print_prev_command h =
    if h.tr then
      begin
        h.lc <- prev h.lc;
        get_current h
      end
    else
      None

  let add_command h e =
    h.lc <- add e h.lc;
    h.tr <- false

end

(***********************)
(* First Unproven goal *)
(***********************)

(* Children should not give the proof attempts *)
let rec unproven_goals_below_node ~proved ~children ~is_goal acc node =
  if proved node then
    acc
  else
    let nodes = children node in
    if is_goal node && nodes = [] then
      node :: acc
    else
      List.fold_left (unproven_goals_below_node ~proved ~children ~is_goal)
        acc nodes

let get_first_unproven_goal_around ~proved ~children ~get_parent ~is_goal node =
  let rec look_around node =
    match get_parent node with
    | None -> unproven_goals_below_node ~proved ~children ~is_goal [] node
    | Some parent ->
        if proved parent then
          look_around parent
        else
          unproven_goals_below_node ~proved ~children ~is_goal [] parent
  in
  match look_around node with
  | [] -> None
  | hd :: _tl  -> Some hd
