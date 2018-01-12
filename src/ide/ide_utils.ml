(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

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
