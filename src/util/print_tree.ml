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

(*s Tree structures. *)

module type Tree = sig
  type t
  val decomp : t -> string * t list
end

(*s Pretty-print functor. *)

module Make(T : Tree) = struct

  open Format

  (* [print_node] prints one node and [print_sons] its children.
     [pref] is the prefix to output at the beginning of line
     and [start] is the branching drawing (["+-"] the first time,
     and then ["|-"]). *)

  let print fmt t =
    let rec print_node pref t =
      let (s, sons) = T.decomp t in
      pp_print_string fmt s;
      if sons <> [] then
        let w = String.length s in
        let pref' = pref ^ String.make (w + 1) ' ' in
        match sons with
          | [t'] -> pp_print_string fmt "---"; print_node (pref' ^ "  ") t'
          | _ -> pp_print_string fmt "-"; print_sons pref' "+-" sons

    and print_sons pref start = function
      | [] ->
          assert false
      | [s] ->
          pp_print_string fmt "`-"; print_node (pref ^ "  ") s
      | s :: sons ->
          pp_print_string fmt start; print_node (pref ^ "| ") s;
          pp_force_newline fmt (); pp_print_string fmt pref;
          print_sons pref "|-" sons

    in
    print_node "" t

end


(*s Tree structures. *)

module type PTree = sig
  type 'a t
  val decomp : 'a t -> string * 'a t list
end

(*s Pretty-print functor. *)

module PMake(T : PTree) = struct

  open Format

  (* [print_node] prints one node and [print_sons] its children.
     [pref] is the prefix to output at the beginning of line
     and [start] is the branching drawing (["+-"] the first time,
     and then ["|-"]). *)

  let print fmt t =
    let rec print_node pref t =
      let (s, sons) = T.decomp t in
      pp_print_string fmt s;
      if sons <> [] then
        let w = String.length s in
        let pref' = pref ^ String.make (w + 1) ' ' in
        match sons with
          | [t'] -> pp_print_string fmt "---"; print_node (pref' ^ "  ") t'
          | _ -> pp_print_string fmt "-"; print_sons pref' "+-" sons

    and print_sons pref start = function
      | [] ->
          assert false
      | [s] ->
          pp_print_string fmt "`-"; print_node (pref ^ "  ") s
      | s :: sons ->
          pp_print_string fmt start; print_node (pref ^ "| ") s;
          pp_force_newline fmt (); pp_print_string fmt pref;
          print_sons pref "|-" sons

    in
    print_node "" t

end

