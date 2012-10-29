(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ident

let flag = Debug.register_flag "track_symbol_use"
  ~desc:"Track@ symbol@ occurrences@ in@ source@ files.@ Used@ by@ why3doc."

let () = Debug.unset_flag flag (* make sure it is unset by default *)

let dummy_id = id_register (id_fresh "dummy")

let glob = Hashtbl.create 5003
  (* could be improved with nested hash tables *)

(* dead code
let with_loc f = function
  | None -> ()
  | Some loc when loc = Loc.dummy_position -> ()
  | Some loc -> f loc
*)

let use loc id =
  let f, l, c, _ = Loc.get loc in
(* Format.eprintf "GLOB USE: id=%s at %s/%d/%d@." id.id_string f l c; *)
  Hashtbl.add glob (f, l, c) id

let locate pos =
  Hashtbl.find glob pos
