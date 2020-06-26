(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
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

type def_use = Def | Use

let glob = Hashtbl.create 16
(* Hash [file -> Hash [(line, column) -> ident]] *)

let key loc = let f, l, c, _ = Loc.get loc in f, (l, c)

let add loc idk =
  let kf, k = key loc in
  match (Hashtbl.find glob kf) with
  | hash_f -> if not (Hashtbl.mem hash_f k) then Hashtbl.add hash_f k idk
  | exception Not_found ->
      let hash_f = Hashtbl.create 255 in
      Hashtbl.add glob kf hash_f

let def ~kind id =
  Opt.iter (fun loc -> add loc (id, Def, kind)) id.id_loc

let use ~kind loc id =
  add loc (id, Use, kind)

let clear f =
  match Hashtbl.find glob f with
  | exception Not_found -> ()
  | hash_f -> Hashtbl.clear hash_f

let find loc =
  let (kf, k) = key loc in
  let hash_f = Hashtbl.find glob kf in
  Hashtbl.find hash_f k

(* FIXME allow several entries for the same loc, find returns all of them,
         and why3doc inserts several anchors *)
