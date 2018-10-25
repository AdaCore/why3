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

open Ident

let flag = Debug.register_flag "track_symbol_use"
  ~desc:"Track@ symbol@ occurrences@ in@ source@ files.@ Used@ by@ why3doc."

let () = Debug.unset_flag flag (* make sure it is unset by default *)

type def_use = Def | Use

let glob = Hashtbl.create 5003
  (* could be improved with nested hash tables *)

let key loc = let f, l, c, _ = Loc.get loc in f, l, c

let add loc idk =
  let k = key loc in
  if not (Hashtbl.mem glob k) then Hashtbl.add glob k idk

let def ~kind id =
  Opt.iter (fun loc -> add loc (id, Def, kind)) id.id_loc

let use ~kind loc id =
  add loc (id, Use, kind)

let find loc =
  Hashtbl.find glob (key loc)

(* FIXME allow several entries for the same loc, find returns all of them,
         and why3doc inserts several anchors *)
