(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Ident

let flag = Debug.register_info_flag "glob"
  ~desc:"TODO, used in parsing?"

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
