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

let glob = Hashtbl.create 5003

let add id = match id.id_loc with
  | None -> ()
  | Some loc ->
      let f, l, c, _ = Loc.get loc in
Format.eprintf "ADD GLOB: id=%s at %s/%d/%d@." id.id_string f l c;
      Hashtbl.add glob (f, l, c) id

let def _id =
  assert false (*TODO*)

let use _loc _id =
  assert false (*TODO*)

let locate ~fname ~line ~column = Hashtbl.find glob (fname, line, column)

