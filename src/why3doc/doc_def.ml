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

open Format
open Why3
open Ident

let loadpath = ref []
let set_loadpath l = loadpath := l

let output_dir = ref None
let set_output_dir d = output_dir := d

let output_file fname =
  let f = Filename.basename fname in
  let base = match !output_dir with
    | None -> f
    | Some dir -> Filename.concat dir f
  in
  base ^ ".html"

type tag = string

type file = {
  tags: (int * int, tag) Hashtbl.t; (* line, column -> tag *)
}

let files = Hashtbl.create 17

let add_file fname =
  Hashtbl.add files fname { tags = Hashtbl.create 17 }

let add_ident id = match id.id_loc with
  | None ->
      ()
  | Some loc ->
      let f, l, c, _ = Loc.get loc in
      try
        let f = Hashtbl.find files f in
        let t = id.id_string ^ "_" ^ string_of_int l in (* TODO: improve? *)
        Hashtbl.add f.tags (l, c) t
      with Not_found ->
        ()

let is_def (fn, l, c) =
  let f = Hashtbl.find files fn in
  Hashtbl.find f.tags (l, c)

let locate id = match id.id_loc with
  | None ->
      raise Not_found
  | Some loc ->
      let fn, l, c, _ = Loc.get loc in
      (Filename.basename fn ^ ".html"), is_def (fn, l, c)
