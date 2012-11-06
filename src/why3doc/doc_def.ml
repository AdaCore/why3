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

open Why3
open Ident

let loadpath = ref []
let set_loadpath l = loadpath := l
let is_in_path fname =
  List.mem (Filename.dirname fname) !loadpath

let stdlib_url = ref None
let set_stdlib_url u = stdlib_url := Some u

let output_dir = ref None
let set_output_dir d = output_dir := d

let output_file fname =
  let f = Filename.basename fname in
  let base = match !output_dir with
    | None -> f
    | Some dir -> Filename.concat dir f
  in
  base ^ ".html"

type url = string
type tag = string

type file_kind = Local | Loadpath | Unknown

type file = {
  tags: (int * int, tag) Hashtbl.t; (* line, column -> tag *)
  kind: file_kind;
}

let files = Hashtbl.create 17

let add_file fname =
  Hashtbl.add files fname { tags = Hashtbl.create 17; kind = Local }

let get_file fname =
  try
    Hashtbl.find files fname
  with Not_found ->
    let k = if is_in_path fname then Loadpath else Unknown in
    let f = { tags = Hashtbl.create 17; kind = k } in
    Hashtbl.add files fname f;
    f

let make_tag s l =
  let t =
    s ^ "_" ^ string_of_int l (* TODO: improve? *)
  in
  for i = 0 to String.length s - 1 do
    if t.[i] = ' ' then t.[i] <- '_'
  done;
  t

let add_ident id = match id.id_loc with
  | None ->
      ()
  | Some loc ->
      let f, l, c, _ = Loc.get loc in
      let f = get_file f in
      let t = make_tag id.id_string l in
      Hashtbl.add f.tags (l, c) t

let is_def (fn, l, c) =
  let f = get_file fn in
  Hashtbl.find f.tags (l, c)

let make_url fn =
  let url = Filename.basename fn ^ ".html" in
  match (get_file fn).kind, !stdlib_url with
    | Local, _ -> url
    | Loadpath, Some www -> www ^ "/" ^ url
    | _ -> raise Not_found

let locate id = match id.id_loc with
  | None ->
      raise Not_found
  | Some loc ->
      let fn, l, _, _ = Loc.get loc in
      fn, make_url fn, make_tag id.id_string l

