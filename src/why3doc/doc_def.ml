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

open Why3
open Ident

let stdlib_url = ref None
let set_stdlib_url u =
  let u =
    let l = String.length u in
    if l = 0 || u.[l - 1] = '/' then u
    else u ^ "/" in
  stdlib_url := Some u

let output_dir = ref None
let set_output_dir d = output_dir := d

let dir_sep = Str.regexp_string Filename.dir_sep

let output_file fname =
  let fname = Filename.chop_extension fname in
  let base = match !output_dir with
    | None -> fname
    | Some dir ->
      let f = Str.global_replace dir_sep "." fname in
      Filename.concat dir f
  in
  base ^ ".html"

let tag_allowed_char =
  let tbl = Array.make 256 false in
  let s = "-._~!$'()*+,;=:@/?" in (* while & is allowed in uri, it has to be escaped in html *)
  String.iter (fun c -> tbl.(Char.code c) <- true) s;
  let span m n = for i = Char.code m to Char.code n do tbl.(i) <- true done in
  span 'A' 'Z';
  span 'a' 'z';
  span '0' '9';
  fun c -> tbl.(Char.code c)

let pp_tag_escape =
  let hex = "0123456789ABCDEF" in fun fmt s ->
    String.iter (fun c ->
      if tag_allowed_char c then Format.fprintf fmt "%c" c else
        let c = Char.code c in
        Format.fprintf fmt "%%%c%c" hex.[c / 16] hex.[c mod 16]) s

let pp_tag ~kind fmt s l =
  if kind = "theory" then
    (* no need to disambiguate by line number for theories *)
    Format.fprintf fmt "%a_" pp_tag_escape s
  else
    Format.fprintf fmt "%a_%d" pp_tag_escape s l

let local_files = Hashtbl.create 17
let add_local_file fn = Hashtbl.add local_files (Filename.chop_extension fn) ()
let is_local_file = Hashtbl.mem local_files

let pp_url fmt lp =
  if lp <> [] then
    let fn = String.concat "." lp in
    match !stdlib_url with
    | Some www when not (is_local_file fn) ->
      Format.fprintf fmt "%s%s.html" www fn
    | _ ->
      Format.fprintf fmt "%s.html" fn

let pp_anchor ~kind fmt id =
  match id.id_loc with
  | None -> raise Not_found
  | Some loc ->
    let _, l, _, _ = Loc.get loc in (pp_tag ~kind) fmt id.id_string l

let pp_locate ~kind fmt id =
  match id.id_loc with
  | None -> raise Not_found
  | Some _loc ->
    let lp, _, _ =
      try Pmodule.restore_path id with Not_found -> Theory.restore_path id
    in
    Format.fprintf fmt "%a#%a" pp_url lp (pp_anchor ~kind) id
