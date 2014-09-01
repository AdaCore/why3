(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3
open Ident

let stdlib_url = ref None
let set_stdlib_url u = stdlib_url := Some u

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

type url = string
type anchor = string

let tag_allowed_char =
  let tbl = Array.make 256 false in
  let s = "-_:" in (* '.' is removed so as to be used as an escape char below *)
  for i = 0 to String.length s - 1 do tbl.(Char.code s.[i]) <- true done;
  let span m n = for i = Char.code m to Char.code n do tbl.(i) <- true done in
  span 'A' 'Z';
  span 'a' 'z';
  span '0' '9';
  fun c -> tbl.(Char.code c)

let tag_escape s =
  let len = ref 0 in
  String.iter (fun c ->
    if tag_allowed_char c then incr len else len := !len + 3) s;
  let len' = !len in
  let len = String.length s in
  if len = len' then s else begin
    let hex = "0123456789ABCDEF" in
    let t = String.create len' in
    let j = ref 0 in
    for i = 0 to len - 1 do
      let c = s.[i] in
      if tag_allowed_char c then begin
        t.[!j] <- c;
        incr j
      end else begin
        let c = Char.code c in
        t.[!j] <- '.';
        t.[!j + 1] <- hex.[c / 16];
        t.[!j + 2] <- hex.[c mod 16];
        j := !j + 3
      end
    done;
    t
  end

let make_tag s l =
  tag_escape s ^ "_" ^ string_of_int l

let local_files = Hashtbl.create 17
let add_local_file fn = Hashtbl.add local_files (Filename.chop_extension fn) ()
let is_local_file = Hashtbl.mem local_files

let make_url fn =
  let url = fn ^ ".html" in
  match !stdlib_url with
  | Some www when not (is_local_file fn) -> www ^ "/" ^ url
  | _ -> url

let anchor id = match id.id_loc with
  | None -> raise Not_found
  | Some loc -> let _, l, _, _ = Loc.get loc in make_tag id.id_string l

let locate id =
  let lp, _, _ =
    try Mlw_module.restore_path id with Not_found -> Theory.restore_path id in
  let url = if lp = [] then "" else make_url (String.concat "." lp) in
  url ^ "#" ^ anchor id
