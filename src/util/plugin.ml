(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

type plugin = string

let debug = Debug.register_info_flag "load_plugin"
  ~desc:"Print@ debugging@ messages@ about@ plugin@ loading."

exception Plugin_Not_Found of plugin * string list

let loadfile f =
  Debug.dprintf debug "Plugin loaded: %s@." f;
  Dynlink.loadfile_private f


let add_extension p =
  if Dynlink.is_native then p^".cmxs" else p^".cmo"

let load ?dirs p =
  let p = add_extension p in
  let f = match dirs with
    | None -> p
    | Some ld ->
      let rec find = function
        | [] -> raise (Plugin_Not_Found (p,ld))
        | d::ld ->
          let f = Filename.concat d p in
          if Sys.file_exists f then f else find ld in
      find ld in
  loadfile f

type plu =
  (* not a plugin extension *)
  | Plubad
  (* good plugin extension *)
  | Plugood
  (* good plugin extension but fail to load *)
  | Plufail of exn
  (* good plugin extension but not tested *)
  | Pluother

let check_plugin f =
  let cmxs = Filename.check_suffix f ".cmxs" in
  let cmo = Filename.check_suffix f ".cmo" in
  if not cmxs && not cmo
  then Plubad
  else
    if (if Dynlink.is_native then cmxs else cmo)
    then try loadfile f; Plugood with exn -> Plufail exn
    else Pluother

let () =
  Exn_printer.register (fun fmt exn ->
    match exn with
      | Plugin_Not_Found (pl,sl) ->
        Format.fprintf fmt "The plugin %s can't be found in the directories %a"
          pl (Pp.print_list Pp.space Pp.string) sl
      | Dynlink.Error (error) ->
        Format.fprintf fmt "Dynlink error: %s" (Dynlink.error_message error)
      | _ -> raise exn)
