open Config

type plugin = string

let debug = Debug.register_flag "load_plugin"

exception Plugin_Not_Found of plugin * string list

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
  Debug.dprintf debug "Plugin loaded : %s" f;
  Dynlink.loadfile_private f

type ext =
  (* not a plugin extension *)
  | Extbad
  (* good plugin extension *)
  | Extgood
  (* good plugin extension but not the current compilation used *)
  | Extother

let check_extension f =
  let cmxs = Filename.check_suffix f ".cmxs" in
  let cmo = Filename.check_suffix f ".cmo" in
  if not cmxs && not cmo
  then Extbad
  else
    if (if Dynlink.is_native then cmxs else cmo)
    then Extgood else Extother

let () =
  Exn_printer.register (fun fmt exn ->
    match exn with
      | Plugin_Not_Found (pl,sl) ->
        Format.fprintf fmt "The plugin %s can't be found in the directories %a"
          pl (Pp.print_list Pp.space Pp.string) sl
      | _ -> raise exn)
