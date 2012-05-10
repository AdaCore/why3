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

let formatter = ref Format.err_formatter

exception UnknownFlag of string

type flag = bool ref

let flag_table = Hashtbl.create 17

let gen_register_flag s stop =
  try
    fst (Hashtbl.find flag_table s)
  with Not_found ->
    let flag = ref false in
    Hashtbl.replace flag_table s (flag,stop);
    flag

let register_flag s = gen_register_flag s false

let register_stop_flag s = gen_register_flag s true

let lookup_flag s =
  try fst (Hashtbl.find flag_table s) with Not_found -> raise (UnknownFlag s)

let list_flags () = Hashtbl.fold (fun s (v,_) acc -> (s,v,!v)::acc)
  flag_table []

let is_stop_flag s =
  try snd (Hashtbl.find flag_table s) with Not_found -> raise (UnknownFlag s)

let test_flag s = !s
let nottest_flag s = not !s

let set_flag s = s := true
let unset_flag s = s := false
let toggle_flag s = s := not !s

let () = Exn_printer.register (fun fmt e -> match e with
  | UnknownFlag s -> Format.fprintf fmt "unknown debug flag `%s'@." s
  | _ -> raise e)

let stack_trace = register_flag "stack_trace"
let timestamp = register_flag "timestamp"
let time_start = Unix.gettimeofday ()

let set_debug_formatter = (:=) formatter
let get_debug_formatter () = !formatter

let dprintf flag s =
  if !flag then
    begin
      if !timestamp then Format.fprintf !formatter "<%f>"
        (Unix.gettimeofday () -. time_start);
      Format.fprintf !formatter s
    end
  else Format.ifprintf !formatter s


(*** Options ****)

module Opt = struct
  type spec = (Arg.key * Arg.spec * Arg.doc)

  let desc_debug_list, option_list =
    let opt_list_flags = ref false in
    let desc =
      "--list-debug-flags", Arg.Set opt_list_flags,
      " List known debug flags" in
    let list () =
      if !opt_list_flags then begin
        let list =
          Hashtbl.fold (fun s (_,stop) acc -> (s,stop)::acc)
            flag_table [] in
        let print fmt (p,stop) =
          if stop then Format.fprintf fmt "%s *" p
          else Format.pp_print_string fmt p in
        Format.printf "@[<hov 2>Known debug flags \
(* mark flags which change the behavior) :@\n%a@]@."
          (Pp.print_list Pp.newline print)
          (List.sort Pervasives.compare list);
      end;
      !opt_list_flags in
    desc,list

  let opt_list_flags = Queue.create ()

  let add_flag s = Queue.add s opt_list_flags

  let desc_shortcut flag option desc =
    let set_flag () = add_flag flag in
    let desc = Pp.sprintf "%s (same as --debug %s)" desc flag in
    (option, Arg.Unit set_flag, desc)

  let desc_debug =
    ("--debug", Arg.String add_flag, "<flag> Set a debug flag")

  let opt_debug_all = ref false

  let desc_debug_all =
    let desc_debug =
      Pp.sprintf
        " Set all debug flags (except flags which change the behavior)" in
    ("--debug-all", Arg.Set opt_debug_all, desc_debug)

  let set_flags_selected () =
    if !opt_debug_all then
      List.iter
        (fun (s,f,_) -> if not (is_stop_flag s) then set_flag f)
        (list_flags ());
    Queue.iter (fun flag -> let flag = lookup_flag flag in set_flag flag)
      opt_list_flags

end

(*

  "--parse-only", Arg.Set opt_parse_only,
      " Stop after parsing (same as --debug parse_only)";
  "--type-only", Arg.Set opt_type_only,
      " Stop after type checking (same as --debug type_only)";
  "--debug-all", Arg.Set opt_debug_all,
      " Set all debug flags (except parse_only and type_only)";
  "--debug", Arg.String add_opt_debug,
      "<flag> Set a debug flag";


  (** Debug flag *)
  if !opt_debug_all then begin
    List.iter (fun (_,f,_) -> Debug.set_flag f) (Debug.list_flags ());
    Debug.unset_flag Typing.debug_parse_only;
    Debug.unset_flag Typing.debug_type_only
  end;

  List.iter (fun s -> Debug.set_flag (Debug.lookup_flag s)) !opt_debug;

  if !opt_parse_only then Debug.set_flag Typing.debug_parse_only;
  if !opt_type_only then Debug.set_flag Typing.debug_type_only;
*)
