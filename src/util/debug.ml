(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
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

let on = ref 0

exception UnknownFlag of string

type flag = string

let flag_table = Hashtbl.create 17

let register_flag s = Hashtbl.replace flag_table s false; s

let lookup_flag s =
  if Hashtbl.mem flag_table s then s else raise (UnknownFlag s)

let list_flags () = Hashtbl.fold (fun s v acc -> (s,s,v)::acc) flag_table []

let test_flag s = !on > 0 && Hashtbl.find flag_table s

let set_flag s = Hashtbl.replace flag_table s true; incr on
let unset_flag s = Hashtbl.replace flag_table s false; decr on

let toggle_flag s = if test_flag s then unset_flag s else set_flag s

let () = Exn_printer.register (fun fmt e -> match e with
  | UnknownFlag s -> Format.fprintf fmt "unknown debug flag `%s'@." s
  | _ -> raise e)

