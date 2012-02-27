(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
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
open Why3session_lib

let cmds =
  [|
    Why3session_copy.cmd_mod;
    Why3session_copy.cmd_copy;
    Why3session_copy.cmd_archive;
    Why3session_info.cmd;
    Why3session_rm.cmd;
  |]

let usage = "why3session cmd [opts]"

let print_usage () =
  let maxl = Array.fold_left
    (fun acc e -> max acc (String.length e.cmd_name)) 0 cmds in
  eprintf "%s@.@.command:@.@[<hov>%a@]@."
    usage (Pp.print_iter1 Array.iter Pp.newline
             (fun fmt e -> fprintf fmt "%s   @[<hov>%s@]"
               (Util.padd_string ' ' e.cmd_name maxl) e.cmd_desc)) cmds;
  exit 1



let () =
  if Array.length Sys.argv < 2 then print_usage ();
  let cmd_name = Sys.argv.(1) in
  match cmd_name with "-h" | "--help" -> print_usage ()
    | "-v" | "--version" -> print_version ()
    | _ -> ();
  let module M = struct exception Found of cmd end in
  let cmd =
    try
      Array.iter (fun e ->
        if e.cmd_name = cmd_name
        then raise (M.Found e)) cmds;
      eprintf "command %s unknown@." cmd_name;
      print_usage ()
    with M.Found cmd -> cmd
  in
  incr Arg.current;
  let cmd_usage = sprintf "why3session %s [opts]:" cmd_name in
  Arg.parse (Arg.align cmd.cmd_spec) anon_fun cmd_usage;
  cmd.cmd_run ()
