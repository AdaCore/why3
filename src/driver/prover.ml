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

open Format
open Driver
open Register

(** error handling *)

type error = string

exception Error of error

let report = pp_print_string

let error e = raise (Error e)

let errorm f =
  let buf = Buffer.create 512 in
  let fmt = formatter_of_buffer buf in
  kfprintf
    (fun _ ->
       pp_print_flush fmt ();
       let s = Buffer.contents buf in
       Buffer.clear buf;
       error s)
    fmt f

(** print'n'prove *)

exception NoPrinter
exception UnknownPrinter of string
exception UnknownTransform of string

let print_task drv fmt task =
  let p = match get_printer drv with
    | None -> errorm "no printer specified in the driver file"
    | Some p -> p
  in
  let printer = try lookup_printer p with
    Not_found -> errorm "unknown printer %s" p
  in
  let lookup t = try t, lookup_transform t with
    Not_found -> errorm "unknown transformation %s" t
  in
  let transl = List.map lookup (get_transform drv) in
  let apply task (s, tr) = 
    try
      Register.apply_driver tr drv task 
    with e ->
      Format.eprintf "failure in transformation %s: %s@." 
	s (Printexc.to_string e);
      raise e
  in
  let task = List.fold_left apply task transl in
  let printer = printer (driver_query drv task) in
  fprintf fmt "@[%a@]@?" printer task

let prove_task ?debug ~command ?timelimit ?memlimit drv task =
  let buf = Buffer.create 1024 in
  let fmt = formatter_of_buffer buf in
  print_task drv fmt task; pp_print_flush fmt ();
  call_on_buffer ?debug ~command ?timelimit ?memlimit drv buf

