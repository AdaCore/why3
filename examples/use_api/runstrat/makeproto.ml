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

(** Make protocol for parallelism **)
type pipe = { pin : Unix.file_descr;
              pout: Unix.file_descr }

type t =
 | Sequential
 | Parallel of pipe

exception Invalid_fd of Unix.file_descr * pipe
exception Bad_IO of Unix.file_descr * pipe

(** How should I do that? *)
let fd_of_int : int -> Unix.file_descr = Obj.magic
let int_of_fd : Unix.file_descr -> int = Obj.magic

let print_fd fmt fd =
  fprintf fmt "%i" (int_of_fd fd)

let print_pipe fmt pipe =
  fprintf fmt "%a,%a" print_fd pipe.pin print_fd pipe.pout

let read_makeflags () =
  (** slave *)
  try
    let flags = Sys.getenv "MAKEFLAGS" in
    let r = Str.regexp "--jobserver-fds=\\([0-9]+\\),\\([0-9]+\\)" in
    ignore (Str.search_forward r flags 0);
    Parallel
      {pin = fd_of_int (int_of_string  (Str.matched_group 1 flags));
       pout = fd_of_int (int_of_string  (Str.matched_group 2 flags))}
  with Not_found ->
      (** No MAKEFLAGS or no --jobserver-fds: sequential*)
    Sequential

let make_jobserver j =
  if j <= 1 then
    invalid_arg "make_serverjob: number of worker must be greater than 1";
  (** master *)
  let pin,pout = Unix.pipe () in
  let pipe = {pin = pin; pout = pout} in
  let s = String.make 1 '|' in
  for i = 1 to j do
    ignore (Unix.write pipe.pout s 0 1)
  done;
  pipe

let from_fd_id pin pout =
  let pipe = {pin = fd_of_int pin; pout = fd_of_int pout} in
  begin try ignore (Unix.select [pipe.pin] [] [] 0.)
    with Unix.Unix_error (Unix.EBADF,_,_) ->
      raise (Invalid_fd (pipe.pin,pipe));
  end;
  begin try ignore (Unix.select [] [pipe.pout] [] 0.)
    with Unix.Unix_error (Unix.EBADF,_,_) ->
      raise (Invalid_fd (pipe.pout,pipe))
  end;
  pipe

(** Wait for a job token *)
let wait_worker pipe =
  let s = String.create 1 in
  let n =
    try Unix.read pipe.pin s 0 1
    with Unix.Unix_error(Unix.EBADF,_,_) ->
      raise (Invalid_fd (pipe.pin,pipe))
  in
  if n <> 1 then raise (Bad_IO (pipe.pin,pipe))

(** Give back the job token *)
let release_worker =
  let s = String.make 1 '|' in
  fun pipe ->
  let n =
    try Unix.write pipe.pout s 0 1
    with Unix.Unix_error(Unix.EBADF,_,_) ->
      raise (Invalid_fd (pipe.pout,pipe))
  in
  if n <> 1 then raise (Bad_IO (pipe.pout,pipe))

let print_error fmt = function
  | Invalid_fd (fd,pipe) ->
    fprintf fmt "Invalid file descriptor given %a for the pipe (%a)"
      print_fd fd print_pipe pipe
  | Bad_IO (fd,pipe) ->
    fprintf fmt "Bad io for the file descriptor given %a for the pipe (%a)"
      print_fd fd print_pipe pipe
  | exn -> raise exn
