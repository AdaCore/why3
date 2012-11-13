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

(** This simple program implement the client side of the make
    jobserver protocole. It ask for a job token and release it after completion
    of the command

    http://mad-scientist.net/make/jobserver.html
*)

(** ./makejob fdid_in fdid_out command [command options]
   fdid_in and fdid_out are valid filedescriptor given by the caller
 *)

open Format

let print_usage fmt =
  fprintf fmt "usage: %s fdid_in fdid_out command [command options]@."
    Sys.argv.(0)


(** Test there is enough arguments *)
let () = if Array.length Sys.argv < 4
  then begin
    print_usage err_formatter; exit 1;
  end

let cmd,args = Sys.argv.(3),Array.sub Sys.argv 3 (Array.length Sys.argv - 3)

(** How should I do that? *)
let fd_of_int : int -> Unix.file_descr = Obj.magic

(** parse the file descriptor *)
let pipe =
  let fdid_in, fdid_out =
    try int_of_string Sys.argv.(1), int_of_string Sys.argv.(2)
    with Invalid_argument _ ->
      eprintf "The first two argument must be the number of a file descriptor%t"
        print_usage;
      exit 1
  in
  Makeproto.from_fd_id fdid_in fdid_out

let run_job f =
  Makeproto.wait_worker pipe;
  try
    let res = f () in
    Makeproto.release_worker pipe;
    res
  with exn ->
    Makeproto.release_worker pipe;
    raise exn

(** Execute the command *)
let () =
  let ps = run_job (fun () ->
  let pid = Unix.create_process cmd args
    Unix.stdin Unix.stdout Unix.stderr in
  let rpid,ps = Unix.waitpid [] pid in
  assert (pid = rpid);
  ps) in
  match ps with
  | Unix.WEXITED i -> exit i
  | Unix.WSIGNALED i ->
    (** Should not appear on windows ? *)
    Unix.kill (Unix.getpid ()) Sys.sigterm
  | Unix.WSTOPPED _ ->
    (** Not possible since we doesn't wait for that *)
    assert false

