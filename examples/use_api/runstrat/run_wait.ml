#!/usr/bin/env ocaml

(** a mini-mini-make or mini-mini-sub-make
    just the protocol for parallelism
*)

#load "unix.cma";;
#load "str.cma";;

open Format


let print_args fmt arr =
  for i = 1 to Array.length arr - 1 do
    fprintf fmt "%s" arr.(i);
    if i <> Array.length arr - 1
    then fprintf fmt " "
  done

let add_id = true
let create_process cmd args id =
  if add_id then args.(Array.length args - 1) <- string_of_int id;
  Unix.create_process cmd args Unix.stdin Unix.stdout Unix.stderr

let cmd = Sys.argv.(3)
let args =
  let add_arg = if add_id then 1 else 0 in
  let t = Array.make (Array.length Sys.argv + add_arg - 3) "" in
  Array.blit Sys.argv 3 t 0 (Array.length Sys.argv - 3);
  t


let nb_run = max (int_of_string Sys.argv.(2)) 1
let nb_j = Sys.argv.(1)

type pipe = { pin : Unix.file_descr;
              pout: Unix.file_descr }

(** How should I do that? *)
let fd_of_int : int -> Unix.file_descr = Obj.magic
let int_of_fd : Unix.file_descr -> int = Obj.magic

let pipe =
  if nb_j = "e" then
    (** slave *)
    try
      let flags = Sys.getenv "MAKEFLAGS" in
      let r = Str.regexp "--jobserver-fds=\\([0-9]+\\),\\([0-9]+\\)" in
      ignore (Str.search_forward r flags 0);
      {pin = fd_of_int (int_of_string  (Str.matched_group 1 flags));
       pout = fd_of_int (int_of_string  (Str.matched_group 2 flags))}
    with Not_found ->
        (** No MAKEFLAGS or no --jobserver-fds: sequential*)
      for i = 1 to nb_run do
        let pid = create_process cmd args i in
        ignore (Unix.waitpid [] pid);
      done;
      exit 0
  else (** number of worker as argument *)
    (** master *)
      let pj = try int_of_string nb_j
        with _ ->
          eprintf
            "The first argument must be 'e' or the number of simultaneous \
         workers@.";
          exit 1
      in
      let pj = max pj 1 in
      let pin,pout = Unix.pipe () in
      let pipe = {pin = pin; pout = pout} in
      let s = String.make 1 '|' in
      for i = 1 to pj - 1 do (* one for run_wait.ml *)
        ignore (Unix.write pipe.pout s 0 1)
      done;
      pipe

let makejob = "./makejob"

let makejob_args =
  let t = Array.make (Array.length args + 3) "" in
  Array.blit args 0 t 3 (Array.length args);
  t.(0) <- makejob;
  t.(1) <- string_of_int (int_of_fd pipe.pin);
  t.(2) <- string_of_int (int_of_fd pipe.pout);
  t

(* let () = *)
(*   eprintf "Sys.argv:%a@.args:%a@.makejobs_args:%a@." *)
(*     print_args Sys.argv *)
(*     print_args args *)
(*     print_args makejob_args *)

let () =
  for i = 1 to nb_run - 1 do
    ignore (create_process cmd args i)
  done;
  ignore (create_process cmd args nb_run);
  eprintf "run_wait: *** Attente des tâches non terminées...@.";
  let remaining_child = ref nb_run in
  while !remaining_child <> 0 do
    ignore (Unix.wait ()); decr remaining_child;
  done


(*

(** If the arguments are e and e then we should read ourself --jobserver-fds *)
let () = if Sys.argv.(1) = "d" && Sys.argv.(2) = "d" then
    try
      Unix.execv cmd args
    with Unix.Unix_error(err,_,_) ->
      eprintf "Can't run exec the program %s:%s@." cmd (Unix.error_message err);
      exit 1

*)
