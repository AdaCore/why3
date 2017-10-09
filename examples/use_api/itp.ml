(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(*******************

Small text-based interactive prover using new Why3 session format, to be run in OCaml toplevel.

******************)

#load "unix.cma";;
#load "nums.cma";;
#load "dynlink.cma";;
#load "str.cma";;
#directory "+../menhirLib";;
#load "menhirLib.cmo";;

#directory "+../zip";;
#load "zip.cma";;

#directory "../../lib/why3";;
#load_rec "why3.cma";;

open Format

(* opening the Why3 library *)
open Why3

(* access to the Why configuration *)

(* reads the config file *)
let config : Whyconf.config = Whyconf.read_config None
(* the [main] section of the config file *)
let main : Whyconf.main = Whyconf.get_main config
(* all the provers detected, from the config file *)
let provers : Whyconf.config_prover Whyconf.Mprover.t =
  Whyconf.get_provers config

(* builds the environment from the [loadpath] *)
let env : Env.env = Env.create_env (Whyconf.loadpath main)

open Format

(* loading the drivers *)
let provers =
  Whyconf.Mprover.fold
    (fun _ p acc ->
      try
        let d = Driver.load_driver env p.Whyconf.driver [] in
        (p,d)::acc
      with e ->
        let p = p.Whyconf.prover in
        eprintf "Failed to load driver for %s %s: %a@."
          p.Whyconf.prover_name p.Whyconf.prover_version
          Exn_printer.exn_printer e;
        acc)
    provers
    []

(* One prover named Alt-Ergo in the config file *)
let alt_ergo : Whyconf.config_prover =
  let fp = Whyconf.parse_filter_prover "Alt-Ergo" in
  (** all provers that have the name "Alt-Ergo" *)
  let provers = Whyconf.filter_provers config fp in
  if Whyconf.Mprover.is_empty provers then begin
    eprintf "Prover Alt-Ergo not installed or not configured@.";
    exit 0
  end else
    snd (Whyconf.Mprover.max_binding provers)


(** Testing Session_itp *)

let s = Session_itp.load_session "../bitwalker/why3session.xml"

let id =
  match Session_itp.get_theories s with
    | (n, (thn, _::_::x::_)::_)::_ -> x
    | _ -> assert false

let () =
  printf "%a@." (Session_itp.print_tree s) (Session_itp.get_tree s id)


let pid = Session_itp.graft_proof_attempt s id alt_ergo.Whyconf.prover ~timelimit:42

let () =
  printf "%a@." (Session_itp.print_tree s) (Session_itp.get_tree s id)


let () = Session_itp.save_session "../bitwalker/testsession.xml" s
let s' = Session_itp.load_session "../bitwalker/testsession.xml"
let id' =
  match Session_itp.get_theories s' with
    | (n, (thn, _::_::x::_)::_)::_ -> x
    | _ -> assert false
let () =
  printf "%a@." (Session_itp.print_tree s') (Session_itp.get_tree s' id')

(** testing Controller_itp *)

let my_session = Session_itp.empty_session ()

module M = Controller_itp

let _ = M.add_file_to_session

(* adds a file in the new session *)
let () =
  let fname = "../logic/hello_proof.why" in
  try
    Controller_itp.add_file_to_session env my_session fname
  with e ->
    eprintf "@[Error while reading file@ '%s':@ %a@.@]" fname
      Exn_printer.exn_printer e;
    exit 1

(* explore the theories in that file *)
let theories = Session_itp.get_theories my_session

let () = eprintf "%d theories found@." (List.length theories)

let id = match theories with
  | (n, (thn, x::_)::_)::_ -> x
  | _ -> assert false

let () = Session_itp.print_session my_session

let _id = Session_itp.graft_transf my_session id "toto" []

let () =
  printf "%a@." (Session_itp.print_tree my_session)
         (Session_itp.get_tree my_session id)

let () =
  let callback st =
    printf "callback called with Status = %a@." Controller_itp.print_status st
  in
  Controller_itp.schedule_proof_attempt my_session id alt_ergo.Whyconf.prover
                                        ~timelimit:5 ~callback

let () =
  printf "%a@." (Session_itp.print_tree my_session)
         (Session_itp.get_tree my_session id)

(* add proof attempts for each goals in the theories *)
(*
let add_proofs_attempts g =
  List.iter
    (fun (p,d) ->
      let _pa : unit Session.proof_attempt =
        Session.add_external_proof
          ~keygen:dummy_keygen
          ~obsolete:true
          ~archived:false
          ~timelimit:5
	  ~steplimit:(-1)
          ~memlimit:1000
          ~edit:None
          g p.Whyconf.prover Session.Scheduled
      in ())
    provers

let () =
  List.iter
    (fun th -> List.iter add_proofs_attempts th.Session.theory_goals)
    theories

(* save the session on disk *)
let () = Session.save_session config env_session.Session.session
*)
