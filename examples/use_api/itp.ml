(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2015   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(*******************

Small text-based interactive prover using new Why3 session format, to be run in OCaml toplevel.

******************)

(*

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

 *)

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
        exit 1)
    provers
    []


let (s,b) = Session_itp.load_session "../bitwalker/why3session.xml"

let t = Session_itp.get_tree s;;

let my_session = Session_itp.empty_session "test.xml";;

(* excerpt from src/session/session.ml *)
let read_file env ?format fn =
  let theories = Env.read_file Env.base_language env ?format fn in
  let ltheories =
    Stdlib.Mstr.fold
      (fun name th acc ->
        (* Hack : with WP [name] and [th.Theory.th_name.Ident.id_string] *)
        let th_name =
          Ident.id_register (Ident.id_derive name th.Theory.th_name) in
         match th.Theory.th_name.Ident.id_loc with
           | Some l -> (l,th_name,th)::acc
           | None   -> (Loc.dummy_position,th_name,th)::acc)
      theories []
  in
  List.sort
    (fun (l1,_,_) (l2,_,_) -> Loc.compare l1 l2)
    ltheories,theories

(* adds a file in the new session *)
let file : unit (* Session_itp.file *) =
  let fname = "../logic/hello_proof.why" in
  try
    let ordered_theories,theories = read_file env fname in
    Session_itp.add_file my_session fname ordered_theories;
  with e ->
    eprintf "@[Error while reading file@ '%s':@ %a@.@]" fname
      Exn_printer.exn_printer e;
    exit 1





(* explore the theories in that file *)
let theories = file.Session.file_theories
let () = eprintf "%d theories found@." (List.length theories)

(* add proof attempts for each goals in the theories *)

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
