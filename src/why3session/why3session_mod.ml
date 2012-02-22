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

open Why3
open Why3session_lib
open Whyconf
module S = Session

(** TODO:
    filter_state
    filter_time
    filter_?
*)

let tobe_archived = ref None
let set_archived () = tobe_archived := Some true
let unset_archived () = tobe_archived := Some false

let tobe_obsolete = ref false

let spec =
  ("--set-obsolete", Arg.Set tobe_obsolete,
   " the proof is set to obsolete" ) ::
  ("--set-archive", Arg.Unit set_archived,
   " the proof is set to archive" ) ::
  ("--unset-archive", Arg.Unit unset_archived,
   " the proof is set to replayable" ) ::
  (filter_spec @ env_spec)

let run_one env config filters fname =
  let env_session,_ =
    read_update_session ~allow_obsolete:false env config fname in
  session_iter_proof_attempt_by_filter filters
    (fun a ->
      if !tobe_obsolete then S.set_obsolete a;
      begin match !tobe_archived with
        | None -> ()
        | Some b -> S.set_archived a b end;
    ) env_session.S.session;
  S.save_session env_session.S.session


let run () =
  let env,config,should_exit1 = read_env_spec () in
  let filters,should_exit2 = read_filter_spec config in
  if should_exit1 || should_exit2 then exit 1;
  iter_files (run_one env config filters)


let cmd =
  { cmd_spec = spec;
    cmd_desc     = "modify proof based on filter. \
No filter means all the possibilities (except for --filter-archived).";
    cmd_name     = "mod";
    cmd_run      = run;
  }
