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

(** This module contains generic tools which can be applied on sessions *)

open Session

val unknown_to_known_provers  :
  Whyconf.config_prover Whyconf.Mprover.t ->
  Whyconf.prover ->
  Whyconf.Mprover.key list * Whyconf.Mprover.key list *
    Whyconf.Mprover.key list
(** return others, same name, same version *)

val convert_unknown_prover : keygen:'a keygen -> 'a env_session -> unit
(** try to add new proof_attempt with known provers for all proof
    attempt with unknown provers *)

val filter_proof_attempt :
  ?notify:'key notify ->
  ('key proof_attempt -> bool) -> 'key session -> unit
(** remove all the proof attempts which doesn't satisfy the given predicate *)

val transform_proof_attempt :
  ?notify:'key notify ->
  keygen:'key keygen ->
  'key env_session -> string -> unit
(** replace all the proof attempts of the given session
    by the application of the given
    registered transformation followed by a proof_attempt with the same prover
    and time limit (but undone) *)
