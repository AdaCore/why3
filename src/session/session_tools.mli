(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Generic tools that can be applied on sessions *)

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
(** remove all the proof attempts that do not satisfy the given predicate *)

val transform_proof_attempt :
  ?notify:'key notify ->
  keygen:'key keygen ->
  'key env_session -> string -> unit
(** replace all the proof attempts of the given session
    by the application of the given
    registered transformation followed by a proof_attempt with the same prover
    and time limit (but undone) *)
