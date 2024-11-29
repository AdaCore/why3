(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Wstdlib
open Ident
open Term

(* Information about the term that triggers VC.  *)
type vc_term_info = {
  mutable vc_inside : bool;
  (* true if the term that triggers VC is currently processed *)
  mutable vc_loc : Loc.position option;
  (* the position of the term that triggers VC *)
  mutable vc_func_name : string option;
  (* the name of the function for that VC was made. None if VC
     is not generated for postcondition or precondition) *)
}

module Cmp : sig
  type t = (lsymbol * Loc.position option * Ident.Sattr.t)

  val compare: t -> t -> int
end

module S : Set.S with type elt = Cmp.t and type t = Set.Make(Cmp).t

val add_model_element: S.elt -> S.t -> S.t

(*
val model_trace_for_postcondition:
  attrs:Ident.Sattr.t -> vc_term_info -> Ident.Sattr.t
 *)

val check_enter_vc_term: Term.term -> bool -> vc_term_info -> unit

val check_exit_vc_term: Term.term -> bool -> vc_term_info -> unit

val update_info_labels: string -> Sattr.t Mstr.t -> Term.term ->
  Term.lsymbol -> Sattr.t Mstr.t

val check_for_counterexample: Term.term -> bool
(* Check if a term should be added for counterexample analysis *)
