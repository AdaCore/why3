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

module TermCmp : sig
  type t = term

  val before: Loc.position option -> Loc.position option -> bool

  val compare: term -> term -> int
end

module S : Set.S with type elt = term and type t = Set.Make(TermCmp).t

val model_trace_regexp: Str.regexp

val label_starts_with: Str.regexp -> Ident.label -> bool

val get_label: unit Ident.Mlab.t -> Str.regexp -> Ident.label

val print_label: Format.formatter -> Ident.label -> unit

val model_label: Ident.label

val model_vc_term_label: Ident.label

val add_model_element: Term.term -> S.t -> S.t

val add_old: string -> string

val model_trace_for_postcondition: labels: unit Ident.Mlab.t -> vc_term_info -> unit Ident.Mlab.t

val get_fun_name: string -> string

val check_enter_vc_term: Term.term -> bool -> vc_term_info -> unit

val check_exit_vc_term: Term.term -> bool -> vc_term_info -> unit
