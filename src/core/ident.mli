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

(** Identifiers *)

(** {2 Attributes} *)

type attribute = private {
  attr_string : string;
  attr_tag    : int;
}

module Mattr : Extmap.S with type key = attribute
module Sattr : Extset.S with module M = Mattr

val attr_compare : attribute -> attribute -> int
val attr_equal : attribute -> attribute -> bool
val attr_hash : attribute -> int

val create_attribute : string -> attribute

val list_attributes : unit -> string list

(** {2 Naming convention } *)

val infix: string -> string
(** Apply the naming convention for infix operator (+) *)

val prefix: string -> string
(** Apply the naming convention for prefix operator *)

val mixfix: string -> string
(** Apply the naming convention for mixfix operator *)

val kind_of_fix: string -> [ `None
                           | `Prefix of string
                           | `Infix  of string
                           | `Mixfix of string ]

(** {2 Identifiers} *)

type ident = private {
  id_string : string;               (** non-unique name *)
  id_attrs  : Sattr.t;              (** identifier attributes *)
  id_loc    : Loc.position option;  (** optional location *)
  id_tag    : Weakhtbl.tag;         (** unique magical tag *)
}

module Mid : Extmap.S with type key = ident
module Sid : Extset.S with module M = Mid
module Hid : Exthtbl.S with type key = ident
module Wid : Weakhtbl.S with type key = ident

val id_compare : ident -> ident -> int
val id_equal : ident -> ident -> bool
val id_hash : ident -> int

(** a user-created type of unregistered identifiers *)
type preid = {
  pre_name  : string;
  pre_attrs : Sattr.t;
  pre_loc   : Loc.position option;
}

(** register a pre-ident (you should never use this function) *)
val id_register : preid -> ident

(** create a fresh pre-ident *)
val id_fresh : ?attrs:Sattr.t -> ?loc:Loc.position -> string -> preid

(** create a localized pre-ident *)
val id_user : ?attrs:Sattr.t -> string -> Loc.position -> preid

(** create a duplicate pre-ident with given attributes *)
val id_attr : ident -> Sattr.t -> preid

(** create a duplicate pre-ident *)
val id_clone : ?attrs:Sattr.t -> ident -> preid

(** create a derived pre-ident (inherit attributes and location) *)
val id_derive : ?attrs:Sattr.t -> string -> ident -> preid

(* DEPRECATED : retrieve preid name without registering *)
val preid_name : preid -> string

(** Unique persistent names for pretty printing *)

type ident_printer

val create_ident_printer :
  ?sanitizer : (string -> string) -> string list -> ident_printer
(** start a new printer with a sanitizing function and a blacklist *)

val id_unique :
  ident_printer -> ?sanitizer : (string -> string) -> ident -> string
(** use ident_printer to generate a unique name for ident
    an optional sanitizer is applied over the printer's sanitizer *)

val string_unique : ident_printer -> string -> string
(** Uniquify string *)

val known_id: ident_printer -> ident -> bool
(** Returns true if the printer already knows the id.
    false if it does not. *)

val forget_id : ident_printer -> ident -> unit
(** forget an ident *)

val forget_all : ident_printer -> unit
(** forget all idents *)

val sanitizer' : (char -> string) -> (char -> string) -> (char -> string) -> string -> string
(** generic sanitizer taking a separate encoder for the first and last letter *)

val sanitizer : (char -> string) -> (char -> string) -> string -> string
(** generic sanitizer taking a separate encoder for the first letter *)

(** various character encoders *)

val char_to_alpha : char -> string
val char_to_lalpha : char -> string
val char_to_ualpha : char -> string
val char_to_alnum : char -> string
val char_to_lalnum : char -> string
val char_to_alnumus : char -> string
val char_to_lalnumus : char -> string


(** {2 Name handling for ITP} *)

(* TODO: integrate this functionality into id_unique *)
val id_unique_attr :
  ident_printer -> ?sanitizer : (string -> string) -> ident -> string
(** Do the same as id_unique except that it tries first to use
    the "name:" attribute to generate the name instead of id.id_string *)

(** {2 Attributes for handling counterexamples} *)

val model_attr : attribute
val model_projected_attr : attribute

val model_vc_attr : attribute
val model_vc_post_attr : attribute
val model_vc_havoc_attr : attribute

val has_a_model_attr : ident -> bool
(** [true] when [ident] has one of the attributes above *)

val remove_model_attrs : attrs:Sattr.t -> Sattr.t
(** Remove the counter-example attributes from an attribute set *)

val create_model_trace_attr : string -> attribute

val is_model_trace_attr : attribute -> bool

val append_to_model_trace_attr : attrs:Sattr.t -> to_append:string -> Sattr.t
(** The returned set of attributes will contain the same set of attributes
    as argument attrs except that an attribute of the form ["model_trace:*"]
    will be ["model_trace:*to_append"]. *)

val append_to_model_element_name : attrs:Sattr.t -> to_append:string -> Sattr.t
(** The returned set of attributes will contain the same set of attributes
    as argument attrs except that an attribute of the form ["model_trace:*@*"]
    will be ["model_trace:*to_append@*"]. *)

val get_model_element_name : attrs:Sattr.t -> string
(** If attributes contain an attribute of the form ["model_trace:name@*"],
    return ["name"]. Raises [Not_found] if there is no attribute of
    the form ["model_trace:*"]. *)

val get_model_trace_string : attrs:Sattr.t -> string
(** If attrs contain an attribute of the form ["model_trace:mt_string"],
    return ["mt_string"]. Raises [Not_found] if there is no attribute of
    the form ["model_trace:*"]. *)

val get_model_trace_attr : attrs:Sattr.t -> attribute
(** Return an attribute of the form ["model_trace:*"].
    Raises [Not_found] if there is no such attribute. *)
