
open Why
open Ident
open Term
open Pgm_types
open Pgm_types.T

module Mnm : Map.S with type key = string

type namespace = private {
  ns_pr : psymbol   Mnm.t;  (* program symbols *)
  ns_ex : esymbol   Mnm.t;  (* exception symbols *)
  ns_mt : mtsymbol  Mnm.t;  (* mutable types *)
  ns_ns : namespace Mnm.t;  (* inner namespaces *)
}

val ns_find_pr : namespace -> string list -> psymbol
val ns_find_ex : namespace -> string list -> esymbol
val ns_find_mt : namespace -> string list -> mtsymbol
val ns_find_ns : namespace -> string list -> namespace

(** a module under construction *)
type uc

val namespace : uc -> namespace
val theory_uc : uc -> Theory.theory_uc

(** a module *)
type t = private {
  m_name   : ident;
  m_th     : Theory.theory;
  m_decls  : Pgm_ttree.decl list;
  m_export : namespace;
}

val create_module : preid -> uc
val close_module : uc -> t

val open_namespace  : uc -> uc
val close_namespace : uc -> bool -> string option -> uc

val use_export : uc -> t -> uc

(** insertion *)

exception ClashSymbol of string

val add_psymbol : psymbol -> uc -> uc
val add_esymbol : esymbol -> uc -> uc
val add_mtsymbol : mtsymbol -> uc -> uc
val add_decl : Pgm_ttree.decl -> uc -> uc
val add_logic_decl : Decl.decl -> uc -> uc

(** TODO: *)
val parse_logic_decls : Env.env -> Loc.position * string -> uc -> uc
val logic_lexpr : Loc.position * string -> Ptree.lexpr

(** exceptions *)

exception CloseModule
