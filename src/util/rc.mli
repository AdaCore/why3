(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
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

(** Parse rc files *)
exception Bad_value_type of string * string * string
(** key * expected * found *)
exception Key_not_found of string
(** key *)
exception Multiple_value of string
(** key *)
exception Yet_defined_key of string
(** key *)
exception Multiple_section of string
exception Section_b_family of string
exception Family_two_many_args of string
exception Not_exhaustive of  string
exception Yet_defined_section of string
(** key *)


type t
type section
type family  = (string * section) list

val empty : t
val empty_section : section

val get_section : t -> string -> section option
(** return None if the section is not in the rc file *)
val get_family  : t -> string -> family

val set_section : t -> string -> section -> t
val set_family  : t -> string -> family  -> t

val get_int  : ?default:int      -> section -> string -> int
  (** raise Bad_value_type
      raise Key_not_found
      raise Multiple_value
  *)

val get_intl : ?default:int list -> section -> string -> int list
  (** raise Bad_value_type
      raise Key_not_found *)

val set_int : section -> string -> int -> section
  (** raise Yet_defined_key *)

val set_intl : section -> string -> int list -> section
  (** raise Yet_defined_key *)

val get_bool  : ?default:bool       -> section -> string -> bool
  (** raise Bad_value_type
      raise Key_not_found
      raise Multiple_value
  *)

val get_booll  : ?default:bool list -> section -> string -> bool list
  (** raise Bad_value_type
      raise Key_not_found *)

val set_bool : section -> string -> bool -> section
  (** raise Yet_defined_key *)

val set_booll : section -> string -> bool list -> section
  (** raise Yet_defined_key *)


val get_string  : ?default:string      -> section -> string -> string
  (** raise Bad_value_type
      raise Key_not_found
      raise Multiple_value
  *)

val get_stringl : ?default:string list -> section -> string -> string list
  (** raise Bad_value_type
      raise Key_not_found *)

val set_string : section -> string -> string -> section
  (** raise Yet_defined_key *)

val set_stringl : section -> string -> string list -> section
  (** raise Yet_defined_key *)



(* val ident  : ?default:string      -> section -> string -> string *)
(*   (\** raise Bad_value_type *)
(*       raise Key_not_found *)
(*       raise Multiple_value *)
(*   *\) *)

(* val identl : ?default:string list -> section -> string -> string list *)
(*   (\** raise Bad_value_type *)
(*       raise Key_not_found *\) *)

(* val set_ident : section -> string -> string -> section *)
(*   (\** raise Yet_defined_key *)
(*       raise Bad_value_type *)
(*   *\) *)

(* val set_identl : section -> string -> string list -> section *)
(*   (\** raise Yet_defined_key *)
(*       raise Bad_value_type *)
(*   *\) *)

val check_exhaustive : section -> Util.Sstr.t -> unit
  (**  raise Not_exhaustive of string *)

val from_file : string -> t
  (** returns the records of the file [f]
      @raise Not_found is f does not exists
      @raise Failure "lexing" in case of incorrect syntax *)

val to_file   : string -> t -> unit
  (** [to_file f t] save the records [t] in the file [f] *)

val get_home_dir : unit -> string
  (** returns the home dir of the user *)


