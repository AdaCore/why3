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
type rc_value =
  | RCint of int
  | RCbool of bool
  | RCfloat of float
  | RCstring of string
  | RCident of string

type t = (string list * (string * rc_value) list) list

val int : rc_value -> int
  (** raise Failure "Rc.int" if not a int value *)

val bool : rc_value -> bool
  (** raise Failure "Rc.bool" if not a int value *)

val string : rc_value -> string
  (** raise Failure "Rc.string" if not a string or an ident value *)

val from_file : string -> t
  (** returns the records of the file [f]
      @raise Not_found is f does not exists 
      @raise Failure "lexing" in case of incorrect syntax *)

val to_file   : string -> t -> unit
  (** save the records in the filr [f] *)

val get_home_dir : unit -> string
  (** returns the home dir of the user *)


