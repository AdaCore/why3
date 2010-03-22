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

(* Compilation of pattern-matching *)

open Ty
open Term

module Compile
  (X : sig
     type action
     val mk_let : vsymbol -> term -> action -> action
     val mk_case : term -> (pattern * action) list -> action
     val constructors : tysymbol -> lsymbol list
   end) :
sig

  exception NonExhaustive of pattern list
  exception Unused of X.action

  val compile : 
    term list -> (pattern list * X.action) list -> X.action
    
end

