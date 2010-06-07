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

(**s transformation from a typed logic to a logic with only one universal
type, builtin types, and symbols used to convert explicitely values from
the universal type to builtin ones (and the other way) *)
(* TODO : learn english... *)


open Util
open Ident
open Ty
open Term
open Decl
open Task






let simple_types =
  Register.store (fun () ->
    Trans.identity)

let _ = Register.register_transform
  "simple_types" simple_types

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. -k"
End:
*)
