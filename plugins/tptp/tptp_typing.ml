(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
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

open Why3
open Util
open Ident
open Ty
open Term
open Decl
open Theory

type symbol =
  | STVar of tvsymbol
  | SVar  of vsymbol
  | SType of tysymbol
  | SFunc of lsymbol
  | SPred of lsymbol
  | SletF of tvsymbol list * vsymbol list * term
  | SletP of tvsymbol list * vsymbol list * term

type env = symbol Mstr.t

type implicit = (string,symbol) Hashtbl.t



let typecheck _env _path _ast = Mstr.empty

