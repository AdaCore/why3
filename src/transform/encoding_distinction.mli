(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    FranÃ§ois Bobot                                                     *)
(*    Jean-Christophe FilliÃ¢tre                                          *)
(*    Claude MarchÃ©                                                      *)
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


val meta_lsinst : Theory.meta
val meta_kept   : Theory.meta

module Env : sig
  module Mtyl : Map.S with type key = Ty.ty list
  module Htyl : Hashtbl.S with type key = Ty.ty list

  type env = Term.lsymbol Mtyl.t Term.Mls.t

  val empty_env : env

  val print_env : Format.formatter -> env -> unit

  val metas_of_env :
    Term.lsymbol Mtyl.t Term.Mls.t -> Theory.tdecl list -> Theory.tdecl list
  val env_of_metas :
    Theory.meta_arg list list -> Term.lsymbol Mtyl.t Term.Mls.t

end

val lsymbol_distinction : Task.task Trans.trans
