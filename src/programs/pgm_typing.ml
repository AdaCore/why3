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

open Theory
open Pgm_ptree

type env = {
  env_uc : theory_uc;
}

let create_env uc = assert false (*TODO*)

let rec expr env e = 
  let d, ty = expr_desc env e.expr_loc e.expr_desc in
  { expr_desc = d; expr_info = ty; expr_loc = e.expr_loc }

and expr_desc env loc = function
_ -> assert false (*TODO*)
(*   | Econstant of constant *)
(*   | Eident of qualid *)
(*   | Eapply of 'info expr * 'info expr *)
(*   | Esequence of 'info expr * 'info expr *)
(*   | Eif of 'info expr * 'info expr * 'info expr *)
(*   | Eskip  *)
(*   | Eassert of assertion_kind * lexpr *)
(*   | Elazy_and of 'info expr * 'info expr *)
(*   | Elazy_or of 'info expr * 'info expr *)
(*   | Elet of ident * 'info expr * 'info expr *)
(*   | Eghost of 'info expr *)
(*   | Elabel of ident * 'info expr *)
(*   | Ewhile of 'info expr * loop_annotation * 'info expr *)

let code uc id e =
  let env = create_env uc in
  ignore (expr env e)

(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. testl"
End: 
*)
