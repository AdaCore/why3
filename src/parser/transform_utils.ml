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

open Ty
open Term
open Theory

let qualid_of_lstring s =
  assert false (*TODO*)
(* let qualid_of_lstring = function *)
(*   | [] -> invalid_arg "Transfrom_utils.qualid_of_lstring : empty list" *)
(*   | a :: l ->  *)
(*       let id = Ptree.Qident {Ptree.id = a;id_loc = Loc.dummy_position} in *)
(*       List.fold_left (fun acc x ->  *)
(*                         Ptree.Qdot (acc,{Ptree.id = x;id_loc = Loc.dummy_position})) id l *)

let cloned_from_ts env ctxt l s ls1 =
  assert false (*TODO*)
(*   try *)
(*     let th = Typing.find_theory env l in *)
(*     let ls2 = Mnm.find s th.th_export.ns_ts in *)
(*     Context_utils.cloned_from ctxt ls1.ts_name ls2.ts_name *)
(*   with Loc.Located _ -> assert false *)
    
    
let cloned_from_ls env ctxt l s ls1 =
  assert false (*TODO*)
(*   try *)
(*     let th = Typing.find_theory env l in *)
(*     let ls2 = Mnm.find s th.th_export.ns_ls in *)
(*     Context_utils.cloned_from ctxt ls1.ls_name ls2.ls_name *)
(*   with Loc.Located _ -> assert false *)
    
let cloned_from_pr env ctxt l s pr1 =
  assert false (*TODO*)
(*   try *)
(*     let th = Typing.find_theory env l in *)
(*     let pr2 = Mnm.find s th.th_export.ns_pr in *)
(*     Context_utils.cloned_from ctxt pr1.pr_name pr2.pr_name *)
(*   with Loc.Located _ -> assert false *)
