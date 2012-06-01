(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
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

open Ident
open Term
open Decl
open Theory
open Task

let rec decompose_forall vl f = match f.t_node with
  | Tquant (Tforall, q) ->
      let ql, _, f = t_open_quant q in
      decompose_forall (vl @ ql) f
  | _ ->
      vl, f

let heuristic = Svs.choose (* IMPROVE ME *)

let make_induction _km qvl _x f =
  [t_forall_close qvl [] f]

let induction km f0 =
  let qvl, f = decompose_forall [] f0 in
  let qvs = List.fold_right Svs.add qvl Svs.empty in
  let rec candidate vs f =
    let vs = match f.t_node with
      | Tapp (ls, tl) -> begin match find_logic_definition km ls with
	  | Some defn -> begin match ls_defn_decrease defn with
	      | [i] -> begin match (List.nth tl i).t_node with
		  | Tvar x when Svs.mem x qvs -> Svs.add x vs
		  | _ -> vs
	      end
	      | _ -> vs
	  end
	  | None -> vs
      end
      | _ -> vs
    in
    t_fold candidate vs f
  in
  let candidates = candidate Svs.empty f in
  Svs.iter
    (fun x -> Format.eprintf "candidate %a@." Pretty.print_vs x) candidates;
  if Svs.is_empty candidates then [f0]
  else let x = heuristic candidates in make_induction km qvl x f

let induction = function
  | Some { task_decl = { td_node = Decl { d_node = Dprop (Pgoal, pr, f) } };
	   task_known = km; task_prev = prev } ->
      List.map (add_prop_decl prev Pgoal pr) (induction km f)
  | _ -> assert false

let () = Trans.register_transform_l "induction" (Trans.store induction)
