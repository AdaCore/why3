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


let decompose_forall t =
  let rec aux qvl_acc t = match t.t_node with
  | Tquant (Tforall, q) ->
      let qvl, _, t = t_open_quant q in
      aux (qvl_acc @ qvl) t
  | _ -> qvl_acc, t 
  in let qvl, t = aux [] t 
     in (List.fold_right Svs.add qvl Svs.empty), qvl, t


let t_candidates km qvs t =
  let rec recf_candidate vs_acc t =
    let vs_acc = match t.t_node with
      | Tapp (ls, tl) -> begin match find_logic_definition km ls with
	  | Some defn -> begin match ls_defn_decrease defn with
	      | [i] -> begin match (List.nth tl i).t_node with
		  | Tvar x when Svs.mem x qvs -> Svs.add x vs_acc
		  | _ -> vs_acc (*here rec call *)
	      end
	      | _ -> vs_acc
	  end
	  | None -> vs_acc
      end
      | _ -> vs_acc
    in 
    t_fold recf_candidate vs_acc t
  in recf_candidate Svs.empty t


let print_candidates vs =
  Svs.iter (fun x -> Format.eprintf "candidate %a@." Pretty.print_vs x) vs

let heuristic = Svs.choose (* IMPROVE ME *)

let make_induction vs _km qvl t =
  let _x = heuristic vs in 
  [t_forall_close qvl [] t]


(* Term.Svs.t -> Term.term -> Term.Svs.t *)
let induction km t0 =
  let qvs, qvl, t = decompose_forall t0 in
  let vs = t_candidates km qvs t in 
  print_candidates vs; 
  if Svs.is_empty vs then [t0] else make_induction vs km qvl t 
    

(* Task.task_hd option -> Task.task list *)
let induction = function
  | Some { task_decl = { td_node = Decl { d_node = Dprop (Pgoal, pr, f) } };
	   task_prev = prev; 
	   task_known = km } ->
      List.map (add_prop_decl prev Pgoal pr) (induction km f)
  | _ -> assert false


let () = Trans.register_transform_l "induction" (Trans.store induction)




(***************************************************************************)
(*

(* Term.vsymbol list -> Term.term -> Term.vsymbol list * Term.term *)
let rec decompose_forall qvl_acc f = match f.t_node with
  | Tquant (Tforall, q) ->
      let qvl, _, f = t_open_quant q in
      decompose_forall (qvl_acc @ qvl) f
  | _ -> qvl_acc, f




(* Term.Svs.t -> Term.term -> Term.Svs.t *)
let induction km f0 =
  let qvs, qvl, f = decompose_forall [] f0 in
  let rec candidate vs f =
    let vs = match f.t_node with
      | Tapp (ls, tl) -> begin match find_logic_definition km ls with
	  | Some defn -> begin match ls_defn_decrease defn with
	      | [i] -> begin match (List.nth tl i).t_node with
		  | Tvar x when Svs.mem x qvs -> Svs.add x vs
		  | _ -> vs (*here rec call *)
	      end
	      | _ -> vs
	  end
	  | None -> vs
      end
      | _ -> vs
    in
    t_fold candidate vs f
  in
  let candidates = 
    candidate Svs.empty f in print_vs candidates; 
  if Svs.is_empty candidates 
  then [f0] 
  else make_induction km qvl f candidates
    





(* Task.task_hd option -> Task.task list *)
(* recolle les déclarations initiales du but transformé *)
let induction = function
  | Some { task_decl = { td_node = Decl { d_node = Dprop (Pgoal, pr, f) } };
	   task_prev = prev; 
	   task_known = km } ->
      List.map (add_prop_decl prev Pgoal pr) (induction km f)
  | _ -> assert false


let () = Trans.register_transform_l "induction" (Trans.store induction)

*)
