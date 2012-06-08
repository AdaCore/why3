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
open Ty
open Term
open Decl
open Theory
open Task


let print_candidates vs =
  Svs.iter (fun x -> Format.eprintf "Candidate %a@." Pretty.print_vs x) vs

(******* Searching for variable candidates to induction tactic  *******)
let decompose_forall t =
  let rec aux qvl_acc t = match t.t_node with
  | Tquant (Tforall, q) ->
      let qvl, _, t = t_open_quant q in
      aux (qvl_acc @ qvl) t
  | _ -> qvl_acc, t 
  in let qvl, t = aux [] t 
     in (List.fold_right Svs.add qvl Svs.empty), qvl, t

let defn_candidate vs_acc km ls tl qvs = 
  let arg_candidate  = function
    | Tvar x when Svs.mem x qvs -> Svs.add x vs_acc
    | _ -> vs_acc 
  in match (find_logic_definition km ls) with
    | Some defn -> 
      begin match ls_defn_decrease defn with
	| [i] -> arg_candidate (List.nth tl i).t_node 
	| _ -> vs_acc
      end
    | None -> vs_acc
      
let t_candidates km qvs t = 
   let rec t_candidate vs_acc t =
     let vs_acc = match t.t_node with
       | Tapp (ls, tl) -> defn_candidate vs_acc km ls tl qvs
       | _ -> vs_acc
     in t_fold t_candidate vs_acc t
   in t_candidate Svs.empty t

let heuristic = Svs.choose (* IMPROVE ME *)


(******* Tranforming the goal into corresponding induction scheme  *******)

let split_quantifiers x qvl = 
  let rec aux x = function
    | (_ as l, [y])      when vs_equal x y  -> (l, [])
    | (_ as l, hd :: tl) when vs_equal x hd -> (l, tl)
    | (_ as l, hd :: tl) -> aux x (l @ [hd], tl) 
    | _ -> assert false 
  in aux x ([], qvl)



let indv_ty x = match x.vs_ty.ty_node with
  | Tyapp (ts, _) -> ts, ty_app ts (List.map ty_var ts.ts_args)
  | Tyvar _ -> assert false
    
  


let make_induction vs km qvl t = 

  (* here I print the initial term *)
  let init_t = t_forall_close qvl [] t in
  Format.printf "Initial task: %a @ \n" Pretty.print_term init_t;

  (* here I print the transformed term *)
  let x = heuristic vs in
  let qvl1, qvl2 = split_quantifiers x qvl in
  let p = t_forall_close qvl2 [] t in
  let ts,ty = indv_ty x in 
  let sigma = ty_match Mtv.empty ty x.vs_ty in

  Format.printf "Induction predicate:@  %a @ \n" Pretty.print_term p; 
  Format.printf "induction on type_symbol:  %a @ \n" Pretty.print_ts ts;
  Format.printf "induction on type:  %a @ \n" Pretty.print_ty ty;
  Mtv.iter (fun x tx -> Format.printf "(%a : %a) @ \n" 
    Pretty.print_tv x Pretty.print_ty tx ) sigma;

  let make_case (ls, _) =
    let _ = if ls = ls then () else () in 
    let f = assert false (* TODO: instancier p sur le constructeur ls *) in
    t_forall_close qvl1 [] f
  in
  (* here I return the new term (TODO) *)
  let cl = find_constructors km ts in
 
  List.iter (fun (cs,_) -> Format.printf "%a @ \n" Pretty.print_cs cs) cl;
  List.map make_case cl
    



(*******                  Applying induction tactic                *******)
let induction km t0 =
  let qvs, qvl, t = decompose_forall t0 in
  let vs = t_candidates km qvs t in 
  print_candidates vs; 
  if Svs.is_empty vs then [t0] else make_induction vs km qvl t 
    
let induction = function
  | Some { task_decl = { td_node = Decl { d_node = Dprop (Pgoal, pr, f) } };
	   task_prev = prev; 
	   task_known = km } ->
      List.map (add_prop_decl prev Pgoal pr) (induction km f)
  | _ -> assert false

let () = Trans.register_transform_l "induction" (Trans.store induction)








(*************************************************************************)
(*

let make_indb = t_subst_single

let t_candidates km qvs t = 
  let rec t_candidates_aux vs_acc t =
    let vs_acc = match t.t_node with
      | Tapp (ls, tl) -> begin match find_logic_definition km ls with
	  | Some defn -> begin match ls_defn_decrease defn with
	      | [i] -> begin match (List.nth tl i).t_node with
		  | Tvar x when Svs.mem x qvs -> Svs.add x vs_acc
		  | _ -> vs_acc 
	      end
	      | _ -> vs_acc
	  end
	  | None -> vs_acc
      end
      | _ -> vs_acc
    in 
    t_fold t_candidates_aux vs_acc t
  in t_candidates_aux Svs.empty t


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
    
let make_induction_bk vs _km qvl t =
  let _x = heuristic vs in 
  [t_forall_close qvl [] t]


Format.printf "induction on type %a @ " Pretty.print_ts ts;

let make_induction vs km qvl t = 

  (* here I print the initial term *)
  let init_t = t_forall_close qvl [] t in
  Format.printf "Initial task: %a @ " Pretty.print_term init_t;

  (* here I print the transformed term *)
  let x = heuristic vs in
  let qvl1, qvl2 = split_quantifiers x qvl in
  let p = t_forall_close qvl2 [] t in
  Format.printf "Induction predicate:@ %a @ " Pretty.print_term p; 

  let ts = match x.vs_ty.ty_node with
    | Tyapp (ts, _) -> ts
    | Tyvar _ -> assert false
  in
  Format.printf "induction on type %a @ " Pretty.print_ts ts;

  let sigma =
    let ty = ty_app ts (List.map ty_var ts.ts_args) in
    ty_match Mtv.empty ty x.vs_ty
  in
  

  let make_case (ls, _) =
    let f = assert false (* TODO: instancier p sur ls constructeur ls *) in
    t_forall_close qvl1 [] f
  in
  (* here I return the new term (TODO) *)
  List.map make_case (find_constructors km ts) 
    



*)
