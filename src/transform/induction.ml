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

let debug = Debug.register_flag "induction"

type ind_info =
    {tact : string ;
     cands : Term.Svs.t;
     ind_v : Term.vsymbol;
     itsk : Term.term;
     pred : Term.term;
     sg : Term.term;
     }

let show_info i =
   Format.printf "\nInduction tactic: %s  @." i.tact;
   Format.printf "Initial task: %a @.Candidates: " Pretty.print_term i.itsk;
   Svs.iter (fun x -> Format.printf "%a @." Pretty.print_vs x) i.cands;
   Format.printf "Induction on variable:   %a @." Pretty.print_vs i.ind_v;
   Format.printf "Induction predicate:   %a @." Pretty.print_term i.pred;
   Format.printf "Induction sub-task: %a \n@." Pretty.print_term i.sg  

(* if Debug.test_flag debug then begin
    print_string "sigma_inst: ";
    Mtv.iter (fun x tx -> Format.printf "(%a : %a) @ \n"
      Pretty.print_tv x Pretty.print_ty tx ) sigma
  end; *)

let show_me_pvars _km _t bl = 
  let _ = List.map t_open_branch bl in
  ()
  


let decompose_forall t =
  let rec aux qvl_acc t = match t.t_node with
    | Tquant (Tforall, qt) ->
      let qvl, _, t = t_open_quant qt in aux (qvl_acc @ qvl) t
    | _ -> qvl_acc, t
  in
  let qvl, t = aux [] t in (List.fold_right Svs.add qvl Svs.empty), qvl, t

let defn_candidate vs_acc km ls tl qvs =
  let arg_candidate  = function
    | Tvar x when Svs.mem x qvs -> Svs.add x vs_acc
    | _ -> vs_acc
  in match (find_logic_definition km ls) with
    | Some defn ->
      begin match ls_defn_decrease defn with
	| [i] -> arg_candidate (List.nth tl i).t_node
	| _  -> vs_acc
      end
    | None -> vs_acc

let t_candidates km qvs t =
   let rec t_candidate vs_acc t =
     let vs_acc = match t.t_node with
       | Tapp (ls, tl) -> defn_candidate vs_acc km ls tl qvs
       | Tcase (t, bl) -> show_me_pvars km t bl; vs_acc
       | _ -> vs_acc
     in t_fold t_candidate vs_acc t
   in t_candidate Svs.empty t


let indv_ty x = match x.vs_ty.ty_node with
  | Tyapp (ts, _) -> ts, ty_app ts (List.map ty_var ts.ts_args)
  | Tyvar _ -> assert false

let heuristic vss =
  let x = Svs.choose vss in
  let ts, ty = indv_ty x in
  x, ts, ty

let split_quantifiers x qvl =
  let rec aux left = function
    | hd :: tl when vs_equal x hd -> List.rev left, tl
    | hd :: tl -> aux (hd :: left) tl
    | [] -> assert false
  in aux [] qvl


let name_from_type ty =
  let s = match ty.ty_node with
    | Tyapp (ts, _) -> ts.ts_name.id_string
    | Tyvar tv -> tv.tv_name.id_string
  in
  if s = "" then "x" else String.make 1 s.[0]


(*********************************************************)
(*******   Induction tactic on type definition   *********)
(*********************************************************)

let make_induction vs km qvl t =
  let x, ts, ty  = heuristic vs in
  let sigma = ty_match Mtv.empty ty x.vs_ty in
  let qvl1, qvl2 = split_quantifiers x qvl in
  let p = t_forall_close qvl2 [] t in
  let make_case (ls, _) =
    let create_var ty =
      let ty = ty_inst sigma ty in
      let id = Ident.id_fresh (name_from_type ty) in
      Term.create_vsymbol id ty
    in
    let ind_vl = List.map create_var ls.ls_args in
    let ind_tl = List.map t_var ind_vl in
    let goal = t_subst_single x (t_app ls ind_tl (Some x.vs_ty)) p in
    let goal = List.fold_left
      (fun goal vs ->
	if ty_equal vs.vs_ty x.vs_ty
	then Term.t_implies (t_subst_single x (t_var vs) p) goal
	else goal) goal ind_vl
    in
    let goal = t_forall_close (qvl1 @ ind_vl) [] goal in
     if Debug.test_flag debug then
       begin
	 let data = {
	   tact = ""; cands = vs; ind_v = x;
	   itsk = t_forall_close qvl [] t ;
	   pred = p; sg = goal}
	 in  show_info data
       end; goal
  in
  let cl = find_constructors km ts in
  List.map make_case cl 


let induction km t0 =
  let qvs, qvl, t = decompose_forall t0 in
  let vs = t_candidates km qvs t in
  if Svs.is_empty vs then [t0] else make_induction vs km qvl t

let induction = function
  | Some { task_decl = { td_node = Decl { d_node = Dprop (Pgoal, pr, f) } };
	   task_prev = prev;
	   task_known = km } ->
      List.map (add_prop_decl prev Pgoal pr) (induction km f)
  | _ -> assert false
    
let () = Trans.register_transform_l "induction" (Trans.store induction)
  
  
(*********************************************************)
(******* Induction tactic on function definition *********)
(*********************************************************)
  

type htree

let mk_term (_tree : htree) x = (x : Term.term) 


let t_iter_scheme km t = 
  
  let ty_cl ts = 
    List.map (fun (ls, _) -> ls ) (find_constructors km ts) in    
  
  let rec t_patc (acc,n) t =   
    match t.t_node with
      | Tapp (ls, tl)      -> t_tapp (acc,n) (ls,tl)
      | Tif (c, t1, t2)    -> t_tif (acc,n)  (c, t1,t2)
      | Tlet (t, tb)       -> t_tlet (acc,n) (t,tb)
      | Tcase (t, tbl)     -> t_tcase (acc,n) (t, tbl) 
      | Tvar _ | Tconst _  -> acc, n 
      | Ttrue | Tfalse | Tnot _ | Tbinop (_, _, _) | Tquant (_,_) -> acc, n
      | Teps _ -> acc,n 
		
  and t_tcase (acc,n) (t0, bl) = match t0.t_node with
    | (Tvar x)  -> 
      begin
        match x.vs_ty.ty_node with
          | Tyapp (_, _) ->
            let tpl = List.map 
	      (fun b -> let (p,t) = t_open_branch b in (p, t)) bl in 
            let sub_ctl = 
              List.fold_left (fun acc (_, t) -> 
                let ctl,_ = (t_patc ([],(n+1)) t) in ctl @ acc) [] tpl in
            let tpl = 
              List.map (fun b -> let (p,t) = t_open_branch b in [p], t) bl
            in
            let patc = Pattern.CompileTerm.compile ty_cl [t0] tpl in
            let acc = ((patc, n) :: sub_ctl) @ acc in
            acc,n
          | _ -> assert false
      end
    | _ ->  
      let tl = List.map (fun b -> let (_,t) = t_open_branch b in t) bl in 
      List.fold_left (fun (acc,n) t -> t_patc (acc,n) t) (acc,n) tl 
	
  and t_tapp (acc,n) (_ls,tl) = 
    List.fold_left (fun (acc,n) t -> t_patc (acc,n) t) (acc,n) tl
      
  and t_tif (acc,n) (_c,t1,t2) =
    let acc, n = (t_patc (acc,n) t1) in t_patc (acc,n) t2 
				     
  and t_tlet (acc,n) (_t,_tb) = acc,n  in
  
  
  let acc, _ = t_patc ([],0) t in 
  List.iter (fun (pc, n ) -> 
    Format.printf "%d: %a \n @." n Pretty.print_term pc  )  
    (List.rev acc) 
    
 
    

let t_collect_data km qvs t =
  
  let defn_collect_data acc ls tl =
    
    let arg_collect_data i defn = function
      | Tvar x when Svs.mem x qvs ->
        let lmap = 
          try 
            Mvs.find x acc 
          with Not_found -> 
            Mls.empty 
        in Mvs.add x (Mls.add ls (i,defn) lmap) acc
      | _ -> acc 
    in 
    
    match (find_logic_definition km ls) with
      | Some defn ->
        begin match ls_defn_decrease defn with
          | [i] -> arg_collect_data i defn (List.nth tl i).t_node
          | _  -> acc
        end
      | None -> acc 
  in
  
  let rec t_collect acc t =
    let acc = match t.t_node with
      | Tapp (ls, tl) -> defn_collect_data acc ls tl 
      | _ -> acc
    in t_fold t_collect acc t
  
  in t_collect (Mvs.empty) t




let functional_induction km t0 =
  let qvs, _qvl, t = decompose_forall t0 in
  let vmap = t_collect_data km qvs t in
  let _x, lmap =  Mvs.choose vmap in
  let _ = Mls.iter (fun _ls (_i,defn) -> 
    let (_,t) = open_ls_defn defn in t_iter_scheme km t) lmap in  
  if (Mvs.is_empty vmap)
  then 
    [t0] 
  else 
    [t0] 
      
               

              
let functional_induction  = function 
  | Some { task_decl = { td_node = Decl { d_node = Dprop (Pgoal, pr, f) } };
           task_prev = prev;
           task_known = km } ->
    List.map (add_prop_decl prev Pgoal pr) (functional_induction km f)
  | _ -> assert false


let () = Trans.register_transform_l 
  "induction_on_function_definition" 
  (Trans.store functional_induction)








(*
Local Variables:
compile-command: "unset LANG; make -C ../..$"
End:
*)


