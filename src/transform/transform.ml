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

open Term
open Ident
open Theory
open Context

(* the memoisation is inside the function *)
type 'a t = { 
  all : context -> 'a;
  clear : unit -> unit;
}

type ctxt_t = context t

let conv_res f c = 
  { all = (fun x -> c (f.all x));
    clear = f.clear; }

let compose f g =
  { all = (fun x -> g.all (f.all x));
    clear = (fun () -> f.clear (); g.clear ()); }

let apply f x = f.all x

let clear f = f.clear ()

let ymemo f tag h =
  let rec aux x =
    let t = tag x in
    try 
      Hashtbl.find h t
    with Not_found -> 
      let r = f aux x in
      Hashtbl.add h t r;
      r in
  aux

let memo f tag h = ymemo (fun _ -> f) tag h

let d_tag d = d.d_tag
let ctxt_tag c = c.ctxt_tag

let t all clear_all =
  { all = all;
    clear = clear_all; }

let register f =
  let memo_t = Hashtbl.create 17 in
  t (memo f ctxt_tag memo_t) (fun () -> Hashtbl.clear memo_t)

let fold_env f_fold v_empty =
  let memo_t = Hashtbl.create 64 in
  let rewind env todo =
    List.fold_left
      (fun env ctxt ->
         let env = f_fold ctxt env in
         Hashtbl.add memo_t ctxt.ctxt_tag env;
         env) 
      env todo 
  in
  let rec f todo ctxt = 
    match ctxt.ctxt_prev with
      | None -> 
	  rewind (v_empty ctxt.ctxt_env) todo
      | Some ctxt2 ->
          try
            let env = Hashtbl.find memo_t ctxt2.ctxt_tag in
            rewind env (ctxt :: todo)
          with Not_found -> 
	    f (ctxt :: todo) ctxt2
  in
  t (f []) (fun () -> Hashtbl.clear memo_t)

let fold f acc = fold_env f (fun _ -> acc)

let fold_map f_fold v_empty =
  let v_empty env = v_empty, init_context env in
  conv_res (fold_env f_fold v_empty) snd

let map f_map =
  fold_map (fun ctxt1 ctxt2 -> (), f_map ctxt1 (snd ctxt2)) ()

let map_concat f_elt = 
  let f_elt ctxt0 ctxt = List.fold_left add_decl ctxt (f_elt ctxt0) in
  map f_elt


let elt f_elt = 
  let memo_elt = Hashtbl.create 64 in
  let f_elt ctxt0 = memo f_elt d_tag memo_elt ctxt0.ctxt_decl in
  let f = map_concat f_elt in
  { f with clear = fun () -> Hashtbl.clear memo_elt; f.clear () }
    
(* Utils *)

(*type odecl =
  | Otype of ty_decl
  | Ologic of logic_decl
  | Oprop of prop_decl
  | Ouse   of theory
  | Oclone of (ident * ident) list*)

let elt_of_oelt ~ty ~logic ~ind ~prop ~use ~clone d = 
  match d.d_node with
    | Dtype l -> [create_ty_decl (List.map ty l)]
    | Dlogic l -> [create_logic_decl (List.map logic l)]
    | Dind l -> ind l 
    | Dprop p -> prop p
    | Duse th -> use th
    | Dclone (th,c) -> clone th c

let fold_context_of_decl f ctxt env ctxt_done d =
  let env,decls = f ctxt env d in
  env,List.fold_left add_decl ctxt_done decls
  
let split_goals =
  let f ctxt0 (ctxt,l) =
    let decl = ctxt0.ctxt_decl in
    match decl.d_node with
      | Dprop (Pgoal, _, _) -> (ctxt, add_decl ctxt decl :: l)
      | Dprop (Plemma, pr, f) ->
          let d1 = create_prop_decl Paxiom pr f in
          let d2 = create_prop_decl Pgoal  pr f in
          (add_decl ctxt d1,
           add_decl ctxt d2 :: l)
      | _ -> (add_decl ctxt decl, l) 
  in
  let g = fold_env f (fun env -> init_context env, []) in
  conv_res g snd

let remove_lemma =
  let f d =
    match d.d_node with
      | Dprop (Plemma, pr, f) ->
          let da = create_prop_decl Paxiom pr f in
          let dg = create_prop_decl Pgoal  pr f in
          [dg;da]
      | _ ->  [d]
  in
  elt f

exception NotGoalContext

let goal_of_ctxt ctxt =
  match ctxt.ctxt_decl.d_node with
    | Dprop (Pgoal,pr,_) -> pr
    | _ -> raise NotGoalContext

let identity = 
  { all = (fun x -> x);
    clear = (fun () -> ()); }

let rewrite_elt rt rf d =
  let re = function
    | Term t -> Term (rt t)
    | Fmla f -> Fmla (rf f)
  in
  match d.d_node with
    | Dtype _ -> [d]
    | Dlogic l -> [create_logic_decl (List.map 
        (function 
           | (ls,Some def) -> 
               let (ls,vsl,expr) = open_ls_defn def in
               (ls,Some (make_ls_defn ls vsl (re expr)))
           | l -> l) l)]
    | Dind indl -> [create_ind_decl 
        (List.map (fun (ls,pl) -> ls, 
        (List.map (fun (pr,f) -> (pr, rf f)) pl)) indl)]
    |Dprop (k,pr,f) -> [create_prop_decl k pr (rf f)]
    |Duse _ |Dclone _ -> [d]

let rewrite_elt rt rf = elt (rewrite_elt rt rf)

let rec find_l ns = function
  | [] -> assert false
  | [a] -> Mnm.find a ns.ns_ls
  | a::l -> find_l (Mnm.find a ns.ns_ns) l
      
let rec find_ty ns = function
  | [] -> assert false
  | [a] -> Mnm.find a ns.ns_ts
  | a::l -> find_ty (Mnm.find a ns.ns_ns) l
  
let rec find_pr ns = function
  | [] -> assert false
  | [a] -> Mnm.find a ns.ns_pr
  | a::l -> find_pr (Mnm.find a ns.ns_ns) l


let cloned_from ctxt i1 i2 = 
  try
    i1 = i2 || Sid.mem i2 (Mid.find i1 ctxt.ctxt_cloned)
  with Not_found -> false

(* let find_theory *)

(* let cloned_from_ts ctxt slth sth sil ls1 = *)
(*   try *)
(*     let th = find_theory ctxt.ctxt_env slth sth in *)
(*     let ls2 = find_ty th.th_export sil in *)
(*     Context_utils.cloned_from ctxt ls1.ts_name ls2.ts_name *)
(*   with Loc.Located _ -> raise Not_found *)
    
(* let cloned_from_ls ctxt slth sth sil ls1 = *)
(*   try *)
(*     let th = find_theory ctxt.ctxt_env l in *)
(*     let ls2 = find_l th.th_export sil in *)
(*       Context_utils.cloned_from ctxt ls1.ls_name ls2.ls_name *)
(*   with Loc.Located _ -> assert false *)
    
(* let cloned_from_pr ctxt l s pr1 = *)
(*   try *)
(*     let th = Typing.find_theory ctxt.ctxt_env l in *)
(*     let pr2 = find_l th.th_export sil in *)
(*     Context_utils.cloned_from ctxt pr1.pr_name pr2.pr_name *)
(*   with Loc.Located _ -> assert false *)

