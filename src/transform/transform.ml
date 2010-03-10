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

open Ident
open Theory
open Context
open Typing

(* the memoisation is inside the function *)
type 'a t = { all : context -> 'a;
              clear : unit -> unit;
              env : env;
         }

type ctxt_t = context t


let conv_res f c = {all = (fun x -> c (f.all x));
                    clear = f.clear;
                    env = f.env}

exception CompositionOfIncompatibleTranformation

let compose f g =
  if g.env != f.env then raise CompositionOfIncompatibleTranformation;
  {all = (fun x -> g.all (f.all x));
   clear = (fun () -> f.clear (); g.clear ());
   env = f.env
  }

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

let t all clear_all env =
  {all = all;
   clear = clear_all;
   env = env;
  }

let fold f_fold v_empty tenv =
  let memo_t = Hashtbl.create 64 in
  let rewind env todo =
    List.fold_left
      (fun env ctxt ->
         let env = f_fold tenv ctxt env in
         Hashtbl.add memo_t ctxt.ctxt_tag env;
         env) env todo in
  let rec f todo ctxt = 
    match ctxt.ctxt_prev with
      | None -> rewind v_empty todo
      | Some (ctxt2) ->
          try
            let env = Hashtbl.find memo_t ctxt2.ctxt_tag in
            rewind env (ctxt::todo)
          with Not_found -> f (ctxt::todo) ctxt2
  in
  t  (f []) (fun () -> Hashtbl.clear memo_t) tenv

let fold_map f_fold v_empty env =
  let v_empty = v_empty,init_context in
  let f_fold env ctxt env_ctxt2 = f_fold env ctxt env_ctxt2 in
  conv_res (fold f_fold v_empty env) snd

let map f_map env =
  fold_map  (fun env ctxt1 ctxt2 -> (), f_map env ctxt1 (snd ctxt2)) () env

let map_concat f_elt env = 
  let f_elt env ctxt0 ctxt = 
    List.fold_left add_decl ctxt (f_elt env ctxt0) in
  map f_elt env


let elt f_elt env = 
  let memo_elt = Hashtbl.create 64 in
  let f_elt env ctxt0 = memo (f_elt env) d_tag memo_elt ctxt0.ctxt_decl in
  let f = map_concat f_elt env in
  {f with clear = fun () -> Hashtbl.clear memo_elt; f.clear ()}
    
let register f env =
  let memo_t = Hashtbl.create 16 in
  t  (memo (f env) ctxt_tag memo_t) (fun () -> Hashtbl.clear memo_t) env

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
  
let split_goals env =
  let f _ ctxt0 (ctxt,l) =
    let decl = ctxt0.ctxt_decl in
    match decl.d_node with
      | Dprop (Pgoal,_) -> (ctxt,(add_decl ctxt decl)::l)
      | Dprop (Plemma,f) ->
          let d1 = create_prop_decl Paxiom f in
          let d2 = create_prop_decl Pgoal f in
          (add_decl ctxt d1,
           (add_decl ctxt d2)::l)
      | _ -> (add_decl ctxt decl,l) in
  let g = fold f (init_context,[]) env in
  conv_res g snd

let extract_goals env =
  let f env ctxt0 (ctxt,l) =
    let decl = ctxt0.ctxt_decl in    
    match decl.d_node with
      | Dprop (Pgoal,f) -> (ctxt,(f.pr_name,f.pr_fmla,ctxt)::l)
      | Dprop (Plemma,f) ->
          let d = create_prop_decl Paxiom f in
          (add_decl ctxt d,
           (f.pr_name,f.pr_fmla,ctxt)::l)
      | _ -> (add_decl ctxt decl,l) in
  let g = fold f (init_context,[]) env in
  conv_res g snd


let identity env = {all = (fun x -> x);
                    clear = (fun () -> ());
                    env = env}
