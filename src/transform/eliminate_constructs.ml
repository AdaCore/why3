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

open Util
open Ident
open Term
open Decl

(* eliminate let *)

let rec remove_let_t map t =
  match t.t_node with
    | Tlet (t1,tb) ->
        let t1 = remove_let_t map t1 in
        let vs,t2 = t_open_bound tb in
        remove_let_t (Mvs.add vs t1 map) t2
    | Tvar vs ->
        begin try
          Mvs.find vs map
        with Not_found -> t end
    | _ -> t_map (remove_let_t map) (remove_let_f map) t

and remove_let_f map f =
  match f.f_node with
    | Flet (t1,fb) ->
        let t1 = remove_let_t map t1 in
        let vs,f2 = f_open_bound fb in
        remove_let_f (Mvs.add vs t1 map) f2
    | _ -> f_map (remove_let_t map) (remove_let_f map) f

let remove_let_t = remove_let_t Mvs.empty
let remove_let_f = remove_let_f Mvs.empty

let eliminate_let =
  Register.store (fun () -> Trans.rewrite remove_let_t remove_let_f None)

let () = Register.register_transform "eliminate_let" eliminate_let

(* eliminate if then else *)

let merge f l1 l2 =
  let f acc (c1,t1) (c2,t2) =
    (f_and_simp c1 c2, f t1 t2)::acc in
  list_fold_product f [] l1 l2

let merge_l f tl =
  let f acc tl =
    let cond,l = List.split tl in
    (f_and_simp_l cond, f l)::acc in
  list_fold_product_l f [] tl

let and_impl_f sign l =
  if sign 
  then List.fold_left (fun acc (c,f) -> f_and_simp acc (f_implies_simp c f))
    f_true l
  else  List.fold_left (fun acc (c,f) -> f_or_simp acc (f_and_simp c f))
    f_false l
    

let rec remove_ite_t t =
  match t.t_node with
    | Tif (f,t1,t2) -> 
        let g f t = 
          List.map (fun (e,t) -> f_and_simp f e,t) (remove_ite_t t)in
        List.rev_append (g f t1) (g (f_not f) t2) 
    | Tbvar _ | Tvar _ | Tconst _ -> [f_true,t]
    | Tapp (ls,tl) -> 
        merge_l (fun tl -> t_app ls tl t.t_ty) (List.map remove_ite_t tl)
    | Tlet (t1,tb) ->
        let vs,t2 = t_open_bound tb in
        merge (t_let vs) (remove_ite_t t1) (remove_ite_t t2)
    | Tcase (tl,tbl) ->
        let tl = merge_l (fun x -> x) (List.map remove_ite_t tl) in
        let tbl = List.map 
          (fun e -> 
             let pl,t = t_open_branch e in
             List.map (fun (c,t) -> (c,(pl,t))) (remove_ite_t t)) tbl in
        let tbl = merge_l (fun x -> x) tbl in
        merge (fun tl tbl -> t_case tl tbl t.t_ty) tl tbl
    | Teps fb ->
        let vs,f = f_open_bound fb in [f_true,t_eps vs (remove_ite_f true f)]
and remove_ite_f sign f = 
  match f.f_node with
    | Fapp (ls,tl) ->
        let l = merge_l (f_app ls) (List.map remove_ite_t tl) in
        and_impl_f sign l
    | Flet (t,fb) ->
        let vs,f' = f_open_bound fb in
        let f'' = remove_ite_f sign f' in
        let tl = remove_ite_t t in
        begin match tl with
          | [c,_] when f' == f'' -> assert (c == f_true); f
          | _ -> 
              let tl = List.map (fun (c,t) -> c,f_let vs t f) tl in
              and_impl_f sign tl
        end
    | Fquant (q, b) -> 
        let vl, tl, f1 = f_open_quant b in
        let f1' = remove_ite_f sign f1 in
        let tr_map (changed,acc) = function
          | Term t as e -> 
              let tl = remove_ite_t t in
              begin match tl with
                | [c,_] -> assert (c == f_true); changed,(e::acc)
                | _ -> true,
                    (* can we do better? *)
                    List.fold_left (fun acc (_,t) -> Term t::acc) acc tl
              end
          | Fmla f as e ->
              let f' = remove_ite_f true f in (*TODO trigger sign *)
              if f == f' then changed,e::acc else true,(Fmla f'::acc) in
        let changed,tl' = rev_map_fold_left 
          (fun acc -> List.fold_left tr_map (acc,[])) false tl in
        if f1' == f1 && (not changed) then f
        else f_quant q vl tl' f1'
    | _ -> f_map_sign (fun _ -> assert false) remove_ite_f sign f

let remove_ite_decl d =
  match d.d_node with
    | Dlogic l ->
        let fn acc = function
          | ls, Some ld ->
              let vl,e = open_ls_defn ld in
              begin match e with
                | Term t ->
                    begin let tl = remove_ite_t t in
                    match tl with
                      | [] -> assert false
                      | [c,t] ->
                          assert (c == f_true);
                          acc,make_ls_defn ls vl (Term t)
                      | _ ->
                          let d = ls,None in
                          let h = t_app ls (List.map t_var vl) t.t_ty in
                          let fax acc (c,t) =
                            let f = f_forall vl [] (f_implies c (f_equ h t)) in
                            let pr = create_prsymbol (id_clone ls.ls_name) in
                            (create_prop_decl Paxiom pr f)::acc in
                            List.fold_left fax acc tl,d
                    end
                | Fmla f -> acc,make_ls_defn ls vl (Fmla (remove_ite_f true f))
              end
          | ld -> acc,ld
        in
        let axs,l = (map_fold_left fn [] l) in
        (create_logic_decl l)::axs
    | _ -> [decl_map (fun _ -> assert false) (remove_ite_f true) d]

let eliminate_ite = Register.store (fun () -> Trans.decl remove_ite_decl None)

let () = Register.register_transform "eliminate_ite" eliminate_ite

(* eliminate if_then_else *)

let rec remove_if_then_else_t t = 
  t_map remove_if_then_else_t remove_if_then_else_f t

and remove_if_then_else_f f =
  match f.f_node with
    | Fif (f1,f2,f3) -> f_and (f_implies f1 f2) (f_implies (f_not f1) f3)
    | _ -> f_map remove_if_then_else_t remove_if_then_else_f f

let eliminate_if_then_else =
  Register.store (fun () -> Trans.rewrite remove_if_then_else_t 
                    remove_if_then_else_f None)

let () = Register.register_transform
  "eliminate_if_then_else" eliminate_if_then_else
