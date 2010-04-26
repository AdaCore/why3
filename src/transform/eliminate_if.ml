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

(* eliminate if-then-else in terms *)

let rec elim_t letl contT t = match t.t_node with
  | Tlet (t1,tb) ->
      let u,t2 = t_open_bound tb in
      let t_let e1 e2 =
        if e1 == t1 && e2 == t2 then t else t_let u e1 e2
      in
      let cont_in t1 t2 = contT (t_let t1 t2) in
      let cont_let t1 = elim_t ((u,t1)::letl) (cont_in t1) t2 in
      elim_t letl cont_let t1
  | Tif (f,t1,t2) ->
      let f = elim_f (fun f -> f) f in
      let f = List.fold_left (fun f (v,t) -> f_let v t f) f letl in
      f_if f (elim_t letl contT t1) (elim_t letl contT t2)
  | Tcase _ ->
      Register.unsupportedExpression (Term t)
        "cannot eliminate 'if-then-else' under 'match' in terms"
  | _ ->
      t_map_cont (elim_t letl) elim_f contT t

and elim_f contF f = match f.f_node with
  | Fapp _ | Flet _ | Fcase _ ->
      contF (f_map_cont (elim_t []) elim_f (fun f -> f) f)
  | _ -> f_map_cont elim_tr elim_f contF f

(* the only terms we can still meet are the terms in triggers *)
and elim_tr contT t = match t.t_node with
  | Tif _ ->
      Register.unsupportedExpression (Term t)
        "cannot eliminate 'if-then-else' in trigger terms"
  | _ -> t_map_cont elim_tr elim_f contT t

let elim_f f = elim_f (fun f -> f) f

let rec elim_t t = t_map elim_t elim_f t

let rec has_if t = match t.t_node with
  | Tif _ -> true
  | _ -> t_any has_if ffalse t

let add_ld axl d = match d with
  | _, None -> axl, d
  | ls, Some ld ->
      let vl,e = open_ls_defn ld in
      begin match e with
        | Term t when has_if t ->
            let f = elim_f (ls_defn_axiom ld) in
            let nm = ls.ls_name.id_short ^ "_def" in
            let pr = create_prsymbol (id_derive nm ls.ls_name) in
            create_prop_decl Paxiom pr f :: axl, (ls, None)
        | _ ->
            axl, make_ls_defn ls vl (e_map elim_t elim_f e)
      end

let elim_d d = match d.d_node with
  | Dlogic l ->
      let axl, l = map_fold_left add_ld [] l in
      let d = create_logic_decl l in
      d :: List.rev axl
  | _ ->
      [decl_map (fun _ -> assert false) elim_f d]

(* eliminate if-then-else in formulas *)

let rec elim_t t = t_map elim_t (elim_f true) t

and elim_f sign f = match f.f_node with
  | Fif (f1,f2,f3) ->
      let f1p = elim_f sign f1 in
      let f1n = elim_f (not sign) f1 in
      let f2 = elim_f sign f2 in
      let f3 = elim_f sign f3 in
      if sign then f_and (f_implies f1n f2) (f_or f1p f3)
              else f_or (f_and f1p f2) (f_and (f_not f1n) f3)
  | _ ->
      f_map_sign elim_t elim_f sign f

(* registration *)

let eliminate_if_term =
  Register.store (fun () -> Trans.decl elim_d None)

let eliminate_if_fmla =
  Register.store (fun () -> Trans.rewrite elim_t (elim_f true) None)

let eliminate_if =
  Register.compose eliminate_if_term eliminate_if_fmla

let () =
  Register.register_transform "eliminate_if_term" eliminate_if_term;
  Register.register_transform "eliminate_if_fmla" eliminate_if_fmla;
  Register.register_transform "eliminate_if" eliminate_if

