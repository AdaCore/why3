(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
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

(** Eliminate if-then-else in terms *)

let rec has_if t = match t.t_node with
  | Tif _ -> true
  | _ -> t_any has_if ffalse t

let rec elim_t contT t =
  let contTl e = contT (t_label_copy t e) in
  match t.t_node with
  | Tlet (t1,tb) ->
      let u,t2,close = t_open_bound_cb tb in
      let cont_in t1 t2 = contTl (t_let t1 (close u t2)) in
      let cont_let_t t1 = elim_t (cont_in t1) t2 in
      let cont_let_f t1 = f_let_close u t1 (elim_t contT t2) in
      elim_t (if has_if t2 then cont_let_f else cont_let_t) t1
  | Tif (f,t1,t2) ->
      let f = elim_f (fun f -> f) f in
      f_if f (elim_t contT t1) (elim_t contT t2)
  | Tcase (t1, bl) ->
      let bl = List.rev_map t_open_branch_cb bl in
      let fi = List.exists (fun (_,t,_) -> has_if t) bl in
      let fnB ctB (p,t,cl) = elim_t (fun t -> ctB (cl p t)) t in
      let cont_with t1 bl = contTl (t_case t1 (List.rev bl)) in
      let cont_case_t t1 = list_map_cont fnB (cont_with t1) bl in
      let close (p,t,_) = f_close_branch p (elim_t contT t) in
      let cont_case_f t1 = f_case t1 (List.rev_map close bl) in
      elim_t (if fi then cont_case_f else cont_case_t) t1
  | _ ->
      t_map_cont elim_t elim_f contT t

and elim_f contF f = match f.t_node with
  | Tapp _ | Tlet _ | Tcase _ ->
      contF (f_map_cont elim_t elim_f (fun f -> f) f)
  | _ -> f_map_cont elim_tr elim_f contF f

(* the only terms we still can meet are the terms in triggers *)
and elim_tr contT t = match t.t_node with
  | Tif _ ->
      Printer.unsupportedTerm t
        "cannot eliminate 'if-then-else' in trigger terms"
  | _ -> t_map_cont elim_tr elim_f contT t

let elim_f f = elim_f (fun f -> f) f

let rec elim_t t = t_map elim_t elim_f t

let add_ld axl d = match d with
  | _, None -> axl, d
  | ls, Some ld ->
      let vl,e = open_ls_defn ld in
      begin match e with
        | Term t when has_if t ->
            let nm = ls.ls_name.id_string ^ "_def" in
            let pr = create_prsymbol (id_derive nm ls.ls_name) in
            let hd = e_app ls (List.map t_var vl) t.t_ty in
            let f = f_forall_close vl [] (elim_f (f_equ hd t)) in
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

let eliminate_if_term = Trans.decl elim_d None

(** Eliminate if-then-else in formulas *)

let rec elim_t t = t_map elim_t (elim_f true) t

and elim_f sign f = match f.t_node with
  | Tif (f1,f2,f3) ->
      let f1p = elim_f sign f1 in
      let f1n = elim_f (not sign) f1 in
      let f2 = elim_f sign f2 in
      let f3 = elim_f sign f3 in
      if sign then f_and (f_implies f1n f2) (f_implies (f_not f1p) f3)
              else f_or (f_and f1p f2) (f_and (f_not f1n) f3)
  | _ ->
      f_map_sign elim_t elim_f sign f

let eliminate_if_fmla = Trans.rewrite elim_t (elim_f true) None

let eliminate_if = Trans.compose eliminate_if_term eliminate_if_fmla

let () =
  Trans.register_transform "eliminate_if_term" eliminate_if_term;
  Trans.register_transform "eliminate_if_fmla" eliminate_if_fmla;
  Trans.register_transform "eliminate_if" eliminate_if

