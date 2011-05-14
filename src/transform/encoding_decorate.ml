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
open Ty
open Term
open Decl
open Libencoding

(* From Encoding Polymorphism CADE07*)

(* polymorphic decoration function *)
let ls_poly_deco =
  let tyvar = ty_var (create_tvsymbol (id_fresh "a")) in
  create_fsymbol (id_fresh "sort") [ty_type;tyvar] tyvar

let rec deco_arg kept tvar t =
  let t = deco_term kept tvar t in
  if Sty.mem (t_type t) kept then t else
  let tty = term_of_ty tvar (t_type t) in
  e_app ls_poly_deco [tty;t] t.t_ty

and deco_term kept tvar t = match t.t_node with
  | Tapp (fs,tl) -> e_app fs (List.map (deco_arg kept tvar) tl) t.t_ty
  | _ -> t_map (deco_term kept tvar) (deco_fmla kept tvar) t

and deco_fmla kept tvar f = match f.f_node with
  | Fapp (ps,tl) -> f_app ps (List.map (deco_arg kept tvar) tl)
  | Fquant (q,b) ->
      let vl,tl,f,close = f_open_quant_cb b in
      let tl = tr_map (deco_arg kept tvar) (deco_fmla kept tvar) tl in
      f_quant q (close vl tl (deco_fmla kept tvar f))
  | _ -> f_map (deco_term kept tvar) (deco_fmla kept tvar) f

let deco_decl kept d = match d.d_node with
  | Dtype tdl ->
      d :: lsdecl_of_tydecl tdl
  | Dlogic ldl ->
      let check = function
        | _, Some _ -> Printer.unsupportedDecl d "eliminate definitions"
        | _ -> ()
      in
      List.iter check ldl;
      [d]
  | Dind _ -> Printer.unsupportedDecl d "eliminate inductives"
  | Dprop (k,pr,f) ->
      let f = f_type_close (deco_fmla kept) f in
      [create_prop_decl k pr f]

let d_poly_deco = create_logic_decl [ls_poly_deco, None]

let deco_init =
  let init = Task.add_decl None d_ts_type in
  let init = Task.add_decl init d_poly_deco in
  init

let deco kept = Trans.decl (deco_decl kept) deco_init

(** Monomorphisation *)

let ts_base = create_tysymbol (id_fresh "uni") [] None
let ty_base = ty_app ts_base []

let ts_deco = create_tysymbol (id_fresh "deco") [] None
let ty_deco = ty_app ts_deco []
let ls_deco = create_fsymbol (id_fresh "sort") [ty_type;ty_base] ty_deco

(* monomorphise a logical symbol *)
let lsmap kept = Wls.memoize 63 (fun ls ->
  if ls_equal ls ls_poly_deco then ls_deco else
  let neg ty = if Sty.mem ty kept then ty else ty_deco in
  let pos ty = if Sty.mem ty kept then ty else ty_base in
  let tyl = List.map neg ls.ls_args in
  let tyr = Util.option_map pos ls.ls_value in
  if Util.option_eq ty_equal tyr ls.ls_value
     && List.for_all2 ty_equal tyl ls.ls_args then ls
  else create_lsymbol (id_clone ls.ls_name) tyl tyr)

let d_ts_base = create_ty_decl [ts_base, Tabstract]
let d_ts_deco = create_ty_decl [ts_deco, Tabstract]

let mono_init =
  let init = Task.add_decl None d_ts_base in
  let init = Task.add_decl init d_ts_deco in
  init

let mono kept =
  Trans.decl (d_monomorph ty_base kept (lsmap kept)) mono_init

let t = Trans.on_tagged_ty Encoding.meta_kept (fun kept ->
  let kept = Sty.add ty_type kept in
  Trans.compose (deco kept) (mono kept))

let () = Hashtbl.replace Encoding.ft_enco_poly "decorate" (const t)

