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

(** Discard definitions of built-in symbols *)

let add_id undef_ls rem_ls (ls,ld) (abst,defn) =
  if Sls.mem ls rem_ls then
    abst,defn
  else if Sls.mem ls undef_ls
  then create_param_decl ls :: abst, defn
  else abst, (ls,ld) :: defn

(** TODO: go further? such as constructor that are removed? *)

let elim undef_ls rem_pr rem_ls rem_ts d = match d.d_node with
  | Dlogic l ->
      let ld, id = List.fold_right (add_id undef_ls rem_ls) l ([],[]) in
      ld @ (if id = [] then [] else [create_logic_decl id])
  | Dind (s, l) ->
      let ld, id = List.fold_right (add_id undef_ls rem_ls) l ([],[]) in
      ld @ (if id = [] then [] else [create_ind_decl s id])
  | Dprop (Paxiom,pr,_) when Spr.mem pr rem_pr -> []
  | Dtype ts when Sts.mem ts rem_ts -> []
  | Ddata l ->
    let test_id (ts,_) = not (Sts.mem ts rem_ts) in
    let l = List.filter test_id l in
    (if l = [] then [] else [create_data_decl l])
  | _ -> [d]

let eliminate_builtin =
  Trans.on_tagged_ls Printer.meta_syntax_logic (fun undef_ls ->
  Trans.on_tagged_pr Printer.meta_remove_prop  (fun rem_pr ->
  Trans.on_tagged_ls Printer.meta_remove_logic  (fun rem_ls ->
  Trans.on_tagged_ts Printer.meta_remove_type_symbol  (fun rem_ts ->
    Trans.decl (elim undef_ls rem_pr rem_ls rem_ts) None))))

let () = Trans.register_transform "eliminate_builtin" eliminate_builtin
  ~desc_metas:[Printer.meta_syntax_logic,
               ("@ Remove@ their@ definitions@ since@ they@ are@ considered@ \
                 builtin."
                   : Pp.formatted);
               Printer.meta_remove_prop, Pp.empty_formatted]
  ~desc:"Eliminate@ facts@ which@ are@ builtin@ in@ the@ prover:@ symbol@ \
         definitions@ or@ axiomatics."

(** compute the meta_remove_* given two task one included in the other *)
let compute_diff t1 t2 =
  let km = Mid.set_diff (Task.task_known t1) (Task.task_known t2) in
  let hdone = Hdecl.create 10 in
  let remove_ts acc ts =
    (Printer.meta_remove_type_symbol, [Theory.MAts ts])::acc in
  let remove_ls acc ls =
    (Printer.meta_remove_logic, [Theory.MAls ls])::acc in
  let remove_pr acc pr =
    (Printer.meta_remove_prop, [Theory.MApr pr])::acc in
  Mid.fold_left (fun acc _ decl ->
    if Hdecl.mem hdone decl then acc
    else begin
      Hdecl.set hdone decl;
      match decl.d_node with
      | Dtype ts -> remove_ts acc ts
      | Ddata l -> List.fold_left (fun acc (ts,_) -> remove_ts acc ts) acc l
      | Dparam ls -> remove_ls acc ls
      | Dlogic l -> List.fold_left (fun acc (ls,_) -> remove_ls acc ls) acc l
      | Dind (_,l) -> List.fold_left (fun acc (ls,_) -> remove_ls acc ls) acc l
      | Dprop (_,pr,_) -> remove_pr acc pr
    end) [] km

let compute_diff =
  Trans.store (fun t1 -> Trans.store (fun t2 -> compute_diff t1 t2))

(** Eliminate definitions of functions and predicates *)

let rec t_insert hd t = match t.t_node with
  | Tif (f1,t2,t3) ->
      t_if f1 (t_insert hd t2) (t_insert hd t3)
  | Tlet (t1,bt) ->
      let v,t2 = t_open_bound bt in
      t_let_close v t1 (t_insert hd t2)
  | Tcase (tl,bl) ->
      let br b =
        let pl,t1 = t_open_branch b in
        t_close_branch pl (t_insert hd t1)
      in
      t_case tl (List.map br bl)
  | _ -> TermTF.t_selecti t_equ_simp t_iff_simp hd t

let add_ld func pred (ls,ld) (abst,defn,axl) =
  if (if ls.ls_value = None then pred else func) then
    let vl,e = open_ls_defn ld in
    let nm = ls.ls_name.id_string ^ "_def" in
    let pr = create_prsymbol (id_derive nm ls.ls_name) in
    let hd = t_app ls (List.map t_var vl) e.t_ty in
    let ax = t_forall_close vl [] (t_insert hd e) in
    let ax = create_prop_decl Paxiom pr ax in
    let ld = create_param_decl ls in
    ld :: abst, defn, ax :: axl
  else
    abst, (ls,ld) :: defn, axl

let elim_decl func pred l =
  let abst,defn,axl = List.fold_right (add_ld func pred) l ([],[],[]) in
  let defn = if defn = [] then [] else [create_logic_decl defn] in
  abst @ defn @ axl

let elim func pred d = match d.d_node with
  | Dlogic l -> elim_decl func pred l
  | _ -> [d]

let elim_recursion d = match d.d_node with
  | Dlogic ([s,_] as l)
    when Sid.mem s.ls_name d.d_syms -> elim_decl true true l
  | Dlogic l when List.length l > 1 -> elim_decl true true l
  | _ -> [d]

let is_struct dl = (* FIXME? Shouldn't 0 be allowed too? *)
  List.for_all (fun (_,ld) -> List.length (ls_defn_decrease ld) = 1) dl

(* FIXME? We can have non-recursive functions in a group *)
let elim_non_struct_recursion d = match d.d_node with
  | Dlogic ((s,_) :: _ as dl)
    when Sid.mem s.ls_name d.d_syms && not (is_struct dl) ->
      elim_decl true true dl
  | _ ->
      [d]

let elim_mutual d = match d.d_node with
  | Dlogic l when List.length l > 1 -> elim_decl true true l
  | _ -> [d]

let eliminate_definition_func  = Trans.decl (elim true false) None
let eliminate_definition_pred  = Trans.decl (elim false true) None
let eliminate_definition       = Trans.decl (elim true true) None
let eliminate_recursion        = Trans.decl elim_recursion None
let eliminate_non_struct_recursion = Trans.decl elim_non_struct_recursion None
let eliminate_mutual_recursion = Trans.decl elim_mutual None

let () =
  Trans.register_transform "eliminate_definition_func"
    eliminate_definition_func
    ~desc:"Transform@ function@ definition@ into@ axioms.";
  Trans.register_transform "eliminate_definition_pred"
    eliminate_definition_pred
    ~desc:"Transform@ predicate@ definition@ into@ axioms.";
  Trans.register_transform "eliminate_definition"
    eliminate_definition
    ~desc:"Same@ as@ eliminate_definition_func/_pred@ at@ the@ same@ time.";
  Trans.register_transform "eliminate_recursion"
    eliminate_recursion
    ~desc:"Same@ as@ eliminate_definition@ ,but@ only@ for@ recursive@ \
           definition";
  Trans.register_transform "eliminate_non_struct_recursion"
    eliminate_non_struct_recursion
    ~desc:"Same@ as@ eliminate_recursion@ ,but@ only@ for@ non@ structural@ \
           recursive@ definition";
  Trans.register_transform "eliminate_mutual_recursion"
    eliminate_mutual_recursion
    ~desc:"Same@ as@ eliminate_recursion@ ,but@ only@ for@ mutual@ \
           recursive@ definition (at@ least@ two@ functions@ or@ \
           predicates@ defined@ at@ the@ same@ time)";

