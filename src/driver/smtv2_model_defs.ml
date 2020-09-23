(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)


open Wstdlib
open Model_parser

type variable = string

type array =
  | Avar of variable
  | Aconst of term
  | Astore of array * term * term

and term =
  | Sval of model_value
  | Apply of (string * term list)
  | Array of array
  | Var of variable
  | Function_var of variable
  | Prover_var of variable
  | Ite of term * term * term * term
  | Record of string * ((string * term) list)
  | To_array of term
  (* TODO remove tree *)
  | Trees of (string * term) list

type definition =
  | Function of (variable * string option) list * term
  | Term of term
  | Noelement

let add_element x (t: definition Mstr.t) =
  match x with
  | None -> t
  | Some (key, value) ->
      Mstr.add key value t

exception Bad_local_variable

let rec make_local_array vars_lists a =
  match a with
  | Avar v ->
      Avar v
  | Aconst t ->
      Aconst (make_local vars_lists t)
  | Astore (a, t1, t2) ->
      let a' = make_local_array vars_lists a in
      let t1' = make_local vars_lists t1 in
      let t2' = make_local vars_lists t2 in
      Astore (a', t1', t2')

and make_local vars_lists t =
  match t with
  | Var s ->
      begin
        if (List.exists (fun x -> s = fst x) vars_lists) then
          Function_var s
        else
          try
          (* Check that s is a Cvc4 or z3 variable. Note that s is a variable
             name so it is of size > 0 *)
            (if (String.get s 0 = '@' || String.contains s '!') then
              Prover_var s
            else
              Var s
            ) (* should not happen *)
          with
            _ -> raise Bad_local_variable (* Should not happen. s = "" *)
      end
  | Array a ->
    begin
      Array (make_local_array vars_lists a)
    end
  | Ite (t1, t2, t3, t4) ->
    let t1 = make_local vars_lists t1 in
    let t2 = make_local vars_lists t2 in
    let t3 = make_local vars_lists t3 in
    let t4 = make_local vars_lists t4 in
    Ite (t1, t2, t3, t4)
  | Apply (s, lt) ->
    let lt = List.map (make_local vars_lists) lt in
    Apply (s, lt)
  | Sval v -> Sval v
  | Prover_var _ -> raise Bad_local_variable
  | Function_var _ -> raise Bad_local_variable
  | Record (n, l) -> Record (n, List.map (fun (f, x) -> f, make_local vars_lists x) l)
  | To_array t -> To_array (make_local vars_lists t)
  (* TODO tree does not exist yet *)
  | Trees t -> Trees t

let rec subst var value = function
  | Sval _ as t -> t
  | Array a -> Array (subst_array var value a)
  | Var v as t -> if v = var then value else t
  | Prover_var _ -> raise Bad_local_variable
  | Function_var _ as t -> t
  | Ite (t1, t2, t3, t4) ->
    let t1 = subst var value t1 in
    let t2 = subst var value t2 in
    let t3 = subst var value t3 in
    let t4 = subst var value t4 in
    Ite (t1, t2, t3, t4)
  | Record (n, l) ->
    Record (n, List.map (fun (f, t) -> f, subst var value t) l)
  | To_array t -> To_array (subst var value t)
  | Apply (s, lt) ->
    Apply (s, List.map (subst var value) lt)
  | Trees _ as t -> t (* Tree does not exists yet *)

and subst_array var value = function
  | Avar v ->
    if v = var then
      match value with
      | Array a -> a
      | _ -> Avar v
    else
      Avar v
  | Aconst t -> Aconst (subst var value t)
  | Astore (a, t1, t2) ->
      let t1 = subst var value t1 in
      let t2 = subst var value t2 in
      let a = subst_array var value a in
      Astore (a, t1, t2)

let substitute l t =
  List.fold_left (fun t (var, value) -> subst var value t) t l
