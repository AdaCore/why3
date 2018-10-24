(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)


open Wstdlib

type variable = string

(* Simple counterexample that already represent a complete value *)
type simple_value =
  | Integer of string
  | Decimal of (string * string)
  | Fraction of (string * string)
  | Float of Model_parser.float_type
  | Other of string
  | Bitvector of string
  | Boolean of bool

type array =
  | Array_var of variable
  | Const of term
  | Store of array * term * term

and term =
  | Sval of simple_value
  | Apply of (string * term list)
  | Array of array
  | Cvc4_Variable of variable
  | Function_Local_Variable of variable
  | Variable of variable
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
  | Array_var v ->
    Array_var v
  | Const t ->
    let t' = make_local vars_lists t in
    Const t'
  | Store (a, t1, t2) ->
    let a' = make_local_array vars_lists a in
    let t1' = make_local vars_lists t1 in
    let t2' = make_local vars_lists t2 in
    Store (a', t1', t2')

(* For a definition of function f, local variables being in vars_lists and the
   returned term being t, this function changes the term to give an appropriate
   tag to variables that are actually local. *)
and make_local vars_lists t =
  match t with
  | Variable s ->
      begin
        if (List.exists (fun x -> s = fst x) vars_lists) then
          Function_Local_Variable s
        else
          try
          (* Check that s is a Cvc4 or z3 variable. Note that s is a variable
             name so it is of size > 0 *)
            (if (String.get s 0 = '@' || String.contains s '!') then
              Cvc4_Variable s
            else
              Variable s
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
  | Cvc4_Variable _ -> raise Bad_local_variable
  | Function_Local_Variable _ -> raise Bad_local_variable
  | Record (n, l) -> Record (n, List.map (fun (f, x) -> f, make_local vars_lists x) l)
  | To_array t -> To_array (make_local vars_lists t)
  (* TODO tree does not exist yet *)
  | Trees t -> Trees t

let rec subst var value t =
  match t with
  | Sval v -> Sval v
  | Array a -> Array (subst_array var value a)
  | Cvc4_Variable _ -> raise Bad_local_variable
  | Function_Local_Variable _ -> t
  | Variable v -> if v = var then value else Variable v
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
 (* Tree does not exists yet *)
 | Trees t -> Trees t

and subst_array var value a =
  match a with
  | Array_var v ->
    if v = var then
      match value with
      | Array a -> a
      | _ -> Array_var v
    else
      Array_var v
  | Const t -> Const (subst var value t)
  | Store (a, t1, t2) ->
      let t1 = subst var value t1 in
      let t2 = subst var value t2 in
      let a = subst_array var value a in
      Store (a, t1, t2)

let substitute l t =
  List.fold_left (fun t (var, value) -> subst var value t) t l
