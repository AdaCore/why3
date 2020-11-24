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
        if List.exists (fun x -> s = fst x) vars_lists then
          Function_var s
        else
          try
          (* Check that s is a Cvc4 or z3 variable. Note that s is a variable
             name so it is of size > 0 *)
            if String.get s 0 = '@' || String.contains s '!' then
              Prover_var s
            else
              Var s (* should not happen *)
          with _ -> raise Bad_local_variable (* Should not happen. s = "" *)
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


(************************************************************************)
(*                              Printing                                *)
(************************************************************************)

let rec print_term fmt = let open Format in function
  | Sval v -> print_model_value fmt v
  | Apply (s, lt) ->
      fprintf fmt "@[<hv2>(Apply %s %a)@]" s
        Pp.(print_list space print_term) lt
  | Array a -> fprintf fmt "@[<hv>(Array %a)@]" print_array a
  | Prover_var v -> fprintf fmt "(Provervar %s)" v
  | Function_var v -> fprintf fmt "(Funvar %s)" v
  | Var v -> fprintf fmt "(Var %s)" v
  | Ite (teq1, teq2, tthen, telse) ->
      fprintf fmt "@[<hv2>(Ite@ %a@ %a@ %a@ %a)@]"
        print_term teq1 print_term teq2 print_term tthen print_term telse
  | Record (n, l) ->
      fprintf fmt "@[<hv2>(Record %s %a)@]" n
        Pp.(print_list semi (fun fmt (x, a) -> fprintf fmt "(%s, %a)" x print_term a)) l
  | To_array t -> fprintf fmt "@[<hv2>(To_array %a)@]" print_term t

and print_array fmt = function
  | Avar v -> Format.fprintf fmt "@[<hv2>(Array_var %s)@]" v
  | Aconst t -> Format.fprintf fmt "@[<hv2>(Aconst %a)@]" print_term t
  | Astore (a, t1, t2) -> Format.fprintf fmt "@[<hv2>(Astore %a %a %a)@]"
                            print_array a print_term t1 print_term t2

and print_definition fmt =
  let open Format in function
    | Function (vars, t) ->
        fprintf fmt "@[<hv2>(Function %a@ %a)@]" Pp.(print_list space string) (List.map fst vars) print_term t
    | Term t -> fprintf fmt "@[<hv2>(Term %a)@]" print_term t
    | Noelement -> fprintf fmt "Noelement"
