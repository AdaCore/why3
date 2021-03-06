(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)


open Wstdlib
open Model_parser

type ident = string

type typ = string

type term =
  | Sval of model_value
  | Var of ident
  | Prover_var of typ * ident
  | Apply of (string * term list)
  | Array of array
  | Ite of term * term * term
  | Let of (string * term) list * term
  (* | Record of string * ((ident * term) list) *)
  | To_array of term

and array =
  | Avar of ident (* Used by let-bindings only *)
  | Aconst of term
  | Astore of array * term * term

type definition =
  | Function of (ident * typ option) list * typ option * term
  | Term of term (* corresponding value of a term *)
  | Noelement

let add_element x (t: definition Mstr.t) =
  match x with
  | None -> t
  | Some (key, value) ->
      Mstr.add key value t

let rec subst var value = function
  | Sval _ as t -> t
  | Array a -> Array (subst_array var value a)
  | Var v | Prover_var (_, v) as t -> if v = var then value else t
  | Let (bs, t') as t ->
      if List.exists (fun (s,_) -> s = var) bs then t
      else Let (List.map (fun (s,t) -> s, subst var value t) bs, subst var value t')
  | Ite (t1, t2, t3) ->
    let t1 = subst var value t1 in
    let t2 = subst var value t2 in
    let t3 = subst var value t3 in
    Ite (t1, t2, t3)
  (* | Record (n, l) ->
   *   Record (n, List.map (fun (f, t) -> f, subst var value t) l) *)
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
  | Sval v -> print_model_value_human fmt v
  | Apply (s, lt) ->
      fprintf fmt "@[<hv2>(Apply %s %a)@]" s
        Pp.(print_list space print_term) lt
  | Array a -> fprintf fmt "@[<hv>(Array %a)@]" print_array a
  | Var v -> fprintf fmt "(Var %s)" v
  | Prover_var (ty,v) -> fprintf fmt "(Prover_var %s:%s)" v ty
  | Let (bs, t) ->
      let print_binding fmt (s,t) = fprintf fmt "(%s %a)" s print_term t in
      fprintf fmt "(Let (%a) %a)" Pp.(print_list space print_binding) bs print_term t
  | Ite (cond, tthen, telse) ->
      fprintf fmt "@[<hv2>(Ite@ %a@ %a@ %a)@]"
        print_term cond print_term tthen print_term telse
  (* | Record (n, l) ->
   *     fprintf fmt "@[<hv2>(Record %s %a)@]" n
   *       Pp.(print_list semi (fun fmt (x, a) -> fprintf fmt "(%s, %a)" x print_term a)) l *)
  | To_array t -> fprintf fmt "@[<hv2>(To_array %a)@]" print_term t

and print_array fmt = function
  | Avar v -> Format.fprintf fmt "@[<hv2>(Array_var %s)@]" v
  | Aconst t -> Format.fprintf fmt "@[<hv2>(Aconst %a)@]" print_term t
  | Astore (a, t1, t2) -> Format.fprintf fmt "@[<hv2>(Astore %a %a %a)@]"
                            print_array a print_term t1 print_term t2

and print_definition fmt =
  let open Format in function
    | Function (vars, iret, t) ->
        fprintf fmt "@[<hv2>(Function (%a)@ %a@ %a)@]" Pp.(print_list space string) (List.map fst vars)
          Pp.(print_option string) iret
          print_term t
    | Term t -> fprintf fmt "@[<hv2>(Term %a)@]" print_term t
    | Noelement -> fprintf fmt "Noelement"
