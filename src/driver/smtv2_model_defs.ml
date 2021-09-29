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
  | Tconst of model_const
  | Tvar of ident
  | Tprover_var of typ * ident
  | Tapply of (string * term list)
  | Tarray of array
  | Tite of term * term * term
  | Tlet of (string * term) list * term
  | Tto_array of term
  | Tunparsed of string

and array =
  | Avar of ident (* Used by let-bindings only *)
  | Aconst of term
  | Astore of array * term * term

type definition =
  | Dfunction of (ident * typ option) list * typ option * term
  | Dterm of term (* corresponding value of a term *)
  | Dnoelement

let add_element x (t: definition Mstr.t) =
  match x with
  | None -> t
  | Some (key, value) ->
      Mstr.add key value t

let rec subst var value = function
  | Tconst _ as t -> t
  | Tarray a -> Tarray (subst_array var value a)
  | Tvar v | Tprover_var (_, v) as t -> if v = var then value else t
  | Tlet (bs, t') as t ->
      if List.exists (fun (s,_) -> s = var) bs then t
      else Tlet (List.map (fun (s,t) -> s, subst var value t) bs, subst var value t')
  | Tite (t1, t2, t3) ->
    let t1 = subst var value t1 in
    let t2 = subst var value t2 in
    let t3 = subst var value t3 in
    Tite (t1, t2, t3)
  (* | Record (n, l) ->
   *   Record (n, List.map (fun (f, t) -> f, subst var value t) l) *)
  | Tto_array t -> Tto_array (subst var value t)
  | Tapply (s, lt) ->
    Tapply (s, List.map (subst var value) lt)
  | Tunparsed _ as t -> t

and subst_array var value = function
  | Avar v ->
    if v = var then
      match value with
      | Tarray a -> a
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
  | Tconst v -> print_model_const_human fmt v
  | Tapply (s, lt) ->
      fprintf fmt "@[<hv2>(Apply %s %a)@]" s
        Pp.(print_list space print_term) lt
  | Tarray a -> fprintf fmt "@[<hv>(Array %a)@]" print_array a
  | Tvar v -> fprintf fmt "(Var %s)" v
  | Tprover_var (ty,v) -> fprintf fmt "(Prover_var %s:%s)" v ty
  | Tlet (bs, t) ->
      let print_binding fmt (s,t) = fprintf fmt "(%s %a)" s print_term t in
      fprintf fmt "(Let (%a) %a)" Pp.(print_list space print_binding) bs print_term t
  | Tite (cond, tthen, telse) ->
      fprintf fmt "@[<hv2>(Ite@ %a@ %a@ %a)@]"
        print_term cond print_term tthen print_term telse
  (* | Record (n, l) ->
   *     fprintf fmt "@[<hv2>(Record %s %a)@]" n
   *       Pp.(print_list semi (fun fmt (x, a) -> fprintf fmt "(%s, %a)" x print_term a)) l *)
  | Tto_array t -> fprintf fmt "@[<hv2>(To_array %a)@]" print_term t
  | Tunparsed s -> fprintf fmt "(UNPARSED %s)" s

and print_array fmt = function
  | Avar v -> Format.fprintf fmt "@[<hv2>(Array_var %s)@]" v
  | Aconst t -> Format.fprintf fmt "@[<hv2>(Aconst %a)@]" print_term t
  | Astore (a, t1, t2) -> Format.fprintf fmt "@[<hv2>(Astore %a %a %a)@]"
                            print_array a print_term t1 print_term t2

and print_definition fmt =
  let open Format in function
    | Dfunction (vars, iret, t) ->
        fprintf fmt "@[<hv2>(Function (%a)@ %a@ %a)@]"
          Pp.(print_list (constant_string " ") string) (List.map fst vars)
          Pp.(print_option string) iret
          print_term t
    | Dterm t -> fprintf fmt "@[<hv2>(Term %a)@]" print_term t
    | Dnoelement -> pp_print_string fmt "Noelement"
