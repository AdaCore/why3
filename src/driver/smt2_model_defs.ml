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

open Stdlib

type variable = string

type float_type =
  | Plus_infinity
  | Minus_infinity
  | Plus_zero
  | Minus_zero
  | Not_a_number
  | Float_value of string * string * string

type array =
  | Const of term
  | Store of array * term * term

and term =
  | Integer of string
  | Decimal of (string * string)
  | Fraction of (string * string)
  | Float of float_type
  | Other of string
  | Array of array
  | Bitvector of string
  | Boolean of bool
  | Cvc4_Variable of variable
  | Function_Local_Variable of variable
  | Variable of variable
  | Ite of term * term * term * term
  | Record of int * (term list)
  | Discr of int * (term list)
  | To_array of term

type definition =
  | Function of (variable * string option) list * term
  | Term of term
  | Noelement

(* Type returned by parsing of model.
   An hashtable that makes a correspondence between names (string) and
   associated definition (complex stuff) *)
type correspondence_table = (bool * definition) Mstr.t

let print_float fmt f =
  match f with
  | Plus_infinity -> Format.fprintf fmt "Plus_infinity"
  | Minus_infinity -> Format.fprintf fmt "Minus_infinity"
  | Plus_zero -> Format.fprintf fmt "Plus_zero"
  | Minus_zero -> Format.fprintf fmt "Minus_zero"
  | Not_a_number -> Format.fprintf fmt "NaN"
  | Float_value (b, eb, sb) -> Format.fprintf fmt "(%s, %s, %s)" b eb sb

let rec print_array fmt a =
  match a with
  | Const t -> Format.fprintf fmt "CONST : %a" print_term t
  | Store (a, t1, t2) ->
      Format.fprintf fmt "STORE : %a %a %a"
        print_array a print_term t1 print_term t2

(* Printing function for terms *)
and print_term fmt t =
  match t with
  | Integer s -> Format.fprintf fmt "Integer: %s" s
  | Decimal (s1, s2) -> Format.fprintf fmt "Decimal: %s . %s" s1 s2
  | Fraction (s1, s2) -> Format.fprintf fmt "Fraction: %s / %s" s1 s2
  | Float f -> Format.fprintf fmt "Float: %a" print_float f
  | Other s -> Format.fprintf fmt "Other: %s" s
  | Array a -> Format.fprintf fmt "Array: %a" print_array a
  | Bitvector bv -> Format.fprintf fmt "Bv: %s" bv
  | Boolean _b -> Format.fprintf fmt "Boolean"
  | Cvc4_Variable cvc -> Format.fprintf fmt "CVC4VAR: %s" cvc
  | Function_Local_Variable v -> Format.fprintf fmt "LOCAL: %s" v
  | Variable v -> Format.fprintf fmt "VAR: %s" v
  | Ite _ -> Format.fprintf fmt "ITE"
  | Record (n, l) -> Format.fprintf fmt "record_type: %d; list_fields: %a" n
        (fun fmt -> Pp.print_list (fun fmt () -> Format.fprintf fmt " ") print_term fmt) l
  | Discr (n, l) -> Format.fprintf fmt "record_type: %d; list_fields: %a" n
        (fun fmt -> Pp.print_list (fun fmt () -> Format.fprintf fmt " ") print_term fmt) l
  | To_array t -> Format.fprintf fmt "TO_array: %a@." print_term t

let print_def fmt d =
  match d with
  | Function (_vars, t) -> Format.fprintf fmt "FUNCTION : %a" print_term t
  | Term t -> Format.fprintf fmt "TERM : %a" print_term t
  | Noelement -> Format.fprintf fmt "NOELEMENT"

let add_element x (t: correspondence_table) b =
  match x with
  | None -> t
  | Some (key, value) ->
      Mstr.add key (b, value) t

exception Bad_local_variable

let rec make_local_array vars_lists a =
  match a with
  | Const t ->
    let t' = make_local vars_lists t in
    Const t'
  | Store (a, t1, t2) ->
    let a' = make_local_array vars_lists a in
    let t1' = make_local vars_lists t1 in
    let t2' = make_local vars_lists t2 in
    Store (a', t1', t2')

(* For a definition of function f, local variables being in vars_lists and the
   returned term being t, this function changes the term give an appropriate tag
   to variables that are actually local. *)
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
  | Integer _ | Decimal _ | Fraction _ | Float _ | Other _ -> t
  | Bitvector _ -> t
  | Cvc4_Variable _ -> raise Bad_local_variable
  | Boolean _ -> t
  | Function_Local_Variable _ -> raise Bad_local_variable
  | Record (n, l) -> Record (n, List.map (fun x -> make_local vars_lists x) l)
  | Discr (n, l) -> Discr (n, List.map (fun x -> make_local vars_lists x) l)
  | To_array t -> To_array (make_local vars_lists t)


let build_record_discr lgen =

  let rec build_records_with_discrs acc (l: term list) =
    match l,acc with
    | Record (n, t) :: tl, None ->
        build_records_with_discrs (Some (Record (n, t))) tl
    | Record (_n, _t) :: _tl, Some (Record (_n', _t')) ->
        assert (false)
    | Record (n, t) :: _tl, Some (Discr (n', t')) ->
        Record (n, (Discr (n', t')) :: t)
    | Discr (n, t) :: tl, None ->
        build_records_with_discrs (Some (Discr (n, t))) tl
    | Discr (n, t) :: _tl, Some (Record (n', t')) ->
        Record (n', (Discr (n, t) :: t'))
    | Discr (_n, _t) :: _tl, Some (Discr (_n', _t')) ->
        assert (false)
    | _a :: tl, _ -> build_records_with_discrs acc tl
    | [], Some b -> b
    | [], None -> List.hd lgen
  in

  build_records_with_discrs None lgen

let rec subst var value t =
  match t with
  | Integer _ | Decimal _ | Fraction _ | Float _
    | Other _ | Bitvector _ | Boolean _ ->
      t
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
     Record (n, List.map (fun t -> subst var value t) l)
 | Discr (n, l) ->
     Discr (n, List.map (fun t -> subst var value t) l)
 | To_array t -> To_array (subst var value t)


and subst_array var value a =
  match a with
  | Const t -> Const (subst var value t)
  | Store (a, t1, t2) ->
      let t1 = subst var value t1 in
      let t2 = subst var value t2 in
      let a = subst_array var value a in
      Store (a, t1, t2)

let substitute l t =
  List.fold_left (fun t (var, value) -> subst var value t) t l
