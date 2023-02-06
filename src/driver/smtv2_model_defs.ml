(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2022 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

type symbol = S of string | Sprover of string
type index = Idxnumeral of BigInt.t | Idxsymbol of symbol
type identifier = Isymbol of symbol | Iindexedsymbol of symbol * index list

type sort =
  | Sstring
  | Sreglan
  | Sint
  | Sreal
  | Sroundingmode
  | Sbool
  | Sbitvec of int
  | Sfloatingpoint of int * int
  | Sarray of sort * sort
  | Ssimple of identifier
  | Smultiple of identifier * sort list

type constant_bv = {
  bv_value : BigInt.t;
  bv_length : int;
  bv_verbatim : string;
}

type constant_real = {
  real_neg : bool; (* true for negative real numbers *)
  real_int : string;
  real_frac : string;
}

type constant_float =
  | Fplusinfinity
  | Fminusinfinity
  | Fpluszero
  | Fminuszero
  | Fnan
  | Fnumber of { sign : constant_bv; exp : constant_bv; mant : constant_bv }

type constant =
  | Cint of BigInt.t
  | Cdecimal of constant_real
  | Cfraction of constant_real * constant_real
  | Cbitvector of constant_bv
  | Cfloat of constant_float
  | Cbool of bool
  | Cstring of string

type qual_identifier = Qident of identifier | Qannotident of identifier * sort

type term =
  | Tconst of constant
  | Tvar of qual_identifier
  | Tapply of qual_identifier * term list
  | Tite of term * term * term
  | Tarray of sort * sort * array_elements
  | Tunparsed of string

and var_binding = symbol * term
and array_elements = { array_indices : (term * term) list; array_others : term }

type function_def = (symbol * sort) list * sort * term

let rec sort_equal s s' =
  match (s, s') with
  | Sstring, Sstring
  | Sreglan, Sreglan
  | Sint, Sint
  | Sreal, Sreal
  | Sroundingmode, Sroundingmode
  | Sbool, Sbool ->
      true
  | Sbitvec n, Sbitvec n' -> n = n'
  | Sfloatingpoint (n1, n2), Sfloatingpoint (n1', n2') -> n1 = n1' && n2 = n2'
  | Sarray (s1, s2), Sarray (s1', s2') -> sort_equal s1 s1' && sort_equal s2 s2'
  | Ssimple id, Ssimple id' -> id_equal id id'
  | Smultiple (id, sorts), Smultiple (id', sorts') -> (
      try
        id_equal id id'
        && List.fold_left2
             (fun acc x x' -> acc && sort_equal x x')
             true sorts sorts'
      with _ -> false)
  | _ -> false

and id_equal id id' =
  match (id, id') with
  | Isymbol (S s), Isymbol (S s') | Isymbol (Sprover s), Isymbol (Sprover s') ->
      String.equal s s'
  | Iindexedsymbol (S s, idx), Iindexedsymbol (S s', idx')
  | Iindexedsymbol (Sprover s, idx), Iindexedsymbol (Sprover s', idx') -> (
      try
        String.equal s s'
        && List.fold_left2 (fun acc x x' -> acc && idx_equal x x') true idx idx'
      with _ -> false)
  | _ -> false

and idx_equal idx idx' =
  match (idx, idx') with
  | Idxnumeral i, Idxnumeral i' -> BigInt.eq i i'
  | Idxsymbol (S s), Idxsymbol (S s')
  | Idxsymbol (Sprover s), Idxsymbol (Sprover s') ->
      String.equal s s'
  | _ -> false

open Format

let print_bigint fmt bigint = fprintf fmt "%s" (BigInt.to_string bigint)

let print_bv fmt { bv_value = bigint; bv_length = i; _ } =
  fprintf fmt "(Cbitvector (%d) %a)" i print_bigint bigint

let print_real fmt { real_neg = sign; real_int = s1; real_frac = s2 } =
  let sign = if sign then "+" else "-" in
  fprintf fmt "(%s %s.%s)" sign s1 s2

let print_constant fmt = function
  | Cint bigint -> fprintf fmt "(Cint %a)" print_bigint bigint
  | Cdecimal r -> fprintf fmt "(Cdecimal %a)" print_real r
  | Cfraction (r1, r2) ->
      fprintf fmt "(Cfraction %a / %a)" print_real r1 print_real r2
  | Cbitvector bv -> print_bv fmt bv
  | Cfloat Fplusinfinity -> fprintf fmt "(Cfloat Fplusinfinity)"
  | Cfloat Fminusinfinity -> fprintf fmt "(Cfloat Fminusinfinity)"
  | Cfloat Fpluszero -> fprintf fmt "(Cfloat Fpluszero)"
  | Cfloat Fminuszero -> fprintf fmt "(Cfloat Fminuszero)"
  | Cfloat Fnan -> fprintf fmt "(Cfloat Fnan)"
  | Cfloat (Fnumber { sign; exp; mant }) ->
      fprintf fmt "(Cfloat Fnumber {sign = %a; exp = %a; mant = %a})" print_bv
        sign print_bv exp print_bv mant
  | Cbool b -> fprintf fmt "(Cbool %b)" b
  | Cstring s -> fprintf fmt "(Cstring %s)" s

let print_symbol fmt = function
  | S str -> fprintf fmt "%s" str
  | Sprover str -> fprintf fmt "(Sprover %s)" str

let print_index fmt = function
  | Idxnumeral bigint -> fprintf fmt "(Idx %a)" print_bigint bigint
  | Idxsymbol s -> fprintf fmt "(Idx %a)" print_symbol s

let rec print_sort fmt = function
  | Sstring -> fprintf fmt "(Sstring)"
  | Sreglan -> fprintf fmt "(Sreglan)"
  | Sint -> fprintf fmt "(Sint)"
  | Sreal -> fprintf fmt "(Sreal)"
  | Sroundingmode -> fprintf fmt "(Sroundingmode)"
  | Sbool -> fprintf fmt "(Sbool)"
  | Sbitvec i -> fprintf fmt "(Sbitvec %d)" i
  | Sfloatingpoint (i1, i2) -> fprintf fmt "(Sfloatingpoint %d,%d)" i1 i2
  | Sarray (s1, s2) -> fprintf fmt "(Sarray %a %a)" print_sort s1 print_sort s2
  | Ssimple id -> fprintf fmt "(Ssimple %a)" print_identifier id
  | Smultiple (id, sorts) ->
      fprintf fmt "(Smultiple %a %a)" print_identifier id
        Pp.(print_list space print_sort)
        sorts

and print_identifier fmt = function
  | Isymbol n -> fprintf fmt "(Isymbol %a)" print_symbol n
  | Iindexedsymbol (n, idx) ->
      fprintf fmt "(Iindexedsymbol %a %a)" print_symbol n
        Pp.(print_list space print_index)
        idx

let print_qualified_identifier fmt = function
  | Qident id -> fprintf fmt "(Qident %a)" print_identifier id
  | Qannotident (id, s) ->
      fprintf fmt "(Qannotident %a %a)" print_identifier id print_sort s

let rec print_term fmt = function
  | Tconst c -> print_constant fmt c
  | Tvar v -> fprintf fmt "(Var %a)" print_qualified_identifier v
  | Tapply (qid, ts) ->
      fprintf fmt "@[<hv2>(Apply %a %a)@]" print_qualified_identifier qid
        Pp.(print_list space print_term)
        ts
  | Tite (b, t1, t2) ->
      fprintf fmt "@[<hv2>(Ite@ %a@ %a@ %a)@]" print_term b print_term t1
        print_term t2
  | Tarray (s1, s2, elts) ->
      fprintf fmt "@[<hv>(Array (%a -> %a) %a)@]" print_sort s1 print_sort s2
        print_array elts
  | Tunparsed s -> fprintf fmt "(UNPARSED %s)" s

and print_var_binding fmt (s, t) =
  fprintf fmt "(%a %a)" print_symbol s print_term t

and print_array_elem fmt (t1, t2) =
  fprintf fmt "@[<hv>(%a -> %a)@]" print_term t1 print_term t2

and print_array fmt a =
  fprintf fmt "@[<hv2>(array_indices = (%a);@ array_others = %a)@]"
    (Pp.print_list Pp.space print_array_elem)
    a.array_indices print_term a.array_others

let print_function_arg fmt (n, s) =
  fprintf fmt "(%a %a)" print_symbol n print_sort s

let print_function_def fmt (args, res, body) =
  fprintf fmt "@[<hv2>(Function (%a)@ %a@ %a)@]"
    Pp.(print_list space print_function_arg)
    args print_sort res print_term body
