(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
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

type constant_int = {
  constant_int_value: Number.int_constant;
  constant_int_verbatim: string
}

type constant_bv = {
  constant_bv_value : BigInt.t;
  constant_bv_length : int;
  constant_bv_verbatim : string;
}

type constant_real = {
  constant_real_value: Number.real_constant;
  constant_real_verbatim: string
}

type constant_frac = {
  constant_frac_num: constant_real;
  constant_frac_den: constant_real;
  constant_frac_verbatim: string
}

type constant_float_value =
  | Fplusinfinity
  | Fminusinfinity
  | Fpluszero
  | Fminuszero
  | Fnan
  | Fnumber of {
      constant_float_sign : constant_bv;
      constant_float_exp : constant_bv;
      constant_float_mant : constant_bv
    }

type constant_float = {
  const_float_exp_size : int;
  const_float_significand_size : int;
  const_float_val : constant_float_value
}

type constant =
  | Cint of constant_int
  | Creal of constant_real
  | Cfraction of constant_frac
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
  | Tasarray of term
  | Tlet of var_binding list * term
  | Tforall of var_signature list * term
  | Tunparsed of string

and var_binding = symbol * term
and var_signature = symbol * sort
and array_elements = { array_indices : (term * term) list; array_others : term }

type function_def = var_signature list * sort * term

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

let print_bigint fmt bigint = pp_print_string fmt (BigInt.to_string bigint)

let print_bv fmt { constant_bv_value; constant_bv_length; constant_bv_verbatim } =
  fprintf fmt "(Cbitvector {value=%a; length=%d; verbatim=%s})"
    print_bigint constant_bv_value constant_bv_length constant_bv_verbatim

let print_real fmt { constant_real_value; constant_real_verbatim } =
  fprintf fmt "(Creal {value=%a; verbatim=%s})"
    Number.(print_real_constant full_support) constant_real_value constant_real_verbatim

let print_float_constant fmt = function
  | Fplusinfinity -> pp_print_string fmt "Fplusinfinity"
  | Fminusinfinity -> pp_print_string fmt "Fminusinfinity"
  | Fpluszero -> pp_print_string fmt "Fpluszero"
  | Fminuszero -> pp_print_string fmt "Fminuszero"
  | Fnan -> pp_print_string fmt "Fnan"
  | Fnumber { constant_float_sign; constant_float_exp; constant_float_mant } ->
    fprintf fmt "Fnumber {sign=%a; exp=%a; mant=%a}"
      print_bv constant_float_sign
      print_bv constant_float_exp
      print_bv constant_float_mant

let print_constant fmt = function
  | Cint {constant_int_value; constant_int_verbatim} ->
    fprintf fmt "(Cint {value=%a; verbatim=%s)"
      Number.(print_int_constant full_support) constant_int_value constant_int_verbatim
  | Creal r -> print_real fmt r
  | Cfraction {constant_frac_num; constant_frac_den; constant_frac_verbatim} ->
      fprintf fmt "(Cfraction {num=%a; den=%a; verbatim=%s})"
        print_real constant_frac_num print_real constant_frac_den constant_frac_verbatim
  | Cbitvector bv -> print_bv fmt bv
  | Cfloat
      { const_float_exp_size; const_float_significand_size; const_float_val} ->
    fprintf fmt
      "(Cfloat { @[<hov>exp_size = %d;@ significand_side = %d;@ value = %a@] })"
      const_float_exp_size
      const_float_significand_size
      print_float_constant const_float_val
  | Cbool b -> fprintf fmt "(Cbool %b)" b
  | Cstring s -> fprintf fmt "(Cstring %s)" s

let print_symbol fmt = function
  | S str -> pp_print_string fmt str
  | Sprover str -> fprintf fmt "(Sprover %s)" str

let print_index fmt = function
  | Idxnumeral bigint -> fprintf fmt "(Idx %a)" print_bigint bigint
  | Idxsymbol s -> fprintf fmt "(Idx %a)" print_symbol s

let rec print_sort fmt = function
  | Sstring -> pp_print_string fmt "(Sstring)"
  | Sreglan -> pp_print_string fmt "(Sreglan)"
  | Sint -> pp_print_string fmt "(Sint)"
  | Sreal -> pp_print_string fmt "(Sreal)"
  | Sroundingmode -> pp_print_string fmt "(Sroundingmode)"
  | Sbool -> pp_print_string fmt "(Sbool)"
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
  | Tasarray t ->
      fprintf fmt "@[<hv>(AsArray %a)@]" print_term t
  | Tlet (bindings, t) ->
      fprintf fmt "@[<hv>(Let (%a) %a)@]" (Pp.print_list Pp.comma print_var_binding) bindings print_term t
  | Tforall (bindings, t) ->
      fprintf fmt "@[<hv>(Forall (%a) %a)@]" (Pp.print_list Pp.comma print_var_signature) bindings print_term t
  | Tunparsed s -> fprintf fmt "(UNPARSED %s)" s

and print_var_binding fmt (s, t) =
  fprintf fmt "(%a %a)" print_symbol s print_term t

and print_var_signature fmt (s, t) =
  fprintf fmt "(%a %a)" print_symbol s print_sort t

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
