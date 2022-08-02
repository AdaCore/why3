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


open Wstdlib
open Model_parser

type symbol = string

type index =
  | Idxnumeral of BigInt.t
  | Idxsymbol of string

type identifier =
  | Isymbol of symbol
  | Iindexedsymbol of symbol * (index list)

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
  | Smultiple of identifier * (sort list)

type constant_bv = BigInt.t * int
type constant_float =
  | Fplusinfinity | Fminusinfinity
  | Fpluszero | Fminuszero
  | Fnan
  | Fnumber of {
      sign: constant_bv;
      exp: constant_bv;
      mant:constant_bv }

type constant =
  | Cint of BigInt.t
  | Cdecimal of (BigInt.t * BigInt.t)
  | Cfraction of (BigInt.t * BigInt.t)
  | Cbitvector of constant_bv
  | Cfloat of constant_float
  | Cbool of bool
  | Cstring of string

type qual_identifier =
  | Qident of identifier
  | Qannotident of identifier * sort

type term =
  | Tconst of constant
  | Tvar of qual_identifier
  | Tapply of qual_identifier * (term list)
  | Tite of term * term * term
  | Tlet of (var_binding list) * term
  | Tarray of array
  | Tunparsed of string

and var_binding = symbol * term

and array =
  | Avar of symbol
  | Aconst of sort * term
  | Astore of array * term * term

type function_def = (symbol * sort) list * sort * term
type datatype_decl = (sort * symbol list)

open Format

let print_bv fmt (bigint,i) =
  fprintf fmt "(Cbitvector (%d) %d)" i (BigInt.to_int bigint)
let print_constant fmt = function
  | Cint bigint ->
    fprintf fmt "(Cint %d)" (BigInt.to_int bigint)
  | Cdecimal (bigint1, bigint2) ->
    fprintf fmt "(Cdecimal %d , %d)" (BigInt.to_int bigint1) (BigInt.to_int bigint2)
  | Cfraction (bigint1, bigint2) ->
    fprintf fmt "(Cfraction %d / %d)" (BigInt.to_int bigint1) (BigInt.to_int bigint2)
  | Cbitvector (bigint, i) -> print_bv fmt (bigint,i)
  | Cfloat Fplusinfinity ->
    fprintf fmt "(Cfloat Fplusinfinity)"
  | Cfloat Fminusinfinity ->
    fprintf fmt "(Cfloat Fminusinfinity)"
  | Cfloat Fpluszero ->
    fprintf fmt "(Cfloat Fpluszero)"
  | Cfloat Fminuszero ->
    fprintf fmt "(Cfloat Fminuszero)"
  | Cfloat Fnan ->
    fprintf fmt "(Cfloat Fnan)"
  | Cfloat Fnumber { sign;exp;mant } ->
    fprintf fmt "(Cfloat Fnumber {sign = %a; exp = %a; mant = %a})"
      print_bv sign
      print_bv exp
      print_bv mant
  | Cbool b -> fprintf fmt "(Cbool %b)" b
  | Cstring s -> fprintf fmt "(Cstring %s)" s

let print_index fmt = function
  | Idxnumeral bigint -> fprintf fmt "(Idx %d)" (BigInt.to_int bigint)
  | Idxsymbol s -> fprintf fmt "(Idx %s)" s
let rec print_sort fmt = function
  | Sstring -> fprintf fmt "(Sstring)"
  | Sreglan -> fprintf fmt "(Sreglan)"
  | Sint -> fprintf fmt "(Sint)"
  | Sreal -> fprintf fmt "(Sreal)"
  | Sroundingmode -> fprintf fmt "(Sroundingmode)"
  | Sbool -> fprintf fmt "(Sbool)"
  | Sbitvec i -> fprintf fmt "(Sbitvec %d)" i
  | Sfloatingpoint (i1,i2) -> fprintf fmt "(Sfloatingpoint %d,%d)" i1 i2
  | Sarray (s1,s2) ->
    fprintf fmt "(Sarray %a %a)" print_sort s1 print_sort s2
  | Ssimple id -> fprintf fmt "(Ssimple %a)" print_identifier id
  | Smultiple (id, sorts) ->
    fprintf fmt "(Smultiple %a %a)"
      print_identifier id
      Pp.(print_list space print_sort) sorts
and print_identifier fmt = function
  | Isymbol n -> fprintf fmt "(Isymbol %s)" n
  | Iindexedsymbol (n, idx) ->
    fprintf fmt "(Iindexedsymbol %s %a)"
      n Pp.(print_list space print_index) idx
let print_qualified_identifier fmt = function
  | Qident id -> fprintf fmt "(Qident %a)" print_identifier id
  | Qannotident (id,s) ->
    fprintf fmt "(Qannotident %a %a)"
      print_identifier id print_sort s

let rec print_term fmt = function
  | Tconst c -> print_constant fmt c
  | Tvar v -> fprintf fmt "(Var %a)" print_qualified_identifier v
  | Tapply (qid, ts) ->
      fprintf fmt "@[<hv2>(Apply %a %a)@]" print_qualified_identifier qid
        Pp.(print_list space print_term) ts
  | Tite (b, t1, t2) ->
      fprintf fmt "@[<hv2>(Ite@ %a@ %a@ %a)@]"
        print_term b print_term t1 print_term t2
  | Tlet (bs, t) ->
      fprintf fmt "(Let (%a) %a)"
        Pp.(print_list space print_var_binding) bs print_term t
  | Tarray a -> fprintf fmt "@[<hv>(Array %a)@]" print_array a
  | Tunparsed s -> fprintf fmt "(UNPARSED %s)" s
and print_var_binding fmt (s,t) = fprintf fmt "(%s %a)" s print_term t
and print_array fmt = function
  | Avar v -> fprintf fmt "@[<hv2>(Avar %s)@]" v
  | Aconst (s,t) ->
    fprintf fmt "@[<hv2>(Aconst %a %a)@]"
      print_sort s print_term t
  | Astore (a, t1, t2) ->
    fprintf fmt "@[<hv2>(Astore %a %a %a)@]"
      print_array a print_term t1 print_term t2

let print_function_arg fmt (n,s) =
  fprintf fmt "(%s %a)" n print_sort s

let print_function_def fmt (args, res, body) =
  fprintf fmt "@[<hv2>(Function (%a)@ %a@ %a)@]"
    Pp.(print_list space print_function_arg) args 
    print_sort res
    print_term body

let print_datatype_decl fmt (dt_sort, dt_symbols) =
  fprintf fmt "@[<hv2>(Datatype %a: %a)@]"
    print_sort dt_sort
    (Pp.print_list Pp.space Pp.string) dt_symbols