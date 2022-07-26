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

type definition =
  | Dfunction of (symbol * sort) list * sort * term
  | Dterm of term (* corresponding value of a term *) (* TODO_WIP unused ?*)
  | Dnoelement (* TODO_WIP unused ?*)