(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Francois Bobot, Jean-Christophe Filliatre,              *)
(*  Johannes Kanig and Andrei Paskevich.                                  *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Util
open Format
open Term

(** errors *)

type error = 
  | ClashType of string
  | BadTypeArity of string

exception Error of error

let error ?loc e = match loc with
  | None -> raise (Error e)
  | Some loc -> raise (Loc.Located (loc, Error e))

let report fmt = function
  | ClashType s ->
      fprintf fmt "clash with previous type %s" s
  | BadTypeArity s ->
      fprintf fmt "duplicate type parameter %s" s

module M = Map.Make(String)

type env = {
  tysymbols : tysymbol M.t;
  fsymbols  : fsymbol M.t;
  psymbols  : psymbol M.t;
  tyvars    : vsymbol M.t;
  vars      : vsymbol M.t;
}

let empty = {
  tysymbols = M.empty;
  fsymbols  = M.empty;
  psymbols  = M.empty;
  tyvars    = M.empty;
  vars      = M.empty;
}

let find_tysymbol s env = M.find s env.tysymbols
let find_fsymbol s env = M.find s env.fsymbols
let find_psymbol s env = M.find s env.psymbols
let find_tyvar s env = M.find s env.tyvars
let find_var s env = M.find s env.vars

(** typing *)

let term env t =
  assert false (*TODO*)

let fmla env f =
  assert false (*TODO*)

(** building environments *)

open Ptree

let add_type loc ext sl s env =
  if M.mem s env.tysymbols then error ~loc (ClashType s);
  let add_ty_var env x =
    if M.mem x env.tyvars then error ~loc (BadTypeArity x);
    let v = Name.from_string x in
    { env with tyvars = M.add x v env.tyvars}, v
  in
  let _, vl = map_fold_left add_ty_var env sl in
  let ty = Ty.create_tysymbol (Name.from_string s) vl None in
  { env with tysymbols = M.add s ty env.tysymbols }

let add env = function
  | TypeDecl (loc, ext, sl, s) ->
      add_type loc ext sl s env
  | _ ->
      assert false (*TODO*)
