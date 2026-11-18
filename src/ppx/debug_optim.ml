(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2026 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(********************************************************************)

open Parsetree
open Ast_mapper
open Asttypes
open Longident

let is_debug_dprintf txt =
  try Longident.flatten txt = ["Debug"; "dprintf"]
  with Misc.Fatal_error -> false

let debug_test_flag =
  match Longident.unflatten ["Debug"; "test_flag"] with
  | Some txt -> txt
  | None -> assert false

let ast_mapper =
  { Ast_mapper.default_mapper with
    expr = fun mapper expr ->
      match expr with
      | { pexp_desc =
          Pexp_apply ({ pexp_desc =
                        Pexp_ident { txt = Ldot (Lident "Debug", "dprintf")}},
                      ((flag :: _) as args))
                      ;
                      pexp_loc = loc } ->
        Some
         (Exp.pexp_ifthenelse ~loc
           (Exp.pexp_apply ~loc (test_flag ~loc) [flag])
           (Exp.pexp_apply ~loc (debug_no_expansion ~loc) args)
           None)
      | _other -> None)

let () =
  Ppxlib.Driver.register_transformation "Debug hook"
    ~rules:[expand_dprintf]
