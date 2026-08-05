(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2025 --  Inria - CNRS - Paris-Saclay University  *)
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
                        Pexp_ident { txt; _ }},
                      flag :: _args) } as app ->
         if not (is_debug_dprintf txt) then
           default_mapper.expr mapper expr
         else
           let open Ast_helper in
           Exp.ifthenelse
             (Exp.apply
                (Exp.ident { txt = debug_test_flag; loc = Location.none (*TODO*) })
                [flag])
             app
             None
      | other -> default_mapper.expr mapper other; }

let () =
  Ppxlib.Driver.register_transformation_using_ocaml_current_ast "Debug hook"
    ~impl:(ast_mapper.structure ast_mapper)

let () =
  Ppxlib.Driver.run_as_ppx_rewriter ()
