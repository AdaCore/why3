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

open Parsetree
open Ast_mapper
open Asttypes
open Longident

let ast_mapper argv =
  { Ast_mapper.default_mapper with
    expr = fun mapper expr ->
      match expr with
      | { pexp_desc =
          Pexp_apply ({ pexp_desc =
                        Pexp_ident { txt = Ldot (Lident "Debug", "dprintf")}},
                      flag :: _args) } as app ->
         let open Ast_helper in
         Exp.ifthenelse
           (Exp.apply
              (Exp.ident { txt = Ldot (Lident "Debug", "test_flag");
                           loc = Location.none (*TODO*) })
              [flag])
           app
           None
      | other -> default_mapper.expr mapper other; }

let () = register "Debug hook" ast_mapper
