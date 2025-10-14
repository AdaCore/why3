(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2025 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(********************************************************************)

module Exp = Ppxlib.Ast_builder.Default

let test_flag ~loc =
  Exp.pexp_ident ~loc { txt = Ldot ((Lident "Debug"), "test_flag"); loc  }
let debug_no_expansion ~loc =
  Exp.pexp_ident ~loc { txt = Ldot ((Lident "Debug"), "dprintf_no_expansion");
loc  }

let expand_dprintf =
  Ppxlib.Context_free.Rule.special_function'
  (Ldot (Lident "Debug","dprintf"))
 (fun expr ->
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
      | other -> None)

let () =
  Ppxlib.Driver.register_transformation "Debug hook"
    ~rules:[expand_dprintf]

let () =
  Ppxlib.Driver.run_as_ppx_rewriter ()
