(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2026 --  Inria - CNRS - Paris-Saclay University       *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(********************************************************************)

open Why3
open Format
open Ident
open Term
open Model_parser

let source_file = "model_order.mlw"
let source_line = 12

let loc =
  Loc.user_position source_file source_line 0 source_line 1

let attrs =
  Ident.Sattr.singleton
    (Ident.create_attribute "model_trace:loop_index")

let make_element internal_name value =
  let lsymbol =
    Term.create_fsymbol
      (Ident.id_fresh ~attrs ~loc internal_name) [] Ty.ty_int
  in
  Model_parser.create_model_element
    ~value:(Term.t_const (Constant.int_const_of_int value) Ty.ty_int)
    ~concrete_value:Model_parser.concrete_undefined
    ~oloc:(Some loc) ~attrs ~lsymbol

let elements =
  [ make_element "index_1" 1;
    make_element "index_2" 2;
    make_element "index_3" 3 ]

let model =
  Model_parser.set_model_files Model_parser.empty_model
    (Wstdlib.Mstr.singleton source_file
       (Wstdlib.Mint.singleton source_line elements))

let candidates =
  [ Call_provers.Unknown "empty", Model_parser.empty_model;
    Call_provers.Unknown "sat", model;
    Call_provers.Unknown "empty", Model_parser.empty_model ]

let model =
  match
    Check_ce.last_nonempty_model
      ~env:(Env.create_env []) ~known_map:Ident.Mid.empty candidates
  with
  | Some model -> model
  | None -> failwith "no model selected"

let elements = Model_parser.get_model_elements model

let () =
  let show element =
    asprintf "%s=%a"
      element.me_lsymbol.ls_name.id_string
      Model_parser.print_concrete_term element.me_concrete_value
  in
  printf "same-location model order: %s@."
    (String.concat ", " (List.map show elements))
