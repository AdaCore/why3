(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

let body_of_constant = Declarations.body_of_constant

let on_leaf_node node f =
  match node with
  | Lib.Leaf lobj -> f lobj
  | Lib.CompilingLibrary _
  | Lib.OpenedModule _
  | Lib.ClosedModule  _
  | Lib.OpenedSection _
  | Lib.ClosedSection _
  | Lib.FrozenState _ -> ()
