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

module Std = Sexplib.Std
module Std_big_int = Sexplib_num.Std.Big_int

let of_list = function
  | Sexplib.Sexp.List l -> l
  | _ -> invalid_arg "Mysexplib.of_list"
