(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* useful option combinators *)

let get_exn exn = function None -> raise exn | Some x -> x

let fold f d = function None -> d | Some x -> f d x

let map_fold f acc x = match x with
  | None -> acc, None
  | Some x -> let acc, x = f acc x in acc, Some x
