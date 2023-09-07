(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** {2 User-defined strategies} *)

open Wstdlib

type instruction =
  | Icall_prover of (Whyconf.prover * float option * int option * int option) list
    (** timelimit (if none use default timelimit),
        memlimit (if none use default memlimit)
        steplimit (if none use no step limit)
     *)
  | Itransform of string * int (** successor state on success *)
  | Igoto of int (** goto state *)

type t = instruction array


exception StratFailure of string * exn
exception UnknownStrat of string
exception KnownStrat of string

type strat = Sdo_nothing | Sapply_trans of string * string list * strat list

let named s f env (t : Task.task) =
  try f env t with e -> raise (StratFailure (s,e))

type reg_strat = Pp.formatted * (Env.env -> Task.task -> strat)
let strats : reg_strat Hstr.t = Hstr.create 17

let register_strat ~desc s p =
  if Hstr.mem strats s then raise (KnownStrat s);
  Hstr.replace strats s (desc, fun env task -> named s p env task)

let lookup_strat s =
  try snd (Hstr.find strats s)
  with Not_found -> raise (UnknownStrat s)

let list_strats () =
  Hstr.fold (fun k (s,_) acc -> (k,s)::acc) strats []

let meta_test = Theory.(register_meta "test_strategy" [MTlsymbol;MTprsymbol] ~desc:"")

let strat_test _ task =
  let decls = Task.find_meta_tds task meta_test in
  let open Ident in
  let open Term in
  let open Decl in
  let open Theory in
  match (Stdecl.choose decls.Task.tds_set).td_node with
  | Meta(_,[MAls p;MApr pr]) ->
      begin
        let g = Task.task_goal_fmla task in
        match g.t_node with
        | Term.Tapp(ls,_) when ls_equal ls p ->
            let a1 = Sapply_trans("apply",[pr.pr_name.id_string],[Sdo_nothing;Sdo_nothing]) in
            Sapply_trans("apply",[pr.pr_name.id_string],[Sdo_nothing;a1])
        | _ -> Sdo_nothing
      end
  | _ -> assert false

let () =
  register_strat "test" strat_test
    ~desc:"Only@ for@ testing@ purposes."
