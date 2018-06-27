(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Term
open Decl
open Theory
open Ty

let debug = Debug.register_info_flag "eliminate_unknown_types"
  ~desc:"Print@ debugging@ messages@ of@ the@ eliminate_unknown_types@ transformation."

let syntactic_transform transf =
  Trans.on_meta Printer.meta_syntax_type (fun metas ->
      let symbols = List.fold_left (fun acc meta_arg ->
      match meta_arg with
      | [MAts ts; MAstr _; MAint _] -> Sts.add ts acc
      | _ -> assert false) Sts.empty metas in
    transf (fun ts -> Sts.exists (ts_equal ts) symbols))

let remove_terms keep =
  let keep_ls ls =
    (* check that we want to keep all the types occurring in the type
       of ls *)
    List.for_all (fun ty -> ty_s_all keep ty) ls.ls_args
    &&
    begin match ls.ls_value with
      | Some ty -> ty_s_all keep ty
      | None -> true            (* bool are kept by default *)
    end
  in
  let keep_term (t:term) =
    t_s_all (fun ty -> ty_s_all keep ty) (fun _ -> true) t
    &&
    begin match t.t_ty with
      | Some t -> ty_s_all keep t
      | None -> true
    end
  in
  Trans.decl (fun d ->
    match d.d_node with
    | Dtype ty when not (keep ty)                                ->
      if Debug.test_flag debug then
        Format.printf "remove@ type@ %a@." Pretty.print_ty_decl ty;
      []
    | Ddata l  when List.exists (fun (t,_) -> not (keep t)) l    ->
      if Debug.test_flag debug then
        Format.printf "remove@ data@ %a@." Pretty.print_data_decl (List.hd l);
      []
    | Dparam l when not (keep_ls l)                              ->
      if Debug.test_flag debug then
        Format.printf "remove@ param@ %a@." Pretty.print_ls l;
      []
    | Dlogic l when List.exists (fun (l,_) -> not (keep_ls l)) l ->
      if Debug.test_flag debug then
        Format.printf "remove@ logic@ %a@." Pretty.print_logic_decl (List.hd l);
      []
    | Dprop (Pgoal,pr,t) when not (keep_term t)                  ->
      if Debug.test_flag debug then
        Format.printf "change@ goal@ %a@." Pretty.print_term t;
      [create_prop_decl Pgoal pr t_false]
    | Dprop (_,_,t) when not (keep_term t)                       ->
      if Debug.test_flag debug then
        Format.printf "remove@ prop@ %a@." Pretty.print_term t;
      []
    | _ -> [d])
    None

let () =
  Trans.register_transform "eliminate_unknown_types" (syntactic_transform remove_terms)
    ~desc:"Remove@ types@ unknown@ to@ the@ prover@ and@ terms@ referring@ to@ them@."
