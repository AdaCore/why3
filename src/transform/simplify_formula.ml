(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Term
open Decl

let rec fmla_simpl f = f_map_simp (fun t -> t) fmla_simpl f

let decl_l d =
  match d.d_node with
    | Dprop (k,pr,f) -> 
        let f = fmla_simpl f in
        begin match f.f_node, k with
          | Ftrue, Paxiom -> [[]]
          | Ffalse, Paxiom -> []
          | Ftrue, Pgoal -> []
          | _ -> [[create_prop_decl k pr f]]
        end
    | _ -> [[decl_map (fun t -> t) fmla_simpl d]]

let simplify_formula = Register.store 
  (fun () -> Trans.rewrite (fun t -> t) fmla_simpl None)

let simplify_formula_and_task = 
  Register.store (fun () -> Trans.decl_l decl_l None)

let () = Register.register_transform 
  "simplify_formula" simplify_formula

let () = Register.register_transform_l 
  "simplify_formula_and_task" simplify_formula_and_task

(** remove_trivial_quantification
    Original version in the alt-ergo prover by Sylvain Conchon *)

(** transform \exists x. x == y /\ F into F[y/x] *)
(** transform \forall x. x <> y \/ F into F[y/x] *)

(** test if the freevariable of a term 
    are included in a given set *)
let t_boundvars_in fvars t =
  try
    t_v_fold (fun () u -> if Svs.mem u fvars then raise Exit) () t;
    false
  with Exit -> true

exception Subst_found of term

let rec fmla_find_subst boundvars var sign f =
  let fnF = fmla_find_subst boundvars var in
  match f.f_node with
    | Fapp (ls,[{t_node=Tvar vs} as tv;t])
        when sign && ls_equal ls ps_equ && vs_equal vs var 
          && not (t_equal t tv) && not (t_boundvars_in boundvars t) ->
        raise (Subst_found t)
    | Fapp (ls,[t;{t_node=Tvar vs} as tv])         
        when sign && ls_equal ls ps_equ && vs_equal vs var 
          && not (t_equal t tv) && not (t_boundvars_in boundvars t) ->
        raise (Subst_found t)
    | Fapp (ls,[{t_node=Tvar vs} as tv;t])
        when not sign && ls_equal ls ps_neq && vs_equal vs var 
          && not (t_equal t tv) && not (t_boundvars_in boundvars t) ->
        raise (Subst_found t)
    | Fapp (ls,[t;{t_node=Tvar vs} as tv]) 
        when not sign && ls_equal ls ps_neq && vs_equal vs var 
          && not (t_equal t tv) && not (t_boundvars_in boundvars t) ->
        raise (Subst_found t)
    | Fbinop (For, f1, f2)  when not sign -> (fnF sign f1); (fnF sign f2) 
    | Fbinop (Fand, f1, f2) when sign ->  (fnF sign f1); (fnF sign f2)
    | Fbinop (Fimplies, f1, f2) when not sign -> 
        (fnF (not sign) f1); (fnF sign f2)
    | Fnot f1 -> fnF (not sign) f1
    | Fquant (_,fb) ->
        let vsl,trl,f' = f_open_quant fb in
        if trl = [] 
        then 
          let boundvars = 
            List.fold_left (fun s v -> Svs.add v s) boundvars vsl in
          fmla_find_subst boundvars var sign f'
    | Flet (_,fb) ->
        let vs,f' = f_open_bound fb in
        let boundvars = Svs.add vs boundvars in
        fmla_find_subst boundvars var sign f'
    | Fcase (_,fbs) ->
        let iter_fb fb =
          let patl,f = f_open_branch fb in
          let boundvars = 
            List.fold_left (fun s p -> pat_freevars s p) boundvars patl in
          fmla_find_subst boundvars var sign f in
        List.iter iter_fb fbs
    | Fbinop (_, _, _) | Fif ( _, _, _) | Fapp _ | Ffalse | Ftrue-> ()

let rec fmla_quant sign f = function
  | [] -> [], f
  | vs::l -> 
      let vsl, f = fmla_quant sign f l in
      try
        fmla_find_subst Svs.empty vs sign f;
        vs::vsl, f
      with Subst_found t ->
        let f = f_subst_single vs t f in
        vsl, fmla_simpl f

let rec fmla_remove_quant f =
  match f.f_node with
    | Fquant (k,fb) ->
        let vsl,trl,f' = f_open_quant fb in
          if trl <> [] 
          then f
          else
            let sign = match k with
              | Fforall -> false | Fexists -> true in
            let vsl, f' = fmla_quant sign f' vsl in
            let f' = fmla_remove_quant f' in
            f_quant k vsl [] f'
    | _ -> f_map (fun t -> t) fmla_remove_quant f

(*let fmla_remove_quant f =
  Format.eprintf "@[<hov>%a =>|@\n" Pretty.print_fmla f;
  let f = fmla_remove_quant f in
  Format.eprintf "|=>%a@]@.@." Pretty.print_fmla f;
  Pretty.forget_all ();
  f
*)

let simplify_trivial_quantification = 
  Register.store 
    (fun () -> Trans.rewrite (fun t -> t) fmla_remove_quant None)

let () = Register.register_transform 
  "simplify_trivial_quantification" simplify_trivial_quantification

let on_goal fn =
  let fn task = match task with
    | Some {Task.task_decl = 
          Task.Decl ({d_node = Decl.Dprop (Pgoal,pr,fmla)});
           task_prev = task_prev} -> 
        (List.fold_left Task.add_decl) task_prev (fn pr fmla)
    | _ -> assert false in
  Trans.store fn


let simplify_trivial_quantification_in_goal =
  Register.store
    (fun () -> on_goal (fun pr f -> 
                          [create_prop_decl Pgoal pr (fmla_remove_quant f)]))

let () = Register.register_transform 
  "simplify_trivial_quantification_in_goal" 
   simplify_trivial_quantification_in_goal
