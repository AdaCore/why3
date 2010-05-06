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

let simplify_formula = Register.store (fun () -> Trans.decl_l decl_l None)


let () = Register.register_transform_l "simplify_formula" simplify_formula

(** remove_trivial_quantification
    Original version in the alt-ergo prover by Sylvain Conchon *)

(** transform \exists x. x == y /\ F into F[y/x] *)
(** transform \forall x. x <> y \/ F into F[y/x] *)

(** test if the freevariable of a term 
    are included in a given set *)
let t_freevars_in fvars t =
  try
    t_v_fold (fun () u -> if not (Svs.mem u fvars) then raise Exit) () t;
    true
  with Exit -> false

exception Subst_found of term

let rec fmla_find_subst freevars var sign f =
  let fnF = fmla_find_subst freevars var in
  match f.f_node with
    | Fapp (ls,[{t_node=Tvar vs};t])
        when sign && ls_equal ls ps_equ && vs_equal vs var 
          && t_freevars_in freevars t ->
        raise (Subst_found t)
    | Fapp (ls,[t;{t_node=Tvar vs}])         
        when sign && ls_equal ls ps_equ && vs_equal vs var 
          && t_freevars_in freevars t ->
        raise (Subst_found t)
    | Fapp (ls,[{t_node=Tvar vs};t])
        when not sign && ls_equal ls ps_neq && vs_equal vs var 
          && t_freevars_in freevars t ->
        raise (Subst_found t)
    | Fapp (ls,[t;{t_node=Tvar vs}]) 
        when not sign && ls_equal ls ps_neq && vs_equal vs var 
          && t_freevars_in freevars t ->
        raise (Subst_found t)
    | Fbinop (For, f1, f2)  when not sign -> (fnF sign f1); (fnF sign f2) 
    | Fbinop (Fand, f1, f2) when sign ->  (fnF sign f1); (fnF sign f2)
    | Fbinop (Fimplies, f1, f2) when not sign -> 
        (fnF (not sign) f1); (fnF sign f2)
    | Fnot f1 -> fnF (not sign) f1
    | Fbinop (Fiff, _, _) | Fif ( _, _, _) -> ()
    | _ -> f_fold (fun () _ -> ()) (fun () -> fnF sign) () f

let rec fmla_quant freevars sign f = function
  | [] -> freevars, [], f
  | vs::l -> 
      let freevars, vsl, f = fmla_quant (Svs.add vs freevars) sign f l in
      let freevars' = Svs.remove vs freevars in
      try
        fmla_find_subst freevars' vs sign f;
        freevars, vs::vsl, f
      with Subst_found t ->
        let f = f_subst_single vs t f in
        freevars', vsl, fmla_simpl f

let rec fmla_remove_quant freevars f =
  match f.f_node with
    | Fquant (k,fb) ->
        let vsl,trl,f = f_open_quant fb in
        let freevars, vsl, f = 
          if trl <> [] 
          then
            let freevars = List.fold_left 
              (fun acc vs -> Svs.add vs acc) freevars vsl in
            freevars, vsl, f
          else
            let sign = match k with
              | Fforall -> false | Fexists -> true in
            fmla_quant freevars sign f vsl in
        let f = fmla_remove_quant freevars f in
        f_quant k vsl trl f
    | _ -> f_map (fun t -> t) (fmla_remove_quant freevars) f

let fmla_remove_quant = (fmla_remove_quant Svs.empty)

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

