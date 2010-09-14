(*

  This module was poorly designed by Claude Marché, with the
  enormous help of Jean-Christophe Filliatre and Andrei Paskevich
  for finding the right function in the Why3 API

*)


(** Introduction of premises *)

(** The premises of the goal of a task are introduced in the
    context, e.g

      goal G: forall x:t, f1 -> forall y:u, f2 and f3 -> f4

    becomes

      logic x:t
      axiom H1: f1
      logic y:u
      axiom H2: f2
      axiom H3: f3
      goal G: f4

*)

open Ident
open Term
open Decl
open Task


let rec intros pr f = match f.f_node with
  | Fbinop (Fimplies,f1,f2) ->
      (* TODO: split f1 *)
      let id = create_prsymbol (id_fresh "H") in
      let d = create_prop_decl Paxiom id f1 in
      d :: intros pr f2
  | Fquant (Fforall,fq) -> 
      let vsl,_trl,f = f_open_quant fq in
      let intro_var subst vs =
        let ls = create_lsymbol (id_clone vs.vs_name) [] (Some vs.vs_ty) in
        Mvs.add vs (t_app ls [] vs.vs_ty) subst,
        create_logic_decl [ls,None]
      in
      let subst, dl = Util.map_fold_left intro_var Mvs.empty vsl in
      let f = f_subst subst f in  
      dl @ intros pr f

  | _ -> [create_prop_decl Pgoal pr f]

let () = Trans.register_transform "introduce_premises" (Trans.goal intros)



(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
