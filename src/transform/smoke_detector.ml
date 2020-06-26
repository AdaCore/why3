(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* Smoke detector try to find if the axiomatisation is self-contradicting.

   The second smoke detector add the negation under the implication and
   universal quantification (replace implication by conjunction).
*)

open Term
open Decl

let create app =
  Trans.goal (fun pr t -> [create_prop_decl Pgoal pr (app t)])

let top = create t_not

let rec neg f = match f.t_node with
  | Tbinop (Timplies,f1,f2) -> t_and f1 (neg f2)
(* Would show too much smoke ?
  | Tbinop (Timplies,f1,f2) -> t_implies f1 (neg f2)
*)
  | Tquant (Tforall,fq) ->
      let vsl,_trl,f = t_open_quant fq in
      t_forall_close vsl _trl (neg f)
  | Tlet (t,fb) ->
      let vs,f = t_open_bound fb in
      t_let_close vs t (neg f)
  | _ -> t_not f

let deep = create neg

let () = Trans.register_transform "smoke_detector_top" top
  ~desc:"Put@ the@ goal@ under@ negation.@ Used@ to@ \
         detect@ inconsistency@ in@ premises."

let () = Trans.register_transform "smoke_detector_deep" deep
  ~desc:"Put@ the@ conclusion@ of@ the@ goal@ (under@ universal@ \
         quantifiers@ and@ implications)@ under@ negation.@ \
         Used@ to@ detect@ inconsistency@ in@ premises@ \
         and@ goal@ hypotheses."

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
