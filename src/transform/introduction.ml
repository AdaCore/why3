
open Ident
open Term
open Decl
open Task


let rec intros pr f = match f.f_node with
  | Fbinop (Fimplies,f1,f2) ->
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
(*
  | Ftrue -> acc
  | Ffalse -> f::acc
  | Fapp _ -> f::acc
  | Fbinop (Fand,f1,f2) when to_split f ->
      split_pos (split_pos acc (f_implies f1 f2)) f1
  | Fbinop (Fand,f1,f2) ->
      split_pos (split_pos acc f2) f1
  | Fbinop (Fimplies,f1,f2) ->
      apply_append2 f_implies acc (split_neg [] f1) (split_pos [] f2)
  | Fbinop (Fiff,f1,f2) ->
      split_pos (split_pos acc (f_implies f1 f2)) (f_implies f2 f1)
  | Fbinop (For,f1,f2) ->
      apply_append2 f_or acc (split_pos [] f1) (split_pos [] f2)
  | Fnot f ->
      apply_append f_not acc (split_neg [] f)
  | Fif (fif,fthen,felse) ->
      split_pos (split_pos acc (f_implies fif fthen)) (f_or fif felse)
  | Flet (t,fb) -> let vs,f = f_open_bound fb in
      apply_append (f_let_close vs t) acc (split_pos [] f)
  | Fcase (tl,bl) ->
      split_case split_pos f_true acc tl bl
  | Fquant (Fexists,_) -> f::acc
*)

let intros pr f : decl list = intros pr f 

let () = Trans.register_transform "introduce_premises" (Trans.goal intros)



(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
