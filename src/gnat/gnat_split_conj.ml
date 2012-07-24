open Why3
open Ident
open Term
open Decl

let apply_append fn acc l =
  List.fold_left (fun l e -> fn e :: l) acc (List.rev l)

let rec split acc f =
   match f.t_node with
   | Ttrue ->
         acc
   | Tfalse | Tapp _ | Tnot _ | Tquant (Texists, _)
   | Tbinop (Tor, _, _) ->
         f :: acc
   | Tbinop (Tand, f1, f2) ->
         split (split acc f2) f1
   | Tbinop (Timplies, f1, f2) ->
         let fn f2 = t_label_copy f (t_implies f1 f2) in
         apply_append fn acc (split [] f2)
  | Tbinop (Tiff,f1,f2) ->
      let f12 = t_label_copy f (t_implies f1 f2) in
      let f21 = t_label_copy f (t_implies f2 f1) in
      split (split acc f21) f12
  | Tif (fif,fthen,felse) ->
      let fit = t_label_copy f (t_implies fif fthen) in
      let fie = t_label_copy f (t_implies (t_not fif) felse) in
      split (split acc fie) fit
  | Tlet (t,fb) ->
      let vs,f1,close = t_open_bound_cb fb in
      let fn f1 = t_label_copy f (t_let t (close vs f1)) in
      apply_append fn acc (split [] f1)
  | Tcase (tl,bl) ->
      split_case f t_true acc tl bl
  | Tquant (Tforall,fq) ->
      let vsl,trl,f1,close = t_open_quant_cb fq in
      let fn f1 = t_label_copy f (t_forall (close vsl trl f1)) in
      apply_append fn acc (split [] f1)
   | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)

and split_case forig c acc tl bl =
  let bl = List.rev_map t_open_branch_cb bl in
  let bll,_ = List.fold_left (fun (bll,el) (pl,f,close) ->
    let spf = split [] f in
    let brc = close pl c in
    let bll = List.map (fun rl -> brc::rl) bll in
    let bll = apply_append (fun f -> close pl f :: el) bll spf in
    bll, brc::el) ([],[]) bl
  in
  let fn bl = t_label_copy forig (t_case tl bl) in
  apply_append fn acc bll

let split_goal pr f =
  let make_prop f = [create_prop_decl Pgoal pr f] in
  List.map make_prop (split [] f)

let split_conj = Trans.goal_l split_goal

let split_conj_name = "split_conj"
let () = Trans.register_transform_l split_conj_name split_conj


