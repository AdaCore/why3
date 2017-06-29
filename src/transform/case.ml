open Term
open Ident
open Ty
open Decl
open Args_wrapper
open Generic_arg_trans_utils

(** This file contains transformation with arguments that acts directly on a
    logic connector for intro (case, or_intro, intros, exists) *)

(* From task [delta |- G] and term t, build the tasks:
   [delta, t] |- G] and [delta, not t | - G] *)
let case t name =
  let name =
    match name with
    | Some name -> name
    | None -> "h"
  in
  let h = Decl.create_prsymbol (gen_ident name) in
  let hnot = Decl.create_prsymbol (gen_ident name) in
  let t_not_decl = Decl.create_prop_decl Decl.Paxiom hnot (Term.t_not t) in
  let t_decl = Decl.create_prop_decl Decl.Paxiom h t in
  Trans.par [Trans.add_decls [t_decl]; Trans.add_decls [t_not_decl]]

let or_intro (left: bool) : Task.task Trans.trans =
  Trans.decl (fun d ->
    match d.d_node with
    | Dprop (Pgoal, pr, t) ->
      begin
        match t.t_node with
        | Tbinop (Tor, t1, t2) ->
          if left then
            [create_prop_decl Pgoal pr t1]
          else
            [create_prop_decl Pgoal pr t2]
        | _ -> [d]
      end
    | _ -> [d]) None

let exists_aux g x =
  let t = subst_exist g x in
  let pr_goal = create_prsymbol (gen_ident "G") in
  let new_goal = Decl.create_prop_decl Decl.Pgoal pr_goal t in
      [new_goal]

(* From task [delta |- exists x. G] and term t, build
   the task  [delta |- G[x -> t]].
   Return an error if x and t are not unifiable. *)
let exists x =
  Trans.goal (fun _ g -> exists_aux g x)

(* TODO temporary for intros *)
let rec intros n pr f =
  if n = 0 then [create_prop_decl Pgoal pr f] else
  match f.t_node with
  (* (f2 \/ True) => _ *)
  | Tbinop (Timplies,{ t_node = Tbinop (Tor,f2,{ t_node = Ttrue }) },_)
      when Slab.mem Term.asym_label f2.t_label ->
        [create_prop_decl Pgoal pr f]
  | Tbinop (Timplies,f1,f2) ->
      (* split f1 *)
      (* f is going to be removed, preserve its labels and location in f2  *)
      let f2 = t_label_copy f f2 in
      let l = Split_goal.split_intro_right f1 in
      List.fold_right
        (fun f acc ->
           let id = create_prsymbol (id_fresh "H") in
           let d = create_prop_decl Paxiom id f in
           d :: acc)
        l
        (intros (n-1) pr f2)
  | Tquant (Tforall,fq) ->
      let vsl,_trl,f_t = t_open_quant fq in
      let intro_var subst vs =
        let ls = create_lsymbol (id_clone vs.vs_name) [] (Some vs.vs_ty) in
        Mvs.add vs (fs_app ls [] vs.vs_ty) subst,
        create_param_decl ls
      in
      let subst, decl = intro_var Mvs.empty (List.hd vsl) in
      if List.length vsl = 1 then
        begin
          let f = t_label_copy f (t_subst subst f_t) in
          decl :: intros (n-1) pr f
        end
      else
        let f = t_quant Tforall
            (t_close_quant (List.tl vsl) [] (t_subst subst f_t)) in
        decl :: intros (n-1) pr f
  | Tlet (t,fb) ->
      let vs,f = t_open_bound fb in
      let ls = create_lsymbol (id_clone vs.vs_name) [] (Some vs.vs_ty) in
      let f = t_subst_single vs (fs_app ls [] vs.vs_ty) f in
      let d = create_logic_decl [make_ls_defn ls [] t] in
      d :: intros (n-1) pr f
  | _ -> [create_prop_decl Pgoal pr f]

let intros n pr f =
  let tvs = t_ty_freevars Stv.empty f in
  let mk_ts tv () = create_tysymbol (id_clone tv.tv_name) [] NoDef in
  let tvm = Mtv.mapi mk_ts tvs in
  let decls = Mtv.map create_ty_decl tvm in
  let subst = Mtv.map (fun ts -> ty_app ts []) tvm in
  Mtv.values decls @ intros n pr (t_ty_subst subst Mvs.empty f)

let introduce_premises n = Trans.goal (intros n)

let () = wrap_and_register
    ~desc:"case <term> [name] generates hypothesis 'name: term' in a first goal and 'name: ~ term' in a second one."
    "case"
    (Tformula (Topt ("as",Tstring Ttrans_l))) case

let () = wrap_and_register ~desc:"left transform a goal of the form A \\/ B into A"
    "left"
    (Ttrans) (or_intro true)

let () = wrap_and_register ~desc:"right transform a goal of the form A \\/ B into B"
    "right"
    (Ttrans) (or_intro false)

let () = wrap_and_register
    ~desc:"exists <term> substitutes the variable quantified by exists with term"
    "exists"
    (Tterm Ttrans) exists

let () = wrap_and_register ~desc:"intros n"
    "intros"
    (Tint Ttrans) introduce_premises
