open Decl
open Ident
open Task
open Term
open Theory
open Ty

let inlined_attr = create_attribute "GP_Inlined"

let apply_append fn acc l =
  List.fold_left (fun l e -> fn e :: l) acc (List.rev l)

let is_bool_true t =
  match t.t_node with
  | Tapp (ls, []) when ls_equal ls fs_bool_true -> true
  | _ -> false

let is_bool_false t =
  match t.t_node with
  | Tapp (ls, []) when ls_equal ls fs_bool_false -> true
  | _ -> false

let rec split acc f =
  match f.t_node with
  | Ttrue ->
      f :: acc
  | Tfalse | Tnot _ | Tquant (Texists, _) | Tbinop (Tor, _, _) ->
      f :: acc
  | Tapp (equ, [{t_node = Tif (c,t,e)} ;r])
    when ls_equal equ ps_equ && is_bool_true t && is_bool_false e ->
    (* the unfolding transformation creates terms of the form
          (if P = True then True else False) = True)
       where P is an expression that we want to split further.  We recognize
       such expressions and (want to) simplify them to just "P".  However, we
       introduce a dummy "let" binding so that the labels attached to "P" are
       separated from the labels attached to the larger equality. *)
      if is_bool_true r then begin
        (* The t_attr_copy below may copy enclosing labels at the same node
          as more specific labels. This messes up reporting (which is the
          objective of splitting). We insert a dummy "let" binding here so that
          the attributes end up at different nodes and the more relevant one is
          further down in the tree.
        *)
        let v = create_vsymbol (id_fresh "dummy") ty_bool in
        let c = t_let t_bool_true (t_close_bound v c) in
        let f = t_attr_copy f c in
        split acc f
      end else
        f :: acc
  | Tapp _ -> f :: acc
  | Tbinop (Tand, f1, f2) ->
      split (split acc (t_attr_copy f f2)) (t_attr_copy f f1)
  | Tbinop (Timplies, f1, f2) ->
      let fn f2 = t_attr_copy f (t_implies f1 f2) in
      apply_append fn acc (split [] f2)
  | Tbinop (Tiff,f1,f2) ->
      let f12 = t_attr_copy f (t_implies f1 (t_attr_copy f f2)) in
      let f21 = t_attr_copy f (t_implies f2 (t_attr_copy f f1)) in
      split (split acc f21) f12
  | Tif (fif,fthen,felse) ->
      let fit = t_attr_copy f (t_implies fif fthen) in
      let fie = t_attr_copy f (t_implies (t_not fif) felse) in
      split (split acc fie) fit
  | Tlet (t,fb) ->
      let vs,f1,close = t_open_bound_cb fb in
      let fn f1 = t_attr_copy f (t_let t (close vs f1)) in
      apply_append fn acc (split [] f1)
  | Tcase (tl,bl) ->
      split_case f t_true acc tl bl
  | Tquant (Tforall,fq) ->
      let vsl,trl,f1,close = t_open_quant_cb fq in
      let fn f1 = t_attr_copy f (t_forall (close vsl trl f1)) in
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
  let fn bl = t_attr_copy forig (t_case tl bl) in
  apply_append fn acc bll

let split_goal pr f =
  let make_prop f = [create_prop_decl Pgoal pr f] in
  let l = split [] f in
  List.map make_prop l

let split_conj = Trans.goal_l split_goal

let split_conj_name = "split_conj"
let () =
   Trans.register_transform_l split_conj_name split_conj
   ~desc:"Split conjunctions, equivalences, if-then-else and case in the goal,\
   on the right hand side, and only there."


let post_def_axiom_regexp = Re.Str.regexp ".*__\\(post\\|def\\)_axiom"

let match_axiom s = Re.Str.string_match post_def_axiom_regexp s 0

let rec merge_univ_quant t acc =
  match t.t_node with
  | Tquant (Tforall, tq) -> let vs, tr, t = t_open_quant tq in
                            if tr <> [] then
                              let t = t_quant Tforall (t_close_quant vs tr t)
                              in
                              t_quant Tforall (t_close_quant acc [] t)
                            else
                              merge_univ_quant t (acc @ vs)
  | _ -> t_quant Tforall (t_close_quant acc [] t)

let split_axioms d =
  match d.d_node with
  | Dprop (Paxiom, ({ pr_name = { Ident.id_string = s } } as prsym), term) ->
     if match_axiom s then
       let splitted_terms = split [] term in
       List.rev_map (fun t -> let t = merge_univ_quant t [] in
                              let name = create_prsymbol (Ident.id_fresh s) in
                              create_prop_decl Paxiom name t) splitted_terms
     else
       [ create_prop_decl Paxiom prsym (merge_univ_quant term []) ]
  | _ -> [ d ]

let split_conj_axioms = Trans.decl split_axioms None

let split_conj_axioms_name = "split_conj_axioms"

let inline_attr = Ident.create_attribute "GP_Inline"

let should_unfold ls =
  Sattr.mem inline_attr (ls.ls_name.id_attrs)

(* copied relocate and t_unfold from inlining.ml *)
let rec relocate loc t =
  t_map (relocate loc) (t_attr_set ?loc t.t_attrs t)

let t_unfold loc env fs tl ty =
  match Mls.find_opt fs env with
  | None ->
      assert false
  | Some (vl,e) ->
      let add (mt,mv) x y = ty_match mt x.vs_ty (t_type y), Mvs.add x y mv in
      let (mt,mv) = List.fold_left2 add (Ty.Mtv.empty, Mvs.empty) vl tl in
      let mt = oty_match mt e.t_ty ty in
      t_ty_subst mt mv (relocate loc e)

let is_true t =
  match t.t_node with
  | Ttrue -> true
  | Tapp (ls, []) when ls_equal ls fs_bool_true -> true
  | _ -> false

(* simple traversal function to unfold marked symbols using the map given by
   [env]. When we unfold, we call the function recursively using (n-1) to achieve
   n total unfoldings. *)
let rec unfold_right n env f =
  if n = 0 then f else
  match f.t_node with
  | Ttrue | Tfalse | Tnot _ | Tquant (Texists, _) | Tbinop (Tor, _, _) | Tvar _ | Tconst _  -> f
  | Tbinop (Tand, f1, f2) ->
    t_attr_copy f (t_and (unfold_right n env f1) (unfold_right n env f2))
  | Tbinop (Timplies, f1, f2) ->
    t_attr_copy f (t_implies f1 (unfold_right n env f2))
  | Tbinop (Tiff,f1,f2) ->
    t_attr_copy f (t_iff (unfold_right n env f1) (unfold_right n env f2))
  | Tif (fif,fthen,felse) ->
    t_attr_copy f (t_if fif (unfold_right n env fthen) (unfold_right n env felse))
  | Tlet (t,fb) ->
      let vs,f1,close = t_open_bound_cb fb in
      t_attr_copy f (t_let t (close vs (unfold_right n env f1)))
  | Tcase (t,bl) ->
      unfold_case n env f t bl
  | Tquant (Tforall,fq) ->
      let vsl,trl,f1,close = t_open_quant_cb fq in
      t_attr_copy f (t_forall (close vsl trl (unfold_right n env f1)))
  | Tapp (ls, tl) ->
    let tl = List.map (unfold_right n env) tl in
    if should_unfold ls then
      let f = t_attr_copy f (t_unfold f.t_loc env ls tl f.t_ty) in
      unfold_right (n-1) env f
    else
      t_attr_copy f (t_app ls tl f.t_ty)
  | Teps fb ->
      let vs,f1,close = t_open_bound_cb fb in
      t_attr_copy f (t_eps (close vs (unfold_right n env f1)))

and unfold_case n env forig t bl =
  let bl = List.map (fun b ->
    let pt, f, close = t_open_branch_cb b in
    close pt (unfold_right n env f))
    bl
  in
  t_attr_copy forig (t_case t bl)


let is_all_vars tl =
  List.for_all (fun t ->
    match t.t_node with
    | Tvar _ -> true
    | _ -> false
    ) tl

let rec has_pretty_labels t =
  let is_pretty_label s = Strings.has_prefix "GP_Pretty_Ada" s in
  if Ident.Sattr.exists (fun a -> is_pretty_label a.Ident.attr_string) t.t_attrs then true
  else match t.t_node with
  | Tvar _ | Tconst _ | Tapp _ | Ttrue | Tfalse -> false
  | Tif (f1,f2,f3) -> has_pretty_labels f1 || has_pretty_labels f2 || has_pretty_labels f3
  | Tbinop (_, f1, f2) -> has_pretty_labels f1 || has_pretty_labels f2
  | Tnot f1 -> has_pretty_labels f1
  | Tlet (f1, tb) -> has_pretty_labels f1 || let _, f = t_open_bound tb in has_pretty_labels f
  | Teps tb -> let _,f = t_open_bound tb in has_pretty_labels f
  | Tquant (_, tb) -> let _,_,f = t_open_quant tb in has_pretty_labels f
  | Tcase (f, pl) -> has_pretty_labels f || List.exists branch_has_pretty_labels pl

and branch_has_pretty_labels b =
  let _, f = t_open_branch b in
  has_pretty_labels f

let extract_def env vs lhs rhs =
  match lhs.t_node with
  | Tapp (ls, tl) when is_all_vars tl && should_unfold ls ->
      let r = has_pretty_labels rhs in
      if r then Mls.add ls (vs, rhs) env else env
  | _ -> env

(* function to open all universal quantifiers on top of a term. *)
let rec match_forall f =
  match f.t_node with
  | Tquant (Tforall, tq) ->
      let vs, _, t = t_open_quant tq in
      begin match match_forall t with
      | None -> Some (vs, t)
      | Some (vs2, t) -> Some (vs @ vs2, t)
      end
  | _ -> None

(* function to extract a definition from an axiom. It supports the two cases
     f(x1 ... xn) = rhs
  and
    f(x1 ... xn) = True <-> rhs

  In the latter case, because rhs is a proposition while f returns a boolean,
  we need to wrap "rhs" in an if expression:
    if rhs then True else False
*)

let extract_def_from_axiom env t =
  match match_forall t with
  | Some (vs, t) ->
    begin
      match t.t_node with
      | Tbinop (Tiff, lhs, rhs) ->
        let rhs = t_attr_add inlined_attr rhs in
        begin match lhs.t_node with
        | Tapp (ls, [a; b]) ->
          if ls_equal ls ps_equ then begin
            if is_true b then begin
              extract_def env vs a (t_if rhs t_bool_true t_bool_false)
            end else extract_def env vs lhs rhs
          end else extract_def env vs lhs rhs
        | _ ->
          let rhs = t_attr_add inlined_attr rhs in
          extract_def env vs lhs rhs
        end
      | Tapp (ls, [lhs; rhs]) when ls_equal ls ps_equ ->
        let rhs = t_attr_add inlined_attr rhs in
        extract_def env vs lhs rhs
      | _ -> env
    end
  | _ -> env


(* Function to traverse all declarations and build a map
     symbol -> definition
   for all symbols that are to be unfolded. *)
let fold env d =
  match d.td_node with
    | Decl d ->
    begin match d.d_node with
      | Dlogic [ls,ld]
        when should_unfold ls ->
          let vl,e = open_ls_defn ld in
          if has_pretty_labels e then Mls.add ls (vl,e) env else env
      | Dprop (Paxiom, _, t) ->
          let env = extract_def_from_axiom env t in
          env
      | _ -> env
    end
    | _ -> env

(* Transformation to unfold marked symbols in the goal. We unfold just one
   level currently. *)
let unfold_trans = Trans.store (fun task ->
  let goal, task = task_separate_goal task in
  let env = task_fold fold Mls.empty task in
  match goal.td_node with
      | Decl d ->
        begin match d.d_node with
        | Dprop (Pgoal,sym,t) ->
          begin try
            let g = (unfold_right 1 env t) in
            add_tdecl task (create_decl (create_prop_decl Pgoal sym g))
          with _ ->
            add_tdecl task goal
          end
        | _ -> assert false
        end
      | _ -> assert false)

let () =
  Trans.register_transform split_conj_axioms_name split_conj_axioms
  ~desc:"Split def and post axioms generated by SPARK tools"


let () =
  let trans =
    Trans.compose_l
      Split_goal.split_goal_right
      (Trans.compose_l
        (Trans.singleton unfold_trans)
          split_conj)
  in
  Trans.register_transform_l "split_goal_wp_conj" trans
    ~desc:"split goal followed by conjunction split"

let () =
  let trans =
    Trans.compose_l
      Introduction.split_vc
      (Trans.compose_l
        (Trans.singleton unfold_trans)
          split_conj)
  in
  Trans.register_transform_l "split_vc_conj" trans
    ~desc:"split vc followed by conjunction split"
