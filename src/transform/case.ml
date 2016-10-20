
open Trans
open Term
open Decl
open Theory
open Task
open Args_wrapper

let rec dup n x = if n = 0 then [] else x::(dup (n-1) x)

let gen_ident = Ident.id_fresh

(* From task [delta |- G] and term t, build the tasks:
   [delta, t] |- G] and [delta, not t | - G] *)
let case t =
  let h = Decl.create_prsymbol (gen_ident "h") in
  let hnot = Decl.create_prsymbol (gen_ident "hnot") in
  let t_not_decl = Decl.create_prop_decl Decl.Paxiom hnot (Term.t_not t) in
  let t_decl = Decl.create_prop_decl Decl.Paxiom h t in
  Trans.par [Trans.add_decls [t_decl]; Trans.add_decls [t_not_decl]]

(* From task [delta |- G] , build the tasks [delta, t | - G] and [delta] |- t] *)
let cut name t =
  let h = Decl.create_prsymbol (gen_ident name) in
  let g_t = Decl.create_prop_decl Decl.Pgoal h t in
  let h_t = Decl.create_prop_decl Decl.Paxiom h t in
  let goal_cut = Trans.goal (fun _ _ -> [g_t]) in
  let goal = Trans.add_decls [h_t] in
  Trans.par [goal; goal_cut]

let subst_quant c tq x : term =
  let (vsl, tr, te) = t_open_quant tq in
  (match vsl with
  | hdv :: tl ->
      (try
        (let new_t = t_subst_single hdv x te in
        t_quant_close c tl tr new_t)
      with
      | Ty.TypeMismatch (_ty1, _ty2) -> failwith "type mismatch") (* TODO match errors *)
  | [] -> failwith "no")


(* Transform the term (exists v, f) into f[x/v] *)
let subst_exist t x =
  match t.t_node with
  | Tquant (Texists, tq) ->
      subst_quant Texists tq x
  | _ -> failwith "term do not begin with exists"

(* Transform the term (forall v, f) into f[x/v] *)
let subst_forall t x =
  match t.t_node with
  | Tquant (Tforall, tq) ->
      subst_quant Tforall tq x
  | _ -> failwith "term do not begin with forall"

let exists_aux g x =
  let t = subst_exist g x in
  let pr_goal = create_prsymbol (gen_ident "G") in
  let new_goal = Decl.create_prop_decl Decl.Pgoal pr_goal t in
      [new_goal]

(* From task [delta |- exists x. G] and term t, build the task [delta] |- G[x -> t]]
   Return an error if x and t are not unifiable. *)
let exists x =
  Trans.goal (fun _ g -> exists_aux g x)

(* Return a new task with hypothesis name removed *)
let remove_task_decl (name: Ident.ident) : task trans =
  Trans.decl
    (fun d ->
     match d.d_node with
    | Dprop (Paxiom, pr, _) when (Ident.id_equal pr.pr_name name) ->
       []
    | _ -> [d])
    None

(* TODO check if this works in particular when hypothesis names
    are extracted from same name. Seemed not to work before
  adding "print_task". To be resolved in a better way. *)
(* from task [delta, name:A |- G]  build the task [delta |- G] *)
let remove name =
  remove_task_decl name.pr_name

(* from task [delta, name:forall x.A |- G,
     build the task [delta,name:forall x.A,name':A[x -> t]] |- G] *)
let instantiate (pr: Decl.prsymbol) t =
  Trans.decl
    (fun d ->
      match d.d_node with
      | Dprop (pk, dpr, ht) when Ident.id_equal dpr.pr_name pr.pr_name ->
          let t_subst = subst_forall ht t in
          let new_pr = create_prsymbol (Ident.id_clone dpr.pr_name) in
          let new_decl = create_prop_decl pk new_pr t_subst in
          [d; new_decl]
      | _ -> [d]) None

(* TODO find correct librrary *)
let choose_option a b =
  match a, b with
  | Some x, _ -> Some x
  | None, Some x -> Some x
  | None, None -> None

(* TODO stupid This function return the term we need to use in place of
  the variable so that the 2 terms can be equal.
This function is NOT used to check that the 2 terms are equal as we want
library function from Term to do that.
TODO cases are probably forgotten. To be completed  *)
let rec is_unify t x v =
  match t.t_node, x.t_node with
  | Tvar v', _ when v == v' -> Some x
  | Tapp(ls, tl), Tapp(ls', tl') when ls == ls' ->
    is_unify_list tl tl' v
  | Tif (f, t, e), Tif(f', t', e') ->
    is_unify_list [f;t;e] [f';t';e'] v
  | Tlet (t, tb), Tlet (t', tb') ->
    let (_v', e) = t_open_bound tb in
    let (_v'', e') = t_open_bound tb' in
    is_unify_list [t; e] [t'; e'] v
  | Tcase (t, bl), Tcase (t', bl') ->
    choose_option
      (List.fold_left2 (fun acc b b' ->
      let (_, t1) = t_open_branch b in
      let (_, t2) = t_open_branch b' in
      choose_option acc (is_unify t1 t2 v)) None bl bl')
    (is_unify t t' v)
  | Teps tb, Teps tb' ->
    let (_v', e) = t_open_bound tb in
    let (_v'', e') = t_open_bound tb' in
    is_unify e e' v
  | Tquant (_q, tq), Tquant (_q', tq') ->
    let (_vl, _tr, t) = t_open_quant tq in
    let (_vl', _tr', t') = t_open_quant tq' in
    is_unify t t' v
  | Tbinop (_b, t1, t2), Tbinop (_b', t1', t2') ->
    is_unify_list [t1;t2] [t1';t2'] v
  | Tnot t, Tnot t' ->
    is_unify t t' v
  | _, _ -> None

and is_unify_list tl xl v =
  List.fold_left2 (fun acc t1 t2 ->
    choose_option acc (is_unify t1 t2 v)) None tl xl

let term_decl d =
  match d.td_node with
  | Decl ({d_node = Dprop (_pk, _pr, t)}) -> t
  | _ -> failwith "Not a correct prop"

let pr_prsymbol pr =
  match pr with
  | Decl {d_node = Dprop (_pk, pr, _t)} -> Some pr
  | _ -> None

(* Looks for the hypothesis name and return it. If not found return None *)
let find_hypothesis (name:Ident.ident) task =
  let ndecl = ref None in
  let _ = task_iter (fun x -> if (
    match (pr_prsymbol x.td_node) with
    | None -> false
    | Some pr -> Ident.id_equal pr.pr_name name) then ndecl := Some x) task in
  !ndecl


(* from task [delta, name:forall x.A->B |- G,
   build the task [delta,name:forall x.A->B] |- A[x -> t]] ou t est tel que B[x->t] = G *)
let apply pr task =
  let name = pr.pr_name in
  let g, task = Task.task_separate_goal task in
  let tg = term_decl g in
  let d = find_hypothesis name task in
  if d = None then failwith "Hypothesis not found" else
  let d = Opt.get d in
  let t = term_decl d in
  match t.t_node with
  | Tquant (Tforall, tb) ->
    let (vl, tr, t) = t_open_quant tb in
    let v = List.hd vl in
    begin
      match t.t_node with
      | Tbinop (Timplies, ta, tb) ->
        let candidate_unifier = is_unify tb tg v in
        begin
          match candidate_unifier with
          | None -> failwith "Unable to unify the hypothesis with the goal"
          | Some x ->
            let new_goal = t_forall_close (List.tl vl) tr (t_subst_single v x ta) in
            let new_tb = t_subst_single v x tb in
            (* TODO t_equal is probably too strong *)
            if (Term.t_equal new_tb tg) then
              Task.add_decl task (create_prop_decl Pgoal
                                    (create_prsymbol (gen_ident "G")) new_goal)
            else
              (Format.printf
                 "Term substituted was %a. Should be goal was %a. Goal was %a @."
                 Pretty.print_term x Pretty.print_term new_tb Pretty.print_term tg;
              failwith "After substitution, terms are not exactly identical")
        end
      | _ -> failwith "Not of the form forall immediately followed by implies"
    end
  | Tbinop (Timplies, _ta, _tb) -> failwith "Not implemented yet" (* TODO to be done later *)
  | _ -> failwith "Not of the form forall x. A -> B"


let use_th th =
  Trans.add_tdecls [Theory.create_use th]

let () = register_transform_with_args_l ~desc:"test case" "case" (wrap_l (Tformula Ttrans_l) case)
let () = register_transform_with_args_l ~desc:"test cut" "cut" (wrap_l (Tstring (Tformula Ttrans_l)) cut)
let () = register_transform_with_args ~desc:"test exists" "exists" (wrap (Tterm Ttrans) exists)
let () = register_transform_with_args ~desc:"test remove" "remove" (wrap (Tprsymbol Ttrans) remove)
let () = register_transform_with_args ~desc:"test instantiate" "instantiate"
                                      (wrap (Tprsymbol (Tterm Ttrans)) instantiate)
let () = register_transform_with_args ~desc:"test apply" "apply" (wrap (Tprsymbol Ttrans) (fun x -> Trans.store (apply x)))
let () = register_transform_with_args_l ~desc:"test duplicate" "duplicate" (wrap_l (Tint Ttrans_l) (fun x -> Trans.store (dup x)))
let () = register_transform_with_args ~desc:"use theory" "use_th" (wrap (Ttheory Ttrans) (use_th))
