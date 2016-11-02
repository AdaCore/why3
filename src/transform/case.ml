
open Trans
open Term
open Decl
open Theory
open Task
open Args_wrapper
open Reduction_engine


let rec dup n x = if n = 0 then [] else x::(dup (n-1) x)

let gen_ident = Ident.id_fresh

(* From task [delta |- G] and term t, build the tasks:
   [delta, t] |- G] and [delta, not t | - G] *)
let case t name =
  let h = Decl.create_prsymbol (gen_ident name) in
  let hnot = Decl.create_prsymbol (gen_ident name) in
  let t_not_decl = Decl.create_prop_decl Decl.Paxiom hnot (Term.t_not t) in
  let t_decl = Decl.create_prop_decl Decl.Paxiom h t in
  Trans.par [Trans.add_decls [t_decl]; Trans.add_decls [t_not_decl]]

(* From task [delta |- G] , build the tasks [delta, t | - G] and [delta] |- t] *)
let cut t name =
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

(* Do as intros: introduce all premises of hypothesis pr and return a triple
   (goal, list_premises, binded variables) *)
let intros f =
  let rec intros_aux lp lv f =
    match f.t_node with
    | Tbinop (Timplies, f1, f2) ->
        intros_aux (f1 :: lp) lv f2
    | Tquant (Tforall, fq) ->
        let vsl, _, fs = t_open_quant fq in
        intros_aux lp (List.fold_left (fun v lv -> Svs.add lv v) lv vsl) fs
    | _ -> (lp, lv, f) in
  intros_aux [] Svs.empty f

(* Apply:
   1) takes the hypothesis and introduce parts of it to keep only the last element of
      the implication. It gathers the premises and variables in a list.
   2) try to find a good substitution for the list of variables so that last element
      of implication is equal to the goal.
   3) generate new goals corresponding to premises with variables instantiated with values found
      in 2).
 *)
let apply pr : Task.task Trans.tlist = Trans.store (fun task ->
  let name = pr.pr_name in
  let g, task = Task.task_separate_goal task in
  let g = term_decl g in
  let d = find_hypothesis name task in
  if d = None then failwith "Hypothesis not found";
  let d = Opt.get d in
  let t = term_decl d in
  let (lp, lv, nt) = intros t in
  let (_ty, subst) = try first_order_matching lv [nt] [g] with
    (* TODO export the exception *)
  | _ -> failwith "Unable to instantiate variables with possible values" in
  let inst_nt = t_subst subst nt in
  if (Term.t_equal inst_nt g) then
    let nlp = List.map (t_subst subst) lp in
    let lt = List.map (fun ng -> Task.add_decl task (create_prop_decl Pgoal
                          (create_prsymbol (gen_ident "G")) ng)) nlp in
    lt
  else
    (Format.printf
      "Term %a and %a are not equal. Failure in matching @."
       Pretty.print_term inst_nt Pretty.print_term g;
     failwith "After substitution, terms are not exactly identical"))

(* Replace all occurences of f1 by f2 in t *)
let rec replace_in_term f1 f2 t =
  t_map (fun t -> if t_equal t f1 then f2 else replace_in_term f1 f2 t) t
(* TODO be careful with label copy in t_map *)

let replace rev f1 f2 t =
  match rev with
  | true -> replace_in_term f1 f2 t
  | false -> replace_in_term f2 f1 t

(* Generic fold to be put in Trans ? TODO *)
let fold (f: decl -> 'a -> 'a) (acc: 'a): 'a Trans.trans =
  Trans.fold (fun t acc -> match t.task_decl.td_node with
  | Decl d -> f d acc
  | _ -> acc) acc


let rewrite rev h h1 =
  let r =
    fold (fun d acc ->
      match d.d_node with
      | Dprop (Paxiom, pr, t) when (Ident.id_equal pr.pr_name h.pr_name)->
          (match t.t_node with
          | Tapp (ls, [t1; t2]) when ls_equal ls ps_equ ->
              Some (t1, t2)
          | Tbinop (Tiff, t1, t2) ->
              Some (t1, t2)
          | _ -> failwith "Hypothesis is neither an equality nor an equivalence@.")
      | _ -> acc) None in
  Trans.bind r
    (fun r -> Trans.decl (fun d ->
      match d.d_node with
      | Dprop (p, pr, t) when (Ident.id_equal pr.pr_name h1.pr_name && (p = Paxiom || p = Pgoal))->
          (match r with
          | None -> assert (false) (* Should not happen even in failing cases *)
          | Some (t1, t2) ->
              [create_prop_decl p pr (replace rev t1 t2 t)])
      | _ -> [d]) None)

let rewrite_rev = rewrite false

let rewrite = rewrite true

(* Replace occurences of t1 with t2 in h *)
let replace t1 t2 h =
  if not (Ty.ty_equal (t_type t1) (t_type t2)) then
    failwith "Terms provided are not of the same type @."
  else
    (* Create a new goal for equality of the two terms *)
    let g = Decl.create_prop_decl Decl.Pgoal h (t_app_infer ps_equ [t1; t2]) in
    let ng = Trans.goal (fun _ _ -> [g]) in
    let g = Trans.decl (fun d ->
      match d.d_node with
      | Dprop (p, pr, t) when (Ident.id_equal pr.pr_name h.pr_name && (p = Paxiom || p = Pgoal)) ->
          [create_prop_decl p pr (replace true t1 t2 t)]
      | _ -> [d]) None in
    Trans.par [g; ng]

let use_th th =
  Trans.add_tdecls [Theory.create_use th]

let () = register_transform_with_args_l ~desc:"test case" "case" (wrap_l (Tformula (Tstring Ttrans_l)) case)
let () = register_transform_with_args_l ~desc:"test cut" "cut" (wrap_l (Tformula (Tstring Ttrans_l)) cut)
let () = register_transform_with_args ~desc:"test exists" "exists" (wrap (Tterm Ttrans) exists)
let () = register_transform_with_args ~desc:"test remove" "remove" (wrap (Tprsymbol Ttrans) remove)
let () = register_transform_with_args ~desc:"test instantiate" "instantiate"
                                      (wrap (Tprsymbol (Tterm Ttrans)) instantiate)
let () = register_transform_with_args_l ~desc:"test apply" "apply"
    (wrap_l (Tprsymbol Ttrans_l) apply)
let () = register_transform_with_args_l ~desc:"test duplicate" "duplicate" (wrap_l (Tint Ttrans_l) (fun x -> Trans.store (dup x)))
let () = register_transform_with_args ~desc:"use theory" "use_th" (wrap (Ttheory Ttrans) (use_th))
let () = register_transform_with_args ~desc:"left to right rewrite of first hypothesis into the second" "rewrite"
    (wrap (Tprsymbol (Tprsymbol Ttrans)) (rewrite))
let () = register_transform_with_args ~desc:"right to left rewrite of first hypothesis into the second" "rewrite_rev"
    (wrap (Tprsymbol (Tprsymbol Ttrans)) (rewrite_rev))
let () = register_transform_with_args_l ~desc:"replace occurences of first term with second term in given hypothesis/goal" "replace"
    (wrap_l (Tterm (Tterm (Tprsymbol Ttrans_l))) (replace))
