
open Trans
open Term
open Decl
open Theory
open Task
open Args_wrapper
open Reduction_engine

let debug_matching = Debug.register_info_flag "print_match"
  ~desc:"Print@ terms@ that@ were@ not@ successfully@ matched@ by@ ITP@ tactic@ apply."

exception Arg_trans of string
exception Arg_trans_term of (string * Term.term option * Term.term option)
exception Arg_trans_type of (string * Ty.ty option * Ty.ty option)

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
      | Ty.TypeMismatch (ty1, ty2) -> raise (Arg_trans_type ("subst_quant", Some ty1, Some ty2)))
  | [] -> failwith "subst_quant: Should not happen, please report")

(* Transform the term (exists v, f) into f[x/v] *)
let subst_exist t x =
  match t.t_node with
  | Tquant (Texists, tq) ->
      subst_quant Texists tq x
  | _ -> raise (Arg_trans "subst_exist")

(* Transform the term (forall v, f) into f[x/v] *)
let subst_forall t x =
  match t.t_node with
  | Tquant (Tforall, tq) ->
      subst_quant Tforall tq x
  | _ -> raise (Arg_trans "subst_forall")

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
  | _ -> raise (Arg_trans "term_decl")

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

exception Hyp_not_found

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
  if d = None then raise Hyp_not_found;
  let d = Opt.get d in
  let t = term_decl d in
  let (lp, lv, nt) = intros t in
  let (_ty, subst) = try first_order_matching lv [nt] [g] with
  | Reduction_engine.NoMatch (Some (t1, t2)) ->
      (if (Debug.test_flag debug_matching) then
        Format.printf "Term %a and %a can not be matched. Failure in matching@."
          Pretty.print_term t1 Pretty.print_term t2
      else ()); raise (Reduction_engine.NoMatch (Some (t1, t2)))
  | Reduction_engine.NoMatch None -> raise (Reduction_engine.NoMatch None)
  in
  let inst_nt = t_subst subst nt in
  if (Term.t_equal_nt_nl inst_nt g) then
    let nlp = List.map (t_subst subst) lp in
    let lt = List.map (fun ng -> Task.add_decl task (create_prop_decl Pgoal
                          (create_prsymbol (gen_ident "G")) ng)) nlp in
    lt
  else
    raise (Arg_trans_term ("apply", Some inst_nt, Some g)))

(*(Format.printf
      "Term %a and %a are not equal. Failure in matching @."
       Pretty.print_term inst_nt Pretty.print_term g;
     failwith "After substitution, terms are not exactly identical"))*)

(* Replace all occurences of f1 by f2 in t *)
let replace_in_term = Term.t_replace
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

(* - If f1 unifiable to t with substitution s then return s.f2 and replace every
     occurences of s.f1 with s.f2 in the rest of the term
   - Else call recursively on subterms of t *)
(* If a substitution s is found then new premises are computed as e -> s.e *)
let replace_subst lp lv f1 f2 t =
  (* is_replced is common to the whole execution of replace_subst. Once an occurence is found,
     it changes to Some (s) so that only one instanciation is rewrritten during execution *)
  (* Note that we can't use an accumulator to do this *)
  let is_replaced = ref None in

  let rec replace lv f1 f2 t : Term.term =
  match !is_replaced with
  | Some subst -> replace_in_term (t_subst subst f1) (t_subst subst f2) t
  | None ->
    begin
      let fom = try Some (first_order_matching lv [f1] [t]) with
      | Reduction_engine.NoMatch (Some (t1, t2)) ->
        (if (Debug.test_flag debug_matching) then
          Format.printf "Term %a and %a can not be matched. Failure in matching@."
          Pretty.print_term t1 Pretty.print_term t2
        else ()); None
      | Reduction_engine.NoMatch None -> None in
        (match fom with
        | None -> t_map (fun t -> replace lv f1 f2 t) t
        | Some (_ty, subst) ->
        let sf1 = t_subst subst f1 in
        if (Term.t_equal sf1 t) then
        begin
          is_replaced := Some subst;
          t_subst subst f2
        end
        else
          replace lv f1 f2 t)
    end in
  let t = t_map (replace lv f1 f2) t in
  match !is_replaced with
  | None -> raise Not_found
  | Some subst ->
    (List.map (t_subst subst) lp, t)

exception Bad_hypothesis of Term.term

let rewrite rev h h1 =
  let found_eq =
    (* Used to find the equality we are rewriting on *)
    fold (fun d acc ->
      match d.d_node with
      | Dprop (Paxiom, pr, t) when Ident.id_equal pr.pr_name h.pr_name ->
          let lp, lv, f = intros t in
          let t1, t2 = (match f.t_node with
          | Tapp (ls, [t1; t2]) when ls_equal ls ps_equ ->
              (* Support to rewrite from the right *)
              if rev then (t1, t2) else (t2, t1)
          | _ -> raise (Bad_hypothesis f)) in
          Some (lp, lv, t1, t2)
      | _ -> acc) None in

(* Return instantiated premises and the hypothesis correctly rewritten *)
  let lp_new found_eq =
    match found_eq with
    | None -> raise Hyp_not_found
    | Some (lp, lv, t1, t2) ->
      fold (fun d acc ->
        match d.d_node with
        | Dprop (p, pr, t) when (Ident.id_equal pr.pr_name h1.pr_name && (p = Paxiom || p = Pgoal)) ->
          let lp, new_term = replace_subst lp lv t1 t2 t in
            Some (lp, create_prop_decl p pr new_term)
        | _ -> acc) None in

(* Pass the premises as new goals. Replace the former toberewritten hypothesis to the new rewritten one *)
  let recreate_tasks lp_new =
    match lp_new with
    | None -> raise (Arg_trans "recreate_tasks")
    | Some (lp, new_term) ->
      let trans_rewriting = Trans.decl (fun d -> match d.d_node with
        | Dprop (p, pr, _t) when (Ident.id_equal pr.pr_name h1.pr_name && (p = Paxiom || p = Pgoal)) ->
          [new_term]
        | _ -> [d]) None in
      let list_par = List.map (fun e -> Trans.decl (fun d -> match d.d_node with
        | Dprop (p, pr, _t) when (Ident.id_equal pr.pr_name h1.pr_name && p = Paxiom) ->
          [d]
        | Dprop (Pgoal, _, _) ->
          [create_prop_decl Pgoal (Decl.create_prsymbol (gen_ident "G")) e]
        | _ -> [d] ) None) lp in
      Trans.par (trans_rewriting :: list_par) in

  (* Composing previous functions *)
  Trans.bind (Trans.bind found_eq lp_new) recreate_tasks

let rewrite_rev = rewrite false

let rewrite = rewrite true

(* Replace occurences of t1 with t2 in h *)
let replace t1 t2 h =
  if not (Ty.ty_equal (t_type t1) (t_type t2)) then
    raise (Arg_trans_term ("replace", Some t1, Some t2))
  else
    (* Create a new goal for equality of the two terms *)
    let g = Decl.create_prop_decl Decl.Pgoal (create_prsymbol (gen_ident "G")) (t_app_infer ps_equ [t1; t2]) in
    let ng = Trans.goal (fun _ _ -> [g]) in
    let g = Trans.decl (fun d ->
      match d.d_node with
      | Dprop (p, pr, t) when (Ident.id_equal pr.pr_name h.pr_name && (p = Paxiom || p = Pgoal)) ->
          [create_prop_decl p pr (replace true t1 t2 t)]
      | _ -> [d]) None in
    Trans.par [g; ng]


let is_good_type t ty =
  try (Term.t_ty_check t (Some ty); true) with
  | _ -> false

let induction env x bound =
  let th = Env.read_theory env ["int"] "Int" in
  let le_int = Theory.ns_find_ls th.Theory.th_export ["infix <="] in
  let plus_int = Theory.ns_find_ls th.Theory.th_export ["infix +"] in
  let one_int = Term.t_const (Number.ConstInt (Number.int_const_dec "1")) in

  if (not (is_good_type x Ty.ty_int) || not (is_good_type bound Ty.ty_int)) then
    raise (Arg_trans "induction")
  else
    let lsx = match x.t_node with
    | Tvar lsx -> lsx.vs_name
    | Tapp (lsx, []) -> lsx.ls_name
    | _ -> raise (Arg_trans "induction") in

  let le_bound = Trans.decl (fun d -> match d.d_node with
    | Dprop (Pgoal, _pr, _t) ->
        let nt = Term.t_app_infer le_int [x; bound] in
        let pr = create_prop_decl Paxiom (Decl.create_prsymbol (gen_ident "H")) nt in
        [pr; d]
    | _ -> [d]) None in

  let x_is_passed = ref false in
  let ge_bound =
    Trans.decl (fun d -> match d.d_node with
    | Dparam (ls) when (Ident.id_equal lsx ls.ls_name) ->
        (x_is_passed := true; [d])
    | Dprop (Pgoal, pr, t) ->
        if not (!x_is_passed) then
          raise (Arg_trans "induction")
        else
          let x_ge_bound_t = t_app_infer le_int [bound; x] in
          let x_ge_bound =
            create_prop_decl Paxiom (Decl.create_prsymbol (gen_ident "H")) x_ge_bound_t in
          let new_pr = create_prsymbol (gen_ident "G") in
          let new_goal = create_prop_decl Pgoal new_pr
              (replace_in_term x (t_app_infer plus_int [x; one_int]) t) in
          [x_ge_bound; create_prop_decl Paxiom pr t; new_goal]
    | Dprop (p, pr, t) ->
        if !x_is_passed then [create_prop_decl p pr (replace_in_term x (t_app_infer plus_int [x; one_int]) t)] else [d]
    (* TODO | Dlogic l ->
        if !x_is_passed then replace things inside and rebuild it else
        [d]*)
    | _ -> [d]) None in
  Trans.par [le_bound; ge_bound]

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
let () = register_transform_with_args_l ~desc:"left to right rewrite of first hypothesis into the second" "rewrite"
    (wrap_l (Tprsymbol (Tprsymbol Ttrans_l)) (rewrite))
let () = register_transform_with_args_l ~desc:"right to left rewrite of first hypothesis into the second" "rewrite_rev"
    (wrap_l (Tprsymbol (Tprsymbol Ttrans_l)) (rewrite_rev))
let () = register_transform_with_args_l ~desc:"replace occurences of first term with second term in given hypothesis/goal" "replace"
    (wrap_l (Tterm (Tterm (Tprsymbol Ttrans_l))) (replace))
let () = register_transform_with_args_l ~desc:"induction on int" "induction"
    (wrap_l (Tenv (Tterm (Tterm Ttrans_l))) (induction))
