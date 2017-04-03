open Trans
open Term
open Decl
open Theory
open Task
open Args_wrapper
open Reduction_engine

exception Arg_trans of string
exception Arg_trans_term of (string * Term.term * Term.term)
exception Arg_trans_pattern of (string * pattern * pattern)
exception Arg_trans_type of (string * Ty.ty * Ty.ty)
exception Arg_bad_hypothesis of (string * Term.term)
exception Cannot_infer_type of string

let debug_matching = Debug.register_info_flag "print_match"
  ~desc:"Print@ terms@ that@ were@ not@ successfully@ matched@ by@ ITP@ tactic@ apply."

let rec dup n x = if n = 0 then [] else x::(dup (n-1) x)

let gen_ident = Ident.id_fresh

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

(* From task [delta |- G] , build the tasks [delta, t | - G] and [delta] |- t] *)
let cut t name =
  let name =
    match name with
    | Some name -> name
    | None -> "h"
  in
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
      | Ty.TypeMismatch (ty1, ty2) ->
          raise (Arg_trans_type ("subst_quant", ty1, ty2)))
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

(* From task [delta |- exists x. G] and term t, build
   the task  [delta |- G[x -> t]].
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
  let r = ref [] in
  Trans.decl
    (fun d ->
      match d.d_node with
      | Dprop (pk, dpr, ht) when Ident.id_equal dpr.pr_name pr.pr_name ->
          let t_subst = subst_forall ht t in
          let new_pr = create_prsymbol (Ident.id_clone dpr.pr_name) in
          let new_decl = create_prop_decl pk new_pr t_subst in
          r := [new_decl];
          [d]
      | Dprop (Pgoal, _, _) -> !r @ [d]
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


(* Apply:
   1) takes the hypothesis and introduce parts of it to keep only the last
      element of the implication. It gathers the premises and variables in a
      list.
   2) try to find a good substitution for the list of variables so that last
      element of implication is equal to the goal.
   3) generate new goals corresponding to premises with variables instantiated
      with values found in 2).
 *)
let apply pr : Task.task Trans.tlist = Trans.store (fun task ->
  let name = pr.pr_name in
  let g, task = Task.task_separate_goal task in
  let g = term_decl g in
  let d = find_hypothesis name task in
  if d = None then raise (Arg_hyp_not_found "apply");
  let d = Opt.get d in
  let t = term_decl d in
  let (lp, lv, nt) = intros t in
  let (_ty, subst) = try first_order_matching lv [nt] [g] with
  | Reduction_engine.NoMatch (Some (t1, t2)) ->
      (if (Debug.test_flag debug_matching) then
        Format.printf "Term %a and %a can not be matched. Failure in matching@."
          Pretty.print_term t1 Pretty.print_term t2
      else ()); raise (Arg_trans_term ("apply", t1, t2))
  | Reduction_engine.NoMatchpat (Some (p1, p2)) ->
      (if (Debug.test_flag debug_matching) then
        Format.printf "Term %a and %a can not be matched. Failure in matching@."
          Pretty.print_pat p1 Pretty.print_pat p2
      else ()); raise (Arg_trans_pattern ("apply", p1, p2))
  | Reduction_engine.NoMatch None -> raise (Arg_trans ("apply"))
  in
  let inst_nt = t_subst subst nt in
  if (Term.t_equal_nt_nl inst_nt g) then
    let nlp = List.map (t_subst subst) lp in
    let lt = List.map (fun ng -> Task.add_decl task (create_prop_decl Pgoal
                          (create_prsymbol (gen_ident "G")) ng)) nlp in
    lt
  else
    raise (Arg_trans_term ("apply", inst_nt, g)))

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
  (* is_replced is common to the whole execution of replace_subst. Once an
     occurence is found, it changes to Some (s) so that only one instanciation
     is rewrritten during execution *)
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
      | Reduction_engine.NoMatchpat (Some (p1, p2)) ->
        (if (Debug.test_flag debug_matching) then
          Format.printf "Term %a and %a can not be matched. Failure in matching@."
          Pretty.print_pat p1 Pretty.print_pat p2
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
  | None -> raise (Arg_trans "matching/replace")
  | Some subst ->
    (List.map (t_subst subst) lp, t)

let rewrite_in rev h h1 =
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
          | _ -> raise (Arg_bad_hypothesis ("rewrite", f))) in
          Some (lp, lv, t1, t2)
      | _ -> acc) None in
  (* Return instantiated premises and the hypothesis correctly rewritten *)
  let lp_new found_eq =
    match found_eq with
    | None -> raise (Arg_hyp_not_found "rewrite")
    | Some (lp, lv, t1, t2) ->
      fold (fun d acc ->
        match d.d_node with
        | Dprop (p, pr, t)
            when (Ident.id_equal pr.pr_name h1.pr_name &&
                 (p = Paxiom || p = Pgoal)) ->
          let lp, new_term = replace_subst lp lv t1 t2 t in
            Some (lp, create_prop_decl p pr new_term)
        | _ -> acc) None in
  (* Pass the premises as new goals. Replace the former toberewritten
     hypothesis to the new rewritten one *)
  let recreate_tasks lp_new =
    match lp_new with
    | None -> raise (Arg_trans "recreate_tasks")
    | Some (lp, new_term) ->
      let trans_rewriting =
        Trans.decl (fun d -> match d.d_node with
        | Dprop (p, pr, _t)
            when (Ident.id_equal pr.pr_name h1.pr_name &&
                 (p = Paxiom || p = Pgoal)) ->
          [new_term]
        | _ -> [d]) None in
      let list_par =
        List.map
          (fun e ->
            Trans.decl (fun d -> match d.d_node with
            | Dprop (p, pr, _t)
              when (Ident.id_equal pr.pr_name h1.pr_name &&
                    p = Paxiom) ->
                [d]
            | Dprop (Pgoal, _, _) ->
                [create_prop_decl Pgoal (Decl.create_prsymbol (gen_ident "G")) e]
            | _ -> [d] )
          None) lp in
      Trans.par (trans_rewriting :: list_par) in

  (* Composing previous functions *)
  Trans.bind (Trans.bind found_eq lp_new) recreate_tasks

let find_target_prop h : prsymbol trans =
  Trans.store (fun task ->
               match h with
                 | Some pr -> pr
                 | None -> Task.task_goal task)

let rewrite rev h h1 = Trans.bind (find_target_prop h1) (rewrite_in (not rev) h)

(* Replace occurences of t1 with t2 in h *)
let replace t1 t2 h =
  if not (Ty.ty_equal (t_type t1) (t_type t2)) then
    raise (Arg_trans_term ("replace", t1, t2))
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

let induction x bound env =
  let th = Env.read_theory env ["int"] "Int" in
  let le_int = Theory.ns_find_ls th.Theory.th_export ["infix <="] in
  let plus_int = Theory.ns_find_ls th.Theory.th_export ["infix +"] in
  let one_int =
    Term.t_const (Number.ConstInt (Number.int_const_dec "1")) Ty.ty_int in

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

let create_constant ty =
  let fresh_name = Ident.id_fresh "x" in
  let ls = create_lsymbol fresh_name [] (Some ty) in
  (ls, create_param_decl ls)

let rec return_list list_types =
  match list_types with
  | [] -> []
  | hd :: tl -> create_constant hd :: return_list tl

let rec build_decls cls x =
  match cls with
  | [] -> []
  | (cs, _) :: tl ->
      let l = return_list cs.ls_args in
      let ht = t_equ x
           (t_app_infer cs (List.map (fun x -> t_app_infer (fst x) []) l)) in
      let h = Decl.create_prsymbol (gen_ident "h") in
      let new_hyp = Decl.create_prop_decl Decl.Paxiom h ht in
      ((List.map snd l) @ [new_hyp]) :: build_decls tl x



(* This tactic acts on a term of algebraic type. It introduces one
   new goal per constructor of the type and introduce corresponding
   variables. It also introduce the equality between the term and
   its destruction in the context.
 *)
(* TODO does not work with polymorphic type *)
let destruct_alg (x: term) : Task.task Trans.tlist =
  let ty = x.t_ty in
  let r = ref [] in
  match ty with
  | None -> raise (Cannot_infer_type "destruct")
  | Some ty ->
    begin
      match ty.Ty.ty_node with
      | Ty.Tyvar _ -> raise (Cannot_infer_type "destruct")
      | Ty.Tyapp (ts, _) ->
        Trans.decl_l (fun d ->
          match d.d_node with
          | Ddata dls ->
              (try
                (let cls = List.assoc ts dls in
                r := build_decls cls x;
                [[d]]
                )
              with Not_found -> [[d]])
          | Dprop (Pgoal, _, _) ->
              if !r = [] then [[d]] else List.map (fun x -> x @ [d]) !r
          | _ -> [[d]]) None
    end

(* Destruct the head term of an hypothesis if it is either
   conjunction, disjunction or exists *)
let destruct pr : Task.task Trans.tlist =
  Trans.decl_l (fun d ->
    match d.d_node with
    | Dprop (Paxiom, dpr, ht) when Ident.id_equal dpr.pr_name pr.pr_name ->
      begin
        match ht.t_node with
        | Tbinop (Tand, t1, t2) ->
          let new_pr1 = create_prsymbol (Ident.id_clone dpr.pr_name) in
          let new_decl1 = create_prop_decl Paxiom new_pr1 t1 in
          let new_pr2 = create_prsymbol (Ident.id_clone dpr.pr_name) in
          let new_decl2 = create_prop_decl Paxiom new_pr2 t2 in
          [[new_decl1;new_decl2]]
        | Tbinop (Tor, t1, t2) ->
          let new_pr1 = create_prsymbol (Ident.id_clone dpr.pr_name) in
          let new_decl1 = create_prop_decl Paxiom new_pr1 t1 in
          let new_pr2 = create_prsymbol (Ident.id_clone dpr.pr_name) in
          let new_decl2 = create_prop_decl Paxiom new_pr2 t2 in
          [[new_decl1];[new_decl2]]
        | Tquant (Texists, tb) ->
          begin
            let (vsl, tr, te) = Term.t_open_quant tb in
            match vsl with
            | x :: tl ->
                let ls = create_lsymbol (Ident.id_clone x.vs_name) [] (Some x.vs_ty) in
                let tx = fs_app ls [] x.vs_ty in
                let x_decl = create_param_decl ls in
                (try
                  let part_t = t_subst_single x tx te in
                  let new_t = t_quant_close Texists tl tr part_t in
                  let new_pr = create_prsymbol (Ident.id_clone dpr.pr_name) in
                  let new_decl = create_prop_decl Paxiom new_pr new_t in
                  [[d; x_decl; new_decl]]
                with
                | Ty.TypeMismatch (ty1, ty2) ->
                    raise (Arg_trans_type ("destruct_exists", ty1, ty2)))
            | [] -> raise (Arg_trans ("destruct_exists"))
          end
        | _ -> raise (Arg_trans ("destruct"))
      end
    | _ -> [[d]]) None


(* TODO to be done ... *)
open Ident
open Ty
open Term
open Decl

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

let t_replace_app unf ls_defn t =
  let (vl, tls) = ls_defn in
  match t.t_node with
  | Tapp (ls, tl) when ls_equal unf ls ->
      let mvs =
        List.fold_left2 (fun acc (v: vsymbol) (t: term) ->
          Mvs.add v t acc) Mvs.empty vl tl in
      t_subst mvs tls
  | _ -> t

let t_ls_replace ls ls_defn t =
  t_replace_app ls ls_defn (t_map (t_replace_app ls ls_defn) t)

let unfold unf h =
  let r = ref None in
  Trans.decl
    (fun d ->
      match d.d_node with
        (* Do not work on mutually recursive functions *)
      | Dlogic [(ls, ls_defn)] when ls_equal ls unf ->
          r := Some (open_ls_defn ls_defn);
          [d]
      | Dprop (k, pr, t) when pr_equal h pr  ->
        begin
          match !r with
          | None -> [d]
          | Some ls_defn ->
              let t = t_ls_replace unf ls_defn t in
              let new_decl = create_prop_decl k pr t in
              [new_decl]
        end
      | _ -> [d]) None

let () = wrap_and_register ~desc:"unfold ls pr: unfold logic symbol ls in hypothesis pr. Experimental." (* TODO *)
    "unfold"
    (Tlsymbol (Tprsymbol Ttrans)) unfold

let () = wrap_and_register ~desc:"intros n"
    "intros"
    (Tint Ttrans) introduce_premises

let use_th th =
  Trans.add_tdecls [Theory.create_use th]

let () = wrap_and_register
    ~desc:"case <term> [name] generates hypothesis 'name: term' in a first goal and 'name: ~ term' in a second one."
    "case"
    (Tformula (Topt ("as",Tstring Ttrans_l))) case

let () = wrap_and_register
    ~desc:"cut <term> [name] makes a cut with hypothesis 'name: term'"
    "cut"
    (Tformula (Topt ("as",Tstring Ttrans_l))) cut

let () = wrap_and_register
    ~desc:"exists <term> substitutes the variable quantified by exists with term"
    "exists"
    (Tterm Ttrans) exists

let () = wrap_and_register
    ~desc:"remove <prop> removes hypothesis named prop"
    "remove"
    (Tprsymbol Ttrans) remove

let () = wrap_and_register
    ~desc:"instantiate <prop> <term> generates a new hypothesis with first quantified variables of prop replaced with term "
    "instantiate"
    (Tprsymbol (Tterm Ttrans)) instantiate

let () = wrap_and_register
    ~desc:"apply <prop> applies prop to the goal" "apply"
    (Tprsymbol Ttrans_l) apply

let () = wrap_and_register
    ~desc:"duplicate <int> duplicates the goal int times" "duplicate"
    (Tint Ttrans_l) (fun x -> Trans.store (dup x))

let () = wrap_and_register
    ~desc:"use_th <theory> imports the theory" "use_th"
    (Ttheory Ttrans) use_th

let _ = wrap_and_register
    ~desc:"rewrite [<-] <name> [in] <name2> rewrites equality defined in name into name2" "rewrite"
    (Toptbool ("<-",(Tprsymbol (Topt ("in", Tprsymbol Ttrans_l))))) rewrite
  (* register_transform_with_args_l *)
  (*   ~desc:"rewrite [<-] <name> [in] <name2> rewrites equality defined in name into name2" *)
  (*   "rewrite" *)
  (*   (wrap_l (Toptbool ("<-",(Tprsymbol (Topt ("in", Tprsymbol Ttrans_l))))) rewrite) *)

let () = wrap_and_register
    ~desc:"replace <term1> <term2> <name> replaces occcurences of term1 by term2 in prop name"
    "replace"
    (Tterm (Tterm (Tprsymbol Ttrans_l))) replace

let () = wrap_and_register
    ~desc:"induction <term1> <term2> performs induction on int term1 from int term2"
    "induction"
    (Tterm (Tterm Tenvtrans_l)) induction

let () = wrap_and_register ~desc:"destruct <name> destructs the head constructor of hypothesis name"
    "destruct" (Tprsymbol Ttrans_l) destruct

let () = wrap_and_register ~desc:"destruct <name> destructs as an algebraic type"
    "destruct_alg" (Tterm Ttrans_l) destruct_alg
