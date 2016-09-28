
open Trans
open Term
open Decl
open Theory
open Task

let rec dup n x = if n = 0 then [] else x::(dup (n-1) x)

let duplicate args task =
  match args with
    | [TAint n] -> dup n task
    | _ -> failwith "wrong arguments for duplicate"

(* From task [delta |- G] and term t, build the tasks:
   [delta, t] |- G] and [delta, not t | - G] *)
let case t task =
  let h = Decl.create_prsymbol (Ident.id_fresh "h") in
  let hnot = Decl.create_prsymbol (Ident.id_fresh "hnot") in
  let t_not_decl = Decl.create_prop_decl Decl.Paxiom hnot (Term.t_not t) in
  let t_decl = Decl.create_prop_decl Decl.Paxiom h t in
  List.map (fun f -> Trans.apply f task) [Trans.add_decls [t_decl]; Trans.add_decls [t_not_decl]]

(* From task [delta |- G] , build the tasks [delta, t | - G] and [delta] |- t] *)
let cut t task =
  let g, task = Task.task_separate_goal task in
  let h = Decl.create_prsymbol (Ident.id_fresh "h") in
  let g_t = Decl.create_prop_decl Decl.Pgoal h t in
  let h_t = Decl.create_prop_decl Decl.Paxiom h t in
  let goal_cut = Task.add_decl task g_t in
  let goal = Task.add_tdecl (Task.add_decl task h_t) g in
  [goal; goal_cut]

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

(* From task [delta |- exists x. G] and term t, build the task [delta] |- G[x -> t]]
   Return an error if x and t are not unifiable. *)
let exists x task =
  let g, task = Task.task_separate_goal task in
  match g.td_node with
  | Decl {d_node = Dprop (_, _, t)} ->
      let t = subst_exist t x in
      let pr_goal = create_prsymbol (Ident.id_fresh "G") in
      let new_goal = Decl.create_prop_decl Decl.Pgoal pr_goal t in
      [Task.add_decl task new_goal]
  | _ -> failwith "No goal"

(* TODO ask to have functions in ident and Pretty that do something like that *)
let string_pr pr =
  ignore (Format.flush_str_formatter ());
  Pretty.print_pr Format.str_formatter pr;
  Format.flush_str_formatter()

(* Return a new task with hypothesis name removed *)
let rec remove_task_decl task (name: string) : task_hd option =
  match task with
  | Some {task_decl = {td_node = Decl {d_node = Dprop (Paxiom, pr, _)}};
          task_prev = task} when (string_pr pr = name) ->
    task
  | Some {task_decl = decl;
          task_prev = task;
          task_known = known;
          task_clone = clone;
          task_meta = meta;
          task_tag = _} ->
    (* Should create a new unique tag each time *)
    Task.mk_task decl (remove_task_decl task name) known clone meta
  | None -> None

(* TODO check if this works in particular when hypothesis names
    are extracted from same name. Seemed not to work before
  adding "print_task". To be resolved in a better way. *)
(* from task [delta, name:A |- G]  build the task [delta |- G] *)
let remove name task =
  (* Force setting of pprinter *)
  let _ = Pretty.print_task Format.str_formatter task in
  let _ = ignore (Format.flush_str_formatter ()) in
  let g, task = Task.task_separate_goal task in
  let task = remove_task_decl task name in
  [Task.add_tdecl task g]

let pr_prsymbol pr =
  match pr with
  | Decl {d_node = Dprop (_pk, pr, _t)} -> Some pr
  | _ -> None

(* Looks for the hypothesis name and return it. If not found return None *)
let find_hypothesis name task =
  let ndecl = ref None in
  let _ = task_iter (fun x -> if (
    match (pr_prsymbol x.td_node) with
    | None -> false
    | Some pr -> string_pr pr = name) then ndecl := Some x) task in
  !ndecl

(* from task [delta, name:forall x.A |- G,
     build the task [delta,name:forall x.A,name':A[x -> t]] |- G] *)
let simple_apply name t task =
  (* Force setting of pprinter *)
  let _ = Pretty.print_task Format.str_formatter task in
  let _ = ignore (Format.flush_str_formatter ()) in
  let g, task = Task.task_separate_goal task in
  let ndecl = find_hypothesis name task in
  match ndecl with
  | None -> Format.printf "Hypothesis %s not found@." name; [Task.add_tdecl task g]
  | Some decl -> (match decl.td_node with
    | Decl {d_node = Dprop (pk, _pr, ht)} ->
      let t_subst = subst_forall ht t in
      let new_pr = create_prsymbol (Ident.id_fresh name) in
      let new_decl = create_prop_decl pk new_pr t_subst in
      let task = add_decl task new_decl in
        [Task.add_tdecl task g]
    | _ -> Format.printf "Not an hypothesis@."; [Task.add_tdecl task g])

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

(* from task [delta, name:forall x.A->B |- G,
   build the task [delta,name:forall x.A->B] |- A[x -> t]] ou t est tel que B[x->t] = G *)
let apply name task =
  (* Force setting of pprinter *)
  let _ = Pretty.print_task Format.str_formatter task in
  let _ = ignore (Format.flush_str_formatter ()) in
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
               [Task.add_decl task (create_prop_decl Pgoal
                 (create_prsymbol (Ident.id_fresh "G")) new_goal)]
            else
              (Format.printf "Term substituted was %a. Should be goal was %a. Goal was %a @." Pretty.print_term x Pretty.print_term new_tb Pretty.print_term tg;
              failwith "After substitution, terms are not exactly identical")
        end
      | _ -> failwith "Not of the form forall immediately followed by implies"
    end
  | Tbinop (Timplies, _ta, _tb) -> failwith "Not implemented yet" (* TODO to be done later *)
  | _ -> failwith "Not of the form forall x. A -> B"

let case' args task  =
  match args with
  | [TAterm t] -> case t task
  | _ -> failwith "wrong arguments for case"

let cut' args task =
  match args with
  | [TAterm t] -> cut t task
  | _ -> failwith "wrong arguments for cut"

let exists' args task =
   match args with
  | [TAterm t] -> exists t task
  | _ -> failwith "wrong arguments for exists"

let remove' args task =
  match args with
  | [TAstring name] -> remove name task
  | _ -> failwith "wrong argument for remove"

let simple_apply' args task =
  match args with
  | [TAstring name; TAterm t] -> simple_apply name t task
  | _ -> failwith "wrong arguments of simple_apply"

let apply' args task =
  match args with
  | [TAstring name] -> apply name task
  | _ -> failwith "wrong arguments of simple_apply"

let () = register_transform_with_args ~desc:"test case" "case" case'
let () = register_transform_with_args ~desc:"test cut" "cut" cut'
let () = register_transform_with_args ~desc:"test exists" "exists" exists'
let () = register_transform_with_args ~desc:"test remove" "remove" remove'
let () = register_transform_with_args ~desc:"test simple_apply" "simple_apply" simple_apply'
let () = register_transform_with_args ~desc:"test apply" "apply" apply'
let () = register_transform_with_args ~desc:"test duplicate" "duplicate" duplicate
