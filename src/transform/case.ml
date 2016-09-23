
open Trans
open Term
open Decl
open Theory

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

(* Transform (exists v, f) into f[x/v] *)
let subst_exist t x =
  match t.t_node with
  | Tquant (Texists, tq) ->
      let (vsl, tr, te) = t_open_quant tq in
      (match vsl with
      | hdv :: tl ->
          (try
            (let new_t = t_subst_single hdv x te in
              t_exists_close tl tr new_t)
          with
          | Ty.TypeMismatch (_ty1, _ty2) -> failwith "type mismatch") (* TODO match errors *)
      | [] -> failwith "no")
  | _ -> failwith "term do not begin with exists"

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

let remove _name task =
  [task;task]
  (* TODO :from task [delta, name:A |- G]  build the task [delta |- G] *)

let simple_apply _name _t task = (* ? *)
  [task;task]
  (* TODO : from task [delta, name:forall x.A |- G,
     build the task [delta,name:forall x.A,name':A[x -> t]] |- G] *)

let apply _name task = (* ? *)
  [task;task]
  (* TODO : from task [delta, name:forall x.A->B |- G,
     build the task [delta,name:forall x.A->B] |- A[x -> t]] ou t est tel que B[x->t] = G *)

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

let () = register_transform_with_args ~desc:"test case" "case" case'
let () = register_transform_with_args ~desc:"test cut" "cut" cut'
let () = register_transform_with_args ~desc:"test exists" "exists" exists'
let () = register_transform_with_args ~desc:"test duplicate" "duplicate" duplicate
