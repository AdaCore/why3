
open Trans

let rec dup n x = if n = 0 then [] else x::(dup (n-1) x)

let duplicate args task =
  match args with
    | [TAint n] -> dup n task
    | _ -> failwith "wrong arguments for duplicate"


let case _t task = (* Sylvain *)
  [task;task]
  (* TODO : from task [delta |- G] , build the tasks [delta, t] |- G] and [delta, not t | - G] *)


let cut _t task = (* Sylvain *)
  [task;task]
  (* TODO : from task [delta |- G] , build the tasks [delta] |- t] and [delta, t | - G] *)

let exists _t task = (* ? *)
  [task;task]
  (* TODO : from task [delta |- exists x. G] , build the task [delta] |- G[x -> t]] *)

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


let () = register_transform_with_args ~desc:"test case" "case" case'
let () = register_transform_with_args ~desc:"test duplicate" "duplicate" duplicate
