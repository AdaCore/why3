open Term

module Env : sig
  type t
  val empty : t
  val add : t -> Name.t -> Ty.scheme -> t
  val get : t -> Name.t -> Ty.scheme
  val mem : t -> Name.t -> bool
end = struct
  module M = Name.M
  type t = Ty.scheme M.t
  let add env x t = M.add x t env
  let get env x = M.find x env
  let mem env x = M.mem x env
  let empty = M.empty
end

let rec infer_term env t = 
  match t.node with
  | BVar _ -> failwith "encountered bound variable"
  | Var n -> 
      begin try Obj.magic (Env.get env n)
      with Not_found -> failwith "unknown variable" end
  | App (t1,t2) -> 
      let ty1 = infer_term env t1 in
      let ta,tb = Ty.split ty1 in
      check_term env ta t2; tb
  | Tuple (t1,t2) ->
      let ty1 = infer_term env t1 in
      let ty2 = infer_term env t2 in
      Ty.tuple ty1 ty2
  | Lam (ty,b) -> 
      let n,t = open_lam b in
      let env = Env.add env n (Ty.as_scheme ty) in
      let ty' = infer_term env t in
      Ty.arrow ty ty'
  | Case (t1,c) -> 
      let ty1 = infer_term env t1 in
      let p,nl,t2 = open_case c in
      let env = check_pattern env ty1 p in
      infer_term env t2

and check_term env ty t = 
  let t = infer_term env t in
  if Ty.equal t ty then () else failwith "expected term of other type"

and check_pattern env ty p = 
  match p with
  | PBVar _ -> assert false
  | PVar n -> 
      if not (Env.mem env n) then Env.add env n (Ty.as_scheme ty)
      else failwith "nonlinear pattern"
  | Wildcard -> env
  | PTuple (p1,p2) ->
      let ty1,ty2 = Ty.tuple_split ty in
      let env = check_pattern env ty1 p1 in
      check_pattern env ty2 p2

let check_polyterm env ty p = 
  let _,t = open_polyterm p in
  check_term env ty t

let decl env d = 
  match d with
  | Logic (n,s) -> Env.add env n s
  | Formula p -> 
      check_polyterm env Ty.prop p;
      env

let theory dl =
  ignore (List.fold_left decl Env.empty dl)
