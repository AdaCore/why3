
type 'n types =
  | TypeVar of 'n
  | DeclaredType of 'n

type 'n constructor =
  | Var
  | BCons of 'n * ( 'n * 'n types list) list * 'n types list

type 'n typedef =
  | TypeAssumption of 'n * 'n list
  | TypeDefinition of 'n * 'n constructor list * 'n list

type 'n decls = { var_parameters : 'n list ;
  binder_types : 'n typedef list }

open Priv

module IntO = struct
  type t = int
  let compare (x:int) (y:int) = compare x y
end

module CName = Priv.Make(IntO)
module TName = CName
module VName = CName
module IMap = Map.Make(IntO)
module TMap = Map.Make(struct type t = TName.t
  let compare x y =
    compare (x:TName.t:>int) (y:TName.t:>int) end)

type internal_types =
  | ITVar of VName.t
  | ITDecl of TName.t

type constr =
  CName.t * (TName.t * internal_types list) list * internal_types list

type constructors = {
  var_present : bool ;
  cons_list : constr list
}

type internal_typedef =
  | ITypeDef of constructors * TName.t list
  | ITypeAssumption of TName.t list

type internal_decl =
  { var_params : VName.t list ;
    type_decls : internal_typedef TMap.t ;
    names : string IMap.t ;
    sccg : TName.t list list }

let type_name dm (tn:TName.t) = IMap.find (tn:>int) dm.names
let var_name = type_name
let cons_name = type_name
let type_def dm tn = TMap.find tn dm.type_decls
let def_binder_vars = function
  | ITypeDef (_,v) | ITypeAssumption v -> v
let binder_vars dm tn = def_binder_vars (type_def dm tn)
  



