
(* Input declarations *)

type 'n types =
  | TypeVar of 'n
  | DeclaredType of 'n

type 'n constructor =
  | Var
  | BCons of 'n * ( 'n * 'n types list) list * 'n types list
    (* BCons (C , [ t,u ; t2,u2 ] [ v1 ; v2 ; v3 ] :
       C : [ x_t : u1 . [ x_t2 : u2 . v1 v2 v3 ] ].
       x_{t} is bound at the right as a variable for declared type t. *)

type 'n typedef =
  (* TypeAssumption (t,[v_1...v_n] : assume
     type t using variables in types v_1...v_n. *)
  | TypeAssumption of 'n * 'n list
  (* Add definition. The list may be incomplete/contains variables
     not really used. In the second case, the variables will be added. *)
  | TypeDefinition of 'n * 'n constructor list * 'n list

type 'n decls = { var_parameters : 'n list ;
  binder_types : 'n typedef list }

module CName : Priv.S with type base = int
module TName : Priv.S with type base = int
module VName : Priv.S with type base = int
module IMap : Map.S with type key = int
module TMap : Map.S with type key = TName.t

(* Processed declarations. *)

type internal_types =
  | ITVar of VName.t
  | ITDecl of TName.t

type constr =
  CName.t * (TName.t * internal_types list) list * internal_types list

type constructors = {
  var_present : bool ;
  cons_list : constr list
}

(* Here, the variables sets should be complete,
   i.e the set of variable declared by a type is
   exactly the union of variable sets declared by types used
   in constructor,+ itself if it contain var,+ the bound variables. *)

type internal_typedef =
  | ITypeDef of constructors * TName.t list
  | ITypeAssumption of TName.t list

type internal_decl =
  { (* Polymorphic common parameters *)
    var_params : VName.t list ;
    (* type declarations map. *)
    type_decls : internal_typedef TMap.t ;
    (* real names. *)
    names : string IMap.t ;
    (* topologically increasing list of scc. A type is considered dependent on
       another iff its definition depend on the other OR one of the binding
       parameter correspond to the other type. Interestingly, every type in
       a scc have same type parameters (for coq translation).  *)
    sccg : TName.t list list }

(* Interrogators *)

val type_name : internal_decl -> TName.t -> string
val var_name : internal_decl -> VName.t -> string
val cons_name : internal_decl -> CName.t -> string
val type_def : internal_decl -> TName.t -> internal_typedef
val def_binder_vars : internal_typedef -> TName.t list
val binder_vars : internal_decl -> TName.t -> TName.t list



