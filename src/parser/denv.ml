
open Format
open Pp
open Util
open Ptree
open Ident
open Ty
open Term
open Theory

type error = 
  | UnboundNamespace of string
  | UnboundType of string
  | UnboundSymbol of string
  | AnyMessage of string
  | TypeArity of qualid * int * int

exception Error of error

let error ?loc e = match loc with
  | None -> raise (Error e)
  | Some loc -> raise (Loc.Located (loc, Error e))

let errorm ?loc f =
  let buf = Buffer.create 512 in
  let fmt = Format.formatter_of_buffer buf in
  Format.kfprintf 
    (fun _ -> 
       Format.pp_print_flush fmt ();
       let s = Buffer.contents buf in
       Buffer.clear buf;
       error ?loc (AnyMessage s))
    fmt f

let rec print_qualid fmt = function
  | Qident s -> fprintf fmt "%s" s.id
  | Qdot (m, s) -> fprintf fmt "%a.%s" print_qualid m s.id

let report fmt = function
  | UnboundNamespace s ->
      fprintf fmt "unbound namespace %s" s
  | UnboundType s ->
       fprintf fmt "Unbound type '%s'" s
  | UnboundSymbol s ->
       fprintf fmt "Unbound symbol '%s'" s
  | AnyMessage s ->
      fprintf fmt "%s" s
  | TypeArity (id, a, n) ->
      fprintf fmt "@[The type %a expects %d argument(s),@ " print_qualid id a;
      fprintf fmt "but is applied to %d argument(s)@]" n


(** types with destructive type variables *)

type dty =
  | Tyvar of type_var
  | Tyapp of tysymbol * dty list
      
and type_var = { 
  tag : int; 
  user : bool;
  tvsymbol : tvsymbol;
  mutable type_val : dty option;
  type_var_loc : loc option;
}

let rec print_dty fmt = function
  | Tyvar { type_val = Some t } ->
      print_dty fmt t
  | Tyvar { type_val = None; tvsymbol = v } ->
      fprintf fmt "'%s" v.tv_name.id_short
  | Tyapp (s, []) ->
      fprintf fmt "%s" s.ts_name.id_short
  | Tyapp (s, [t]) -> 
      fprintf fmt "%a %s" print_dty t s.ts_name.id_short
  | Tyapp (s, l) -> 
      fprintf fmt "(%a) %s" 
	(print_list comma print_dty) l s.ts_name.id_short

let create_ty_decl_var =
  let t = ref 0 in
  fun ?loc ~user tv -> 
    incr t; 
    { tag = !t; user = user; tvsymbol = tv; type_val = None;
      type_var_loc = loc }

let rec occurs v = function
  | Tyvar { type_val = Some t } -> occurs v t
  | Tyvar { tag = t; type_val = None } -> v.tag = t
  | Tyapp (_, l) -> List.exists (occurs v) l

(* destructive type unification *)
let rec unify t1 t2 = match t1, t2 with
  | Tyvar { type_val = Some t1 }, _ ->
      unify t1 t2
  | _, Tyvar { type_val = Some t2 } ->
      unify t1 t2
  | Tyvar v1, Tyvar v2 when v1.tag = v2.tag ->
      true
	(* instantiable variables *)
  | Tyvar ({user=false} as v), t
  | t, Tyvar ({user=false} as v) ->
      not (occurs v t) && (v.type_val <- Some t; true)
	(* recursive types *)
  | Tyapp (s1, l1), Tyapp (s2, l2) ->
      s1 == s2 && List.length l1 = List.length l2 &&
	  List.for_all2 unify l1 l2
  | Tyapp _, _ | _, Tyapp _ ->
      false
	(* other cases *)
  | Tyvar {user=true; tag=t1}, Tyvar {user=true; tag=t2} -> 
      t1 = t2

(* intermediate types -> types *)
let rec ty_of_dty = function
  | Tyvar { type_val = Some t } ->
      ty_of_dty t
  | Tyvar { type_val = None; user = false; type_var_loc = loc } ->
      errorm ?loc "undefined type variable"
  | Tyvar { tvsymbol = tv } ->
      Ty.ty_var tv
  | Tyapp (s, tl) ->
      Ty.ty_app s (List.map ty_of_dty tl)


(** Destructive typing environment, that is
    environment + local variables.
    It is only local to this module and created with [create_denv] below. *)

type denv = { 
  th : theory_uc; (* the theory under construction *)
  utyvars : (string, type_var) Hashtbl.t; (* user type variables *)
  dvars : dty Mstr.t; (* local variables, to be bound later *)
}

let create_denv th = { 
  th = th; 
  utyvars = Hashtbl.create 17; 
  dvars = Mstr.empty;
}

let find_user_type_var x env =
  try
    Hashtbl.find env.utyvars x
  with Not_found ->
    (* TODO: shouldn't we localize this ident? *)
    let v = create_tvsymbol (id_fresh x) in
    let v = create_ty_decl_var ~user:true v in
    Hashtbl.add env.utyvars x v;
    v
 
(* Specialize *)

let find_type_var ~loc env tv =
  try
    Htv.find env tv
  with Not_found ->
    let v = create_ty_decl_var ~loc ~user:false tv in
    Htv.add env tv v;
    v
 
let rec specialize ~loc env t = match t.ty_node with
  | Ty.Tyvar tv -> 
      Tyvar (find_type_var ~loc env tv)
  | Ty.Tyapp (s, tl) ->
      Tyapp (s, List.map (specialize ~loc env) tl)

(** generic find function using a path *)

let find_local_namespace {id=x; id_loc=loc} ns = 
  try Mnm.find x ns.ns_ns
  with Not_found -> error ~loc (UnboundNamespace x)

let rec find_namespace q ns = match q with
  | Qident t -> find_local_namespace t ns
  | Qdot (q, t) -> let ns = find_namespace q ns in find_local_namespace t ns

let rec find f q ns = match q with
  | Qident x -> f x ns
  | Qdot (m, x) -> let ns = find_namespace m ns in f x ns

(** specific find functions using a path *)

let find_local_tysymbol {id=x; id_loc=loc} ns = 
  try Mnm.find x ns.ns_ts
  with Not_found -> error ~loc (UnboundType x)

let find_tysymbol_ns p ns =
  find find_local_tysymbol p ns

let find_tysymbol p th = 
  find_tysymbol_ns p (get_namespace th)

let find_lsymbol {id=x; id_loc=loc} ns = 
  try Mnm.find x ns.ns_ls
  with Not_found -> error ~loc (UnboundSymbol x)

let find_lsymbol_ns p ns = 
  find find_lsymbol p ns

let find_lsymbol p th = 
  find_lsymbol_ns p (get_namespace th)

let find_prop {id=x; id_loc=loc} ns = 
  try Mnm.find x ns.ns_pr
  with Not_found -> errorm ~loc "unbound formula %s" x

let find_prop_ns p ns =
  find find_prop p ns

let find_prop p th =
  find_prop_ns p (get_namespace th)

(** specialize functions *)

let specialize_tysymbol ~loc x env =
  let s = find_tysymbol x env.th in
  let env = Htv.create 17 in
  s, List.map (find_type_var ~loc env) s.ts_args
	
let specialize_lsymbol ~loc s =
  let tl = s.ls_args in
  let t = s.ls_value in
  let env = Htv.create 17 in
  s, List.map (specialize ~loc env) tl, option_map (specialize ~loc env) t

(* parsed types -> intermediate types *)

let rec qloc = function
  | Qident x -> x.id_loc
  | Qdot (m, x) -> Loc.join (qloc m) x.id_loc

let rec type_inst s ty = match ty.ty_node with
  | Ty.Tyvar n -> Mtv.find n s
  | Ty.Tyapp (ts, tyl) -> Tyapp (ts, List.map (type_inst s) tyl)

let rec dty env = function
  | PPTtyvar {id=x} -> 
      Tyvar (find_user_type_var x env)
  | PPTtyapp (p, x) ->
      let loc = qloc x in
      let ts, tv = specialize_tysymbol ~loc x env in
      let np = List.length p in
      let a = List.length tv in
      if np <> a then error ~loc (TypeArity (x, a, np));
      let tyl = List.map (dty env) p in
      match ts.ts_def with
	| None -> 
	    Tyapp (ts, tyl)
	| Some ty -> 
	    let add m v t = Mtv.add v t m in
            let s = List.fold_left2 add Mtv.empty ts.ts_args tyl in
	    type_inst s ty

