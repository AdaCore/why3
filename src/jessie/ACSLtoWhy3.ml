(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)



let help = "Checks ACSL contracts using Why3"

let global_logic_decls_theory_name = "Global logic declarations"

let programs_module_name = "C Functions"



module Self =
  Plugin.Register
    (struct
       let name = "Jessie3"
       let shortname = "jessie3"
       let help = help
     end)


module Options = struct

end

module Enabled =
  Self.False
    (struct
       let option_name = "-jessie3"
       let help = help
     end)

open Cil_types
open Why3




(***************)
(* environment *)
(***************)

let env,config =
  try
    (* reads the Why3 config file *)
    Self.result "Loading Why3 configuration...";
    let config : Whyconf.config = Whyconf.read_config None in
    (* the [main] section of the config file *)
    let main : Whyconf.main = Whyconf.get_main config in
    let env : Env.env = Env.create_env (Whyconf.loadpath main) in
    Self.result "Why3 environment loaded.";
    env,config
  with e ->
    Self.fatal "Exception raised while reading Why3 environment:@ %a"
      Exn_printer.exn_printer e

let find th s =
  try
    Theory.ns_find_ls th.Theory.th_export [s]
  with e ->
    Self.fatal "Exception raised while loading Why3 symbol %s:@ %a"
      s Exn_printer.exn_printer e

let find_type th s =
  try
    Theory.ns_find_ts th.Theory.th_export [s]
  with e ->
    Self.fatal "Exception raised while loading Why3 type %s:@ %a"
      s Exn_printer.exn_printer e

let () = Self.result "Loading Why3 theories..."

(* int.Int theory *)
let int_type : Ty.ty = Ty.ty_int
let int_theory : Theory.theory =
  try
    Env.read_theory env ["int"] "Int"
  with e ->
    Self.fatal "Exception raised while loading int theory:@ %a"
      Exn_printer.exn_printer e

let add_int : Term.lsymbol = find int_theory "infix +"
let sub_int : Term.lsymbol = find int_theory "infix -"
let minus_int : Term.lsymbol = find int_theory "prefix -"
let mul_int : Term.lsymbol = find int_theory "infix *"
let ge_int : Term.lsymbol = find int_theory "infix >="
let le_int : Term.lsymbol = find int_theory "infix <="
let gt_int : Term.lsymbol = find int_theory "infix >"
let lt_int : Term.lsymbol = find int_theory "infix <"

let computer_div_theory : Theory.theory =
  Env.read_theory env ["int"] "ComputerDivision"
let div_int : Term.lsymbol = find computer_div_theory "div"

(* real.Real theory *)
let real_type : Ty.ty = Ty.ty_real
let real_theory : Theory.theory = Env.read_theory env ["real"] "Real"
let add_real : Term.lsymbol = find real_theory "infix +"
let sub_real : Term.lsymbol = find real_theory "infix -"
let minus_real : Term.lsymbol = find real_theory "prefix -"
let mul_real : Term.lsymbol = find real_theory "infix *"
let ge_real : Term.lsymbol = find real_theory "infix >="

(* map.Map theory *)
let map_theory : Theory.theory = Env.read_theory env ["map"] "Map"
let map_ts : Ty.tysymbol = find_type map_theory "map"
(* let map_type (t:Ty.ty) : Ty.ty = Ty.ty_app map_ts [t] *)
let map_get : Term.lsymbol = find map_theory "get"


let () = Self.result "Loading Why3 modules..."

let find_ps mo s =
  try
    Mlw_module.ns_find_ps mo.Mlw_module.mod_export [s]
  with e ->
    Self.fatal "Exception raised while loading Why3 program symbol %s:@ %a"
      s Exn_printer.exn_printer e

let find_ls mo s = find mo.Mlw_module.mod_theory s

(* ref.Ref module *)

(*
let ref_modules, ref_theories =
  try
    Env.read_library (Env.locate_library env) ["ref"]
  with e ->
    Self.fatal "Exception raised while loading ref module:@ %a"
      Exn_printer.exn_printer e

let ref_module : Mlw_module.modul = Stdlib.Mstr.find "Ref" ref_modules
*)
let ref_module : Mlw_module.modul =
  Mlw_module.read_module env ["ref"] "Ref"

let ref_type : Mlw_ty.T.itysymbol =
  Mlw_module.ns_find_its ref_module.Mlw_module.mod_export ["ref"]

let ref_fun : Mlw_expr.psymbol = find_ps ref_module "ref"

let get_logic_fun : Term.lsymbol = find_ls ref_module "prefix !"

let get_fun : Mlw_expr.psymbol = find_ps ref_module "prefix !"

let set_fun : Mlw_expr.psymbol = find_ps ref_module "infix :="

(* mach_int.Int32 module *)

(*
let mach_int_modules, _mach_int_theories =
  try
    Env.read_lib_file (Mlw_main.library_of_env env) ["mach";"int"]
  with e ->
    Self.fatal "Exception raised while loading mach.int modules:@ %a"
      Exn_printer.exn_printer e
*)

(*
let int32_module : Mlw_module.modul =
  try
    Self.result "Looking up module mach.int.Int32";
    Stdlib.Mstr.find "Int32" mach_int_modules
  with Not_found ->
    Self.fatal "Module mach.int.Int32 not found"
*)

let uint32_module =
  try
    Mlw_module.read_module env ["mach";"bv"] "BVCheck32"
  with e ->
    Self.fatal "Exception raised while loading ref module:@ %a"
      Exn_printer.exn_printer e

let uint32_type : Why3.Ty.tysymbol =
  Mlw_module.ns_find_ts uint32_module.Mlw_module.mod_export ["t"]

let uint32_to_int : Term.lsymbol = find_ls uint32_module "to_uint"

let uadd32_fun : Mlw_expr.psymbol = find_ps uint32_module "add_check"

let usub32_fun : Mlw_expr.psymbol = find_ps uint32_module "sub_check"

let umul32_fun : Mlw_expr.psymbol = find_ps uint32_module "mul_check"

(*let neg32_fun : Mlw_expr.psymbol = find_ps uint32_module "prefix -"
 *)

let ueq32_fun : Mlw_expr.psymbol = find_ps uint32_module "eq_check"

let une32_fun : Mlw_expr.psymbol = find_ps uint32_module "ne_check"

let ule32_fun : Mlw_expr.psymbol = find_ps uint32_module "le_check"

let ult32_fun : Mlw_expr.psymbol = find_ps uint32_module "lt_check"

let uge32_fun : Mlw_expr.psymbol = find_ps uint32_module "ge_check"

let ugt32_fun : Mlw_expr.psymbol = find_ps uint32_module "gt_check"

let uint32ofint_fun : Mlw_expr.psymbol = find_ps uint32_module "int_check"

(* mach_int.Int64 module *)

(*
let int64_module : Mlw_module.modul =
  try
    Self.result "Looking up module mach.int.Int64";
    Stdlib.Mstr.find "Int64" mach_int_modules
  with Not_found ->
    Self.fatal "Module mach.int.Int64 not found"
*)
let int64_module =
  Mlw_module.read_module env ["mach";"int"] "Int64"

let int64_type : Why3.Ty.tysymbol =
  Mlw_module.ns_find_ts int64_module.Mlw_module.mod_export ["int64"]

let int64_to_int : Term.lsymbol = find_ls int64_module "to_int"

let add64_fun : Mlw_expr.psymbol = find_ps int64_module "infix +"

let sub64_fun : Mlw_expr.psymbol = find_ps int64_module "infix -"

let mul64_fun : Mlw_expr.psymbol = find_ps int64_module "infix *"

let le64_fun : Mlw_expr.psymbol = find_ps int64_module "infix <="

let lt64_fun : Mlw_expr.psymbol = find_ps int64_module "infix <"

let int64ofint_fun : Mlw_expr.psymbol = find_ps int64_module "of_int"

(* array.Array module *)

(*
let array_modules, array_theories =
  Env.read_lib_file (Mlw_main.library_of_env env) ["array"]

let array_module : Mlw_module.modul = Stdlib.Mstr.find "Array" array_modules
*)

(*
let array_type : Mlw_ty.T.itysymbol =
  match
    Mlw_module.ns_find_ts array_module.Mlw_module.mod_export ["array"]
  with
    | Mlw_module.PT itys -> itys
    | Mlw_module.TS _ -> assert false
*)


(*********)
(* types *)
(*********)

let unit_type = Ty.ty_tuple []
let mlw_int_type = Mlw_ty.ity_pur Ty.ts_int []
let mlw_uint32_type = Mlw_ty.ity_pur uint32_type []
let mlw_int64_type = Mlw_ty.ity_pur int64_type []

let rec ctype_and_default ty =
  match ty with
    | TVoid _attr -> Mlw_ty.ity_unit, Mlw_expr.e_void
    | TInt (IInt, _attr) ->
      let n = Mlw_expr.e_const (Number.ConstInt (Number.int_const_dec "0")) in
      mlw_uint32_type,
      Mlw_expr.e_app
        (Mlw_expr.e_arrow uint32ofint_fun [mlw_int_type] mlw_uint32_type) [n]
    | TInt (ILong, _attr) ->
      let n = Mlw_expr.e_const (Number.ConstInt (Number.int_const_dec "0")) in
      mlw_int64_type,
      Mlw_expr.e_app
        (Mlw_expr.e_arrow int64ofint_fun [mlw_int_type] mlw_int64_type) [n]
    | TInt (_, _) ->
      Self.not_yet_implemented "ctype TInt"
    | TFloat (_, _) ->
      Self.not_yet_implemented "ctype TFloat"
    | TPtr(TInt _ as t, _attr) ->
      let t,_ = ctype_and_default t in
      Mlw_ty.ity_pur map_ts [mlw_int_type ; t], Mlw_expr.e_void
    | TPtr(_ty, _attr) ->
      Self.not_yet_implemented "ctype TPtr"
    | TArray (_, _, _, _) ->
      Self.not_yet_implemented "ctype TArray"
    | TFun (_, _, _, _) ->
      Self.not_yet_implemented "ctype TFun"
    | TNamed (_, _) ->
      Self.not_yet_implemented "ctype TNamed"
    | TComp (_, _, _) ->
      Self.not_yet_implemented "ctype TComp"
    | TEnum (_, _) ->
      Self.not_yet_implemented "ctype TEnum"
    | TBuiltin_va_list _ ->
      Self.not_yet_implemented "ctype TBuiltin_va_list"

let ctype ty = fst(ctype_and_default ty)

let logic_types = Hashtbl.create 257

let type_vars = ref []

let find_type_var v =
  try
    List.assoc v !type_vars
  with Not_found -> Self.fatal "type variable %s not found" v

let push_type_var v =
  let tv = Ty.create_tvsymbol (Ident.id_fresh v) in
  type_vars := (v,tv) :: !type_vars

let pop_type_var v =
  match !type_vars with
    | (w,_) :: r ->
      if v=w then type_vars := r
      else Self.fatal "pop_type_var: %s expected,found %s" v w
    | [] -> Self.fatal "pop_type_var: empty"

let rec logic_type ty =
  match ty with
    | Linteger -> int_type
    | Lreal -> real_type
    | Ltype (lt, args) ->
      begin
        try
          let ts = Hashtbl.find logic_types lt.lt_name in
          Ty.ty_app ts (List.map logic_type args)
        with
            Not_found -> Self.fatal "logic type %s not found" lt.lt_name
      end
    | Lvar v -> Ty.ty_var (find_type_var v)
    | Ctype _
    | Larrow (_, _) ->
        Self.not_yet_implemented "logic_type"



let mk_ref ty =
    let ref_ty = Mlw_ty.ity_app_fresh ref_type [ty] in
    Mlw_expr.e_arrow ref_fun [ty] ref_ty

let mk_get ref_ty ty =
    Mlw_expr.e_arrow get_fun [ref_ty] ty

let mk_set ref_ty ty =
    (* (:=) has type (r:ref 'a) (v:'a) unit *)
    Mlw_expr.e_arrow set_fun [ref_ty; ty] Mlw_ty.ity_unit





(*********)
(* terms *)
(*********)

let logic_constant c =
  match c with
    | Integer(_value,Some s) ->
      let c = Literals.integer s in Number.ConstInt c
    | Integer(_value,None) ->
      Self.not_yet_implemented "logic_constant Integer None"
    | LReal { r_literal = s } ->
      let c = Literals.floating_point s in Number.ConstReal c
    | (LStr _|LWStr _|LChr _|LEnum _) ->
      Self.not_yet_implemented "logic_constant"

let t_app ls args =
  try
    Term.t_app_infer ls args
  with
      Not_found ->
        Self.fatal "lsymbol %s not found" ls.Term.ls_name.Ident.id_string

let bin (ty1,t1) op (ty2,t2) =
  match op,ty1,ty2 with

    | PlusA,Linteger,Linteger -> t_app add_int [t1;t2]
    | PlusA,Lreal,Lreal -> t_app add_real [t1;t2]

    | MinusA,Linteger,Linteger -> t_app sub_int [t1;t2]
    | MinusA,Lreal,Lreal -> t_app sub_real [t1;t2]

    | Mult,Linteger,Linteger -> t_app mul_int [t1;t2]
    | Mult,Lreal,Lreal -> t_app mul_real [t1;t2]

    | PlusA,ty1,ty2 -> Self.not_yet_implemented "bin PlusA(%a,%a)"
      Cil_printer.pp_logic_type ty1 Cil_printer.pp_logic_type ty2
    | MinusA,_,_ -> Self.not_yet_implemented "bin MinusA"
    | Mult,_,_ -> Self.not_yet_implemented "bin Mult"
    | (PlusPI|IndexPI|MinusPI|MinusPP),_,_
      -> Self.not_yet_implemented "bin Plus"
    | Div,Linteger,Linteger -> t_app div_int [t1;t2]
    | (Div|Mod),_,_
      -> Self.not_yet_implemented "bin Div/Mod"
    | (Shiftlt|Shiftrt),_,_
      -> Self.not_yet_implemented "bin Shift"
    | (Lt|Gt|Le|Ge|Eq|Ne),_,_
      -> Self.not_yet_implemented "bin Lt..Ne"
    | (BAnd|BXor|BOr|LAnd|LOr),_,_
      -> Self.not_yet_implemented "bin BAnd..LOr"

let unary op (ty,t) =
  match op,ty with
    | Neg,Linteger -> t_app minus_int [t]
    | Neg,Lreal -> t_app minus_real [t]
    | Neg,_ -> Self.not_yet_implemented "unary Neg,_"
    | BNot,_ -> Self.not_yet_implemented "unary BNot"
    | LNot,_ -> Self.not_yet_implemented "unary LNot"

let bound_vars = Hashtbl.create 257

let create_lvar v =
  let id = Ident.id_fresh v.lv_name in
  let vs = Term.create_vsymbol id (logic_type v.lv_type) in
(**)
  Self.result "create logic variable %d" v.lv_id;
(**)
  Hashtbl.add bound_vars v.lv_id vs;
  vs

let get_lvar lv =
  try
    Hashtbl.find bound_vars lv.lv_id
  with Not_found ->
    Self.fatal "logic variable %s (%d) not found" lv.lv_name lv.lv_id


let program_vars = Hashtbl.create 257

let create_var_full v =
(**)
 Self.result "create program variable %s (%d)" v.vname v.vid;
(**)
  let id = Ident.id_fresh v.vname in
  let ty,def = ctype_and_default v.vtype in
  let def = Mlw_expr.e_app (mk_ref ty) [def] in
  let let_defn, vs = Mlw_expr.create_let_pv_defn id def in
  Hashtbl.add program_vars v.vid (vs,true,ty);
  let_defn,vs

let create_var v = fst (create_var_full v)

let get_var v =
  try
    Hashtbl.find program_vars v.vid
  with Not_found ->
    Self.fatal "program variable %s (%d) not found" v.vname v.vid

let program_funs = Hashtbl.create 257

let create_function v args spec ret_type =
  let id = Ident.id_fresh v.vname in
  let aty = Mlw_ty.vty_arrow args ~spec (Mlw_ty.VTvalue ret_type) in
  let ps = Mlw_expr.create_psymbol id aty in
(*
  let def = Mlw_expr.create_fun_defn id lambda in
  let ps = def.Mlw_expr.fun_ps in
*)
  Self.result "created program function %s (%d)" v.vname v.vid;
  let arg_ty = List.map (fun v -> v.Mlw_ty.pv_ity) args in
  Hashtbl.add program_funs v.vid (ps,arg_ty,ret_type);
  ps

let get_function v =
  try
    Hashtbl.find program_funs v.vid
  with Not_found ->
    Self.fatal "program function %s (%d) not found" v.vname v.vid


let logic_symbols = Hashtbl.create 257

let create_lsymbol li =
  let name = li.l_var_info.lv_name in
  let id = Ident.id_fresh name in
  let args = List.map create_lvar li.l_profile in
  let targs = List.map (fun v -> v.Term.vs_ty) args in
  let ret_ty = Opt.map logic_type li.l_type in
  let vs = Term.create_lsymbol id targs ret_ty in
  Self.result "creating logic symbol %d (%s)" li.l_var_info.lv_id name;
  Hashtbl.add logic_symbols li.l_var_info.lv_id vs;
  vs,args

let get_lsymbol li =
  try
    Hashtbl.find logic_symbols li.l_var_info.lv_id
  with
      Not_found -> Self.fatal "logic symbol %s not found" li.l_var_info.lv_name

let result_vsymbol =
  ref (Term.create_vsymbol (Ident.id_fresh "result") unit_type)

type label = Here | Old | At of string

let is_int_type t =
  match t with
    | Linteger -> true
    | Ctype(TInt (_, _)) -> true
    | _ -> false

let is_real_type t =
  match t with
    | Lreal -> true
    | Ctype(TFloat (_, _)) -> true
    | _ -> false


let coerce_to_int ty t =
  match ty with
    | Linteger -> t
    | Ctype(TInt(IInt,_attr)) -> t_app uint32_to_int [t]
    | Ctype(TInt(ILong,_attr)) -> t_app int64_to_int [t]
    | _ -> Self.not_yet_implemented "coerce_to_int"


let rec term_node ~label t =
  match t with
    | TConst cst -> Term.t_const (logic_constant cst)
    | TLval lv -> tlval ~label lv
    | TBinOp (op, t1, t2) -> bin (term ~label t1) op (term ~label t2)
    | TUnOp (op, t) -> unary op (term ~label t)
    | TCastE (_, _) -> Self.not_yet_implemented "term_node TCastE"
    | Tapp (li, labels, args) ->
      begin
        match labels with
          | [] ->
            let ls = get_lsymbol li in
            let args = List.map (fun x ->
              let _ty,t = term ~label x in
(*
              Self.result "arg = %a, type  = %a"
              Cil_printer.pp_term x
              Cil_printer.pp_logic_type ty;
*)
              t) args in
            t_app ls args
          | _ ->
            Self.not_yet_implemented "term_node Tapp with labels"
      end
    | Tat (t, lab) ->
      begin
        match lab with
          | LogicLabel(None, "Here") -> snd (term ~label:Here t)
          | LogicLabel(None, "Old") -> snd (term ~label:Old t)
          | LogicLabel(None, lab) -> snd (term ~label:(At lab) t)
          | LogicLabel(Some _, _lab) ->
            Self.not_yet_implemented "term_node Tat/LogicLabel/Some"
          | StmtLabel _ ->
            Self.not_yet_implemented "term_node Tat/StmtLabel"
      end
    | TCoerce (_, _)->
      Self.not_yet_implemented "TCoerce"
    | TCoerceE (_, _)->
      Self.not_yet_implemented "TCoerceE"
    | TLogic_coerce (ty, t) when is_int_type ty ->
      let _,t' = term ~label t in
      begin
        match ty, t.term_type with
          | Linteger, Ctype(TInt(IInt,_attr)) ->
             t_app uint32_to_int [t']
          | Linteger, Ctype(TInt(ILong,_attr)) ->
             t_app int64_to_int [t']
          | _ ->
            Self.not_yet_implemented "TLogic_coerce(int_type,_)"
      end
    | TLogic_coerce (_, _) ->
      Self.not_yet_implemented "TLogic_coerce"
    | TSizeOf _
    | TSizeOfE _
    | TSizeOfStr _
    | TAlignOf _
    | TAlignOfE _
    | TAddrOf _
    | TStartOf _
    | Tlambda (_, _)
    | TDataCons (_, _)
    | Tif (_, _, _)
    | Tbase_addr (_, _)
    | Toffset (_, _)
    | Tblock_length (_, _)
    | Tnull ->
      Self.not_yet_implemented "term_node (1)"
    | TUpdate (_, _, _)
    | Ttypeof _
    | Ttype _
    | Tempty_set
    | Tunion _
    | Tinter _
    | Tcomprehension (_, _, _)
    | Trange (_, _)
    | Tlet (_, _) ->
      Self.not_yet_implemented "term_node (2)"

and term ~label t =
(*
  Self.result "term %a: type = %a"
    Cil_printer.pp_term t Cil_printer.pp_logic_type t.term_type;
*)
  (t.term_type, term_node ~label t.term_node)

and tlval ~label (host,offset) =
  match host,offset with
    | TResult _, TNoOffset -> Term.t_var !result_vsymbol
    | TVar lv, TNoOffset ->
      begin
        let t =
          match lv.lv_origin with
            | None -> Term.t_var (get_lvar lv)
            | Some v ->
              let (v,is_mutable,_ty) = get_var v in
              if is_mutable then
                t_app get_logic_fun [Term.t_var v.Mlw_ty.pv_vs]
              else
                Term.t_var v.Mlw_ty.pv_vs
        in
        match label with
          | Here -> t
          | Old -> Mlw_wp.t_at_old t
          | At _lab ->
            (* t_app Mlw_wp.fs_at [t; ??? lab] *)
      Self.not_yet_implemented "tlval TVar/At"
      end
    | TVar _, (TField (_, _)|TModel (_, _)|TIndex (_, _)) ->
      Self.not_yet_implemented "tlval TVar"
    | TResult _, _ ->
      Self.not_yet_implemented "tlval Result"
    | TMem({term_node = TBinOp((PlusPI|IndexPI),t,i)}), TNoOffset ->
      (* t[i] *)
      t_app map_get [snd(term ~label t);snd(term ~label i)]
    | TMem({term_node = TBinOp(_,t,i)}), TNoOffset ->
      Self.not_yet_implemented "tlval Mem(TBinOp(_,%a,%a), TNoOffset)"
        Cil_printer.pp_term t Cil_printer.pp_term i
    | TMem t, TNoOffset ->
      Self.not_yet_implemented "tlval Mem(%a, TNoOffset)"
        Cil_printer.pp_term t
    | TMem _t, TField _ ->
      Self.not_yet_implemented "tlval Mem TField"
    | TMem _t, TModel _ ->
      Self.not_yet_implemented "tlval Mem TModel"
    | TMem _t, TIndex _ ->
      Self.not_yet_implemented "tlval Mem TNoOffset"




(****************)
(* propositions *)
(****************)

let eq op ty1 t1 ty2 t2 =
  match ty1,ty2 with
    | ty1, ty2 when is_int_type ty1 && is_int_type ty2 ->
      op (coerce_to_int ty1 t1) (coerce_to_int ty2 t2)
    | Lreal, Lreal -> op t1 t2
    | Ctype _,_ ->
      Self.not_yet_implemented "eq Ctype"
    | Ltype _, Ltype _ when ty1 = ty2 -> op t1 t2
    | Lvar _,_ ->
      Self.not_yet_implemented "eq Lvar"
    | Larrow _,_ ->
      Self.not_yet_implemented "eq Larrow"
    | _,_ ->
      Self.not_yet_implemented "eq"

let compare op ty1 t1 ty2 t2 =
  match ty1,ty2 with
    | ty1,ty2 when is_int_type ty1 && is_int_type ty2 ->
      t_app op [coerce_to_int ty1 t1;coerce_to_int ty2 t2]
    | Lreal, Lreal -> assert false
    | Ctype _,_ ->
      Self.not_yet_implemented "compare Ctype"
    | Ltype _, Ltype _ -> assert false
    | Lvar _,_ ->
      Self.not_yet_implemented "compare Lvar"
    | Larrow _,_ ->
      Self.not_yet_implemented "compare Larrow"
    | _,_ ->
      Self.not_yet_implemented "compare"


let rel (ty1,t1) op (ty2,t2) =
  match op with
    | Req -> eq Term.t_equ ty1 t1 ty2 t2
    | Rneq -> eq Term.t_neq ty1 t1 ty2 t2
    | Rge when is_int_type ty1 && is_int_type ty2 -> compare ge_int ty1 t1 ty2 t2
    | Rle when is_int_type ty1 && is_int_type ty2 -> compare le_int ty1 t1 ty2 t2
    | Rgt when is_int_type ty1 && is_int_type ty2 -> compare gt_int ty1 t1 ty2 t2
    | Rlt when is_int_type ty1 && is_int_type ty2 -> compare lt_int ty1 t1 ty2 t2
    | Rge when is_real_type ty1 && is_real_type ty2 -> t_app ge_real [t1;t2]
    | Rge ->
      Self.not_yet_implemented "rel Rge"
    | Rle ->
      Self.not_yet_implemented "rel Rle"
    | Rgt ->
      Self.not_yet_implemented "rel Rgt"
    | Rlt ->
      Self.not_yet_implemented "rel Rlt %a %a"
        Cil_printer.pp_logic_type ty1 Cil_printer.pp_logic_type ty2

let rec predicate ~label p =
  match p with
    | Pfalse -> Term.t_false
    | Ptrue -> Term.t_true
    | Prel (op, t1, t2) -> rel (term ~label t1) op (term ~label t2)
    | Pforall (lv, p) ->
      let l = List.map create_lvar lv in
      Term.t_forall_close l [] (predicate_named ~label p)
    | Pimplies (p1, p2) ->
      Term.t_implies (predicate_named ~label p1) (predicate_named ~label p2)
    | Pand (p1, p2) ->
      Term.t_and (predicate_named ~label p1) (predicate_named ~label p2)
    | Papp (_, _, _) ->
      Self.not_yet_implemented "predicate Papp"
    | Pnot _ ->
      Self.not_yet_implemented "predicate Pnot"
    | Pat (_, _) ->
      Self.not_yet_implemented "predicate Pat"
    | Pdangling _
    | Pseparated _
    | Por (_, _)
    | Pxor (_, _)
    | Piff (_, _)
    | Pif (_, _, _)
    | Plet (_, _)
    | Pexists (_, _)
    | Pvalid_read (_, _)
    | Pvalid (_, _)
    | Pinitialized (_, _)
    | Pallocable (_, _)
    | Pfreeable (_, _)
    | Pfresh (_, _, _, _)
    | Psubtype (_, _) ->
        Self.not_yet_implemented "predicate"

and predicate_named ~label p = predicate ~label p.content






(**********************)
(* logic declarations *)
(**********************)

let use th1 th2 =
  let name = th2.Theory.th_name in
  Theory.close_namespace
    (Theory.use_export (Theory.open_namespace th1 name.Ident.id_string) th2)
    true

let add_decl th d =
  try
    Theory.add_decl th d
  with
      Not_found -> Self.fatal "add_decl"

let add_decls_as_theory theories id decls =
  match decls with
    | [] -> theories
    | _ ->
      let th = Theory.create_theory id in
      let th = use th int_theory in
      let th = use th real_theory in
      let th = use th map_theory in
      let th = List.fold_left use th theories in
      let th = List.fold_left add_decl th (List.rev decls) in
      let th = Theory.close_theory th in
      th :: theories

let rec logic_decl ~in_axiomatic a _loc (theories,decls) =
  match a with
    | Dtype (lt, loc) ->
      let targs =
        List.map (fun s -> Ty.create_tvsymbol (Ident.id_fresh s)) lt.lt_params
      in
      let tdef = match lt.lt_def with
          | None -> None
          | Some _ -> Self.not_yet_implemented "logic_decl Dtype non abstract"
      in
      let ts =
        Ty.create_tysymbol
          (Ident.id_user lt.lt_name (Loc.extract loc)) targs tdef
      in
      Hashtbl.add logic_types lt.lt_name ts;
      let d = Decl.create_ty_decl ts in
      (theories,d::decls)
    | Dfun_or_pred (li, _loc) ->
      begin
        match li.l_labels with
          | [] ->
            List.iter push_type_var li.l_tparams;
            let d =
              match li.l_body with
                | LBnone ->
                  let ls,_ = create_lsymbol li in
                  Decl.create_param_decl ls
                | LBterm d ->
                  let ls,args = create_lsymbol li in
                  let (_ty,d) = term ~label:Here d in
                  let def = Decl.make_ls_defn ls args d in
                  Decl.create_logic_decl [def]
                | _ ->
                  Self.not_yet_implemented "Dfun_or_pred, other bodies"
            in
            List.iter pop_type_var (List.rev li.l_tparams);
            (theories,d :: decls)

          | _ ->
            Self.not_yet_implemented "Dfun_or_pred with labels"
      end
    | Dlemma(name,is_axiom,labels,vars,p,loc) ->
      begin
        match labels,vars with
          | [],[] ->
            assert (in_axiomatic || not is_axiom);
            let d =
              let pr = Decl.create_prsymbol
                (Ident.id_user name (Loc.extract loc))
              in
              Decl.create_prop_decl
                (if is_axiom then Decl.Paxiom else Decl.Plemma)
                pr (predicate_named ~label:Here p)
            in
            (theories,d::decls)
          | _ ->
            Self.not_yet_implemented "Dlemma with labels or vars"
      end
    | Daxiomatic (name, decls', loc) ->
      let theories =
        add_decls_as_theory theories
          (Ident.id_fresh global_logic_decls_theory_name) decls
      in
      let (t,decls'') =
        List.fold_left
          (fun acc d -> logic_decl ~in_axiomatic:true d loc acc)
          ([],[])
          decls'
      in
      assert (t = []);
      let theories =
        add_decls_as_theory theories (Ident.id_user name (Loc.extract loc)) decls''
      in
      (theories,[])
    | Dvolatile (_, _, _, _)
    | Dinvariant (_, _)
    | Dtype_annot (_, _)
    | Dmodel_annot (_, _)
    | Dcustom_annot (_, _, _)
        -> Self.not_yet_implemented "logic_decl"

let identified_proposition p =
  { name = p.ip_name; loc = p.ip_loc; content = p.ip_content }






(**************)
(* statements *)
(**************)




let seq e1 e2 =
  let l = Mlw_expr.create_let_defn (Ident.id_fresh "_tmp") e1 in
  Mlw_expr.e_let l e2

let annot a e =
  match a.annot_content with
  | AAssert ([],pred) ->
    let p = predicate_named ~label:Here pred in
    let a = Mlw_expr.e_assert Mlw_expr.Aassert p in
    seq a e
  | AAssert(_labels,_pred) ->
    Self.not_yet_implemented "annot AAssert"
  | AStmtSpec _ ->
    Self.not_yet_implemented "annot AStmtSpec"
  | AInvariant _ ->
    Self.not_yet_implemented "annot AInvariant"
  | AVariant _ ->
    Self.not_yet_implemented "annot AVariant"
  | AAssigns _ ->
    Self.not_yet_implemented "annot AAssigns"
  | AAllocation _ ->
    Self.not_yet_implemented "annot AAllocation"
  | APragma _ ->
    Self.not_yet_implemented "annot APragma"

let loop_annot a =
  List.fold_left (fun (inv,var) a ->
    match a.annot_content with
      | AAssert ([],_pred) ->
        Self.not_yet_implemented "loop_annot AAssert"
      | AAssert(_labels,_pred) ->
        Self.not_yet_implemented "loop_annot AAssert"
      | AStmtSpec _ ->
        Self.not_yet_implemented "loop_annot AStmtSpec"
      | AInvariant([],true,p) ->
        (Term.t_and inv (predicate_named ~label:Here p),var)
      | AInvariant _ ->
        Self.not_yet_implemented "loop_annot AInvariant"
      | AVariant (t, None) ->
        (inv,(snd (term ~label:Here t),None)::var)
      | AVariant (_var, Some _) ->
        Self.not_yet_implemented "loop_annot AVariant/Some"
      | AAssigns _ ->
        Self.not_yet_implemented "loop_annot AAssigns"
      | AAllocation _ ->
        Self.not_yet_implemented "loop_annot AAllocation"
      | APragma _ ->
        Self.not_yet_implemented "loop_annot APragma")
    (Term.t_true, []) a

let binop op e1 e2 =
  let ls,ty,ty' =
    match op with
      | PlusA -> uadd32_fun, mlw_uint32_type, mlw_uint32_type
      | MinusA -> usub32_fun, mlw_uint32_type, mlw_uint32_type
      | Mult -> umul32_fun, mlw_uint32_type, mlw_uint32_type
      | Lt -> ult32_fun, mlw_uint32_type, Mlw_ty.ity_bool
      | Le -> ule32_fun, mlw_uint32_type, Mlw_ty.ity_bool
      | Gt -> ugt32_fun, mlw_uint32_type, Mlw_ty.ity_bool
      | Ge -> uge32_fun, mlw_uint32_type, Mlw_ty.ity_bool
      | Eq -> ueq32_fun, mlw_uint32_type, Mlw_ty.ity_bool
      | Ne -> une32_fun, mlw_uint32_type, Mlw_ty.ity_bool
      | PlusPI|IndexPI|MinusPI|MinusPP ->
        Self.not_yet_implemented "binop plus/minus"
      | Div|Mod ->
        Self.not_yet_implemented "binop div/mod"
      | Shiftlt|Shiftrt ->
        Self.not_yet_implemented "binop shift"
      | BAnd|BXor|BOr|LAnd|LOr ->
        Self.not_yet_implemented "binop bool"
  in
  Mlw_expr.e_app (Mlw_expr.e_arrow ls [ty;ty] ty') [e1;e2]

let unop op e =
  let ls,ty,ty' =
    match op with
      | Neg -> (* Unary minus *)
        Self.not_yet_implemented "unop Neg"
      (*        neg32_fun, mlw_int32_type, mlw_int32_type*)
      | BNot -> (* Bitwise complement (~) *)
        Self.not_yet_implemented "unop BNot"
      | LNot -> (* Logical Not (!) *)
        Self.not_yet_implemented "unop LNot"
  in
  Mlw_expr.e_app (Mlw_expr.e_arrow ls [ty] ty') [e]

let constant c =
  match c with
  | CInt64(t,IInt, sopt) ->
    let s =
      match sopt with
        | Some s -> s
        | None -> Integer.to_string t
    in
    let n = Mlw_expr.e_const (Number.ConstInt (Literals.integer s)) in
    Mlw_expr.e_app
      (Mlw_expr.e_arrow uint32ofint_fun [mlw_int_type] mlw_uint32_type) [n]
  | CInt64(_t,_ikind, _) ->
      Self.not_yet_implemented "CInt64"
  | CStr _
  | CWStr _
  | CChr _
  | CReal (_, _, _)
  | CEnum _ ->
      Self.not_yet_implemented "constant"

let rec expr e =
  match e.enode with
    | Const c -> constant c
    | Lval lv -> lval lv
    | BinOp (op, e1, e2, _loc) ->
      binop op (expr e1) (expr e2)
    | UnOp (op, e, _loc) ->
      unop op (expr e)
    | CastE (ty, e) ->
      let e' = expr e in
      begin
        match ty, Cil.typeOf e with
          | TInt(ILong,_attr1), TInt(IInt,_attr2) ->
            Mlw_expr.e_app
              (Mlw_expr.e_arrow int64ofint_fun
                 [mlw_int_type] mlw_int64_type)
              [Mlw_expr.e_lapp uint32_to_int [e'] mlw_int_type]
          | _ ->
            Self.not_yet_implemented "expr CastE"
      end
    | SizeOf _
    | SizeOfE _
    | SizeOfStr _
    | AlignOf _
    | AlignOfE _
    | AddrOf _
    | StartOf _
    | Info (_, _)
      -> Self.not_yet_implemented "expr"

and lval (host,offset) =
  match host,offset with
    | Var v, NoOffset ->
      let v,is_mutable,ty = get_var v in
      if is_mutable then
        begin try
                Mlw_expr.e_app
                  (mk_get v.Mlw_ty.pv_ity ty)
                  [Mlw_expr.e_value v]
          with e ->
            Self.fatal "Exception raised during application of !@ %a@."
              Exn_printer.exn_printer e
        end
      else
        Mlw_expr.e_value v
    | Var _, (Field (_, _)|Index (_, _)) ->
      Self.not_yet_implemented "lval Var"
    | Mem({enode = BinOp((PlusPI|IndexPI),e,i,ty)}), NoOffset ->
      (* e[i] -> Map.get e i *)
      let e = expr e in
      let ity =
        match ty with
          | TPtr(t,_) -> ctype t
          | _ -> assert false
      in
      let i = expr i in
      let i = Mlw_expr.e_lapp uint32_to_int [i] mlw_int_type in
      Mlw_expr.e_lapp map_get [e;i] ity
  | Mem _, _ ->
      Self.not_yet_implemented "lval Mem"

let functional_expr e =
  match e.enode with
    | Lval (Var v, NoOffset) ->
      let id,tyl,ty = get_function v in
      Mlw_expr.e_arrow id tyl ty
    | Lval _
    | Const _
    | BinOp _
    | SizeOf _
    | SizeOfE _
    | SizeOfStr _
    | AlignOf _
    | AlignOfE _
    | UnOp (_, _, _)
    | CastE (_, _)
    | AddrOf _
    | StartOf _
    | Info (_, _)
      -> Self.not_yet_implemented "functional_expr"

let assignment (lhost,offset) e _loc =
  match lhost,offset with
    | Var v , NoOffset ->
      let v,is_mutable,ty = get_var v in
      if is_mutable then
        Mlw_expr.e_app
          (mk_set v.Mlw_ty.pv_ity ty)
          [Mlw_expr.e_value v; e]
      else
        Self.not_yet_implemented "mutation of formal parameters"
    | Var _ , Field _ ->
      Self.not_yet_implemented "assignment Var/Field"
    | Var _ , Index _ ->
      Self.not_yet_implemented "assignment Var/Index"
    | Mem _, _ ->
      Self.not_yet_implemented "assignment Mem"

let instr i =
  match i with
  | Set(lv,e,loc) -> assignment lv (expr e) loc
  | Call (None, e, el, _loc) ->
    let e = functional_expr e in
    Mlw_expr.e_app e (List.map expr el)
  | Call (Some lv, e, el, loc) ->
    let e = functional_expr e in
    let e = Mlw_expr.e_app e (List.map expr el) in
    assignment lv e loc
  | Asm _ ->
    Self.not_yet_implemented "instr Asm"
  | Skip _loc ->
    Mlw_expr.e_void
  | Code_annot (_, _) ->
    Self.not_yet_implemented "instr Code_annot"

let exc_break =
  Mlw_ty.create_xsymbol (Ident.id_fresh "Break") Mlw_ty.ity_unit

let rec stmt s =
  match s.skind with
    | Instr i ->
      let annotations = Annotations.code_annot s in
      let e =
        List.fold_right annot annotations (instr i)
      in e
    | Block b -> block b
    | Return (None, _loc) ->
      Mlw_expr.e_void
    | Return (Some e, _loc) ->
      expr e
    | Goto (_, _) ->
      Self.not_yet_implemented "stmt Goto"
    | Break _loc ->
      Mlw_expr.e_raise exc_break Mlw_expr.e_void
        Mlw_ty.ity_unit
    | Continue _ ->
      Self.not_yet_implemented "stmt Continue"
    | If (c, e1, e2, _loc) ->
      Mlw_expr.e_if (expr c) (block e1) (block e2)
    | Switch (_, _, _, _) ->
      Self.not_yet_implemented "stmt Switch"
    | Loop (annots, body, _loc, _continue, _break) ->
      (*
        "while (1) body" is translated to
        try loop
          try body
          with Continue -> ()
        with Break -> ()
      *)
      assert (annots = []);
      let annots = Annotations.code_annot s in
      let inv, var = loop_annot annots in
      let v =
        Mlw_ty.create_pvsymbol (Ident.id_fresh "_dummy") Mlw_ty.ity_unit
      in
      Mlw_expr.e_try
        (Mlw_expr.e_loop inv var (block body))
        [exc_break,v,Mlw_expr.e_void]
    | UnspecifiedSequence _ ->
      Self.not_yet_implemented "stmt UnspecifiedSequence"
    | Throw (_, _) ->
      Self.not_yet_implemented "stmt Throw"
    | TryCatch (_, _, _) ->
      Self.not_yet_implemented "stmt TryCatch"
    | TryFinally (_, _, _) ->
      Self.not_yet_implemented "stmt TryFinally"
    | TryExcept (_, _, _, _) ->
      Self.not_yet_implemented "stmt TryExcept"

and block b =
  let rec mk_seq l =
    match l with
      | [] -> Mlw_expr.e_void
      | [s] -> stmt s
      | s::r -> seq (stmt s) (mk_seq r)
  in
  mk_seq b.bstmts







(*************)
(* contracts *)
(*************)

let extract_simple_contract c =
  let pre,post,ass = List.fold_left
    (fun (pre,post,ass) b ->
      if not (Cil.is_default_behavior b) then
        Self.not_yet_implemented "named behaviors";
      if b.b_assumes <> [] then
        Self.not_yet_implemented "assumes clause";
      let pre =
        List.fold_left
          (fun acc f -> (identified_proposition f) :: acc)
          pre b.b_requires
      in
      let post =
        List.fold_left
          (fun acc (k,f) ->
            if k <> Normal then
              Self.not_yet_implemented "abnormal termination post-condition";
            (identified_proposition f) :: acc)
          post b.b_post_cond
      in
      let ass =
        match b.b_assigns with
        | WritesAny -> ass
        | Writes l ->
          let l = List.map (fun (t,_) ->
            term (* ~in_contract:true Logic_const.here_label *) t.it_content) l in
          match ass with
          | None -> Some l
          | Some l' -> Some (l@l')
      in
      (pre,post, ass))
    ([],[],None) c.spec_behavior
  in
  (Logic_const.pands pre, Logic_const.pands post, ass)






(*************************)
(* function declarations *)
(*************************)

let fundecl fdec =
  let fun_id = fdec.svar in
  let kf = Globals.Functions.get fun_id in
  Self.log "processing function %a" Kernel_function.pretty kf;
  let args =
    match Kernel_function.get_formals kf with
      | [] ->
        [ Mlw_ty.create_pvsymbol (Ident.id_fresh "_dummy") Mlw_ty.ity_unit ]
      | l ->
        List.map (fun v ->
          let ity = ctype v.vtype in
          let vs =
            Mlw_ty.create_pvsymbol (Ident.id_fresh v.vname) ity
          in
          Hashtbl.add program_vars v.vid (vs,false,ity);
          vs)
        l
  in
  let body = fdec.sbody in
  let contract = Annotations.funspec kf in
  let pre,post,_ass = extract_simple_contract contract in
  let ret_type = ctype (Kernel_function.get_return_type kf) in
  let result =
    Term.create_vsymbol (Ident.id_fresh "result")
      (Mlw_ty.ty_of_ity ret_type)
  in
  result_vsymbol := result;
  let locals =
    List.map create_var (Kernel_function.get_locals kf)
  in
  let spec = {
    Mlw_ty.c_pre = predicate_named ~label:Here pre;
    c_post =
      Term.t_eps
        (Term.t_close_bound result (predicate_named ~label:Here post));
    c_xpost = Mlw_ty.Mexn.empty;
    c_effect = Mlw_ty.eff_empty;
    c_variant = [];
    c_letrec  = 0;
  }
  in
  let ps = create_function fun_id args spec ret_type in
  let body = block body in
  let full_body = List.fold_right Mlw_expr.e_let locals body in
  let lambda = {
    Mlw_expr.l_args = args;
    l_expr = full_body;
    l_spec = spec;
  }
  in
  let def = Mlw_expr.create_rec_defn [ps,lambda] in
  Mlw_decl.create_rec_decl def






(***********************)
(* global declarations *)
(***********************)


let global (theories,lemmas,functions) g =
  match g with
    | GFun (fdec,_) ->
      let f = fundecl fdec in
      (theories,lemmas,f::functions)
   | GVar (vi, _init, _loc) ->
(*
        let ty = translate_type vi.vtype in
        let init = match init.init with
        | None -> [AST.Init_space(Csyntax.sizeof ty)]
        | Some _ -> Self.fatal "cannot handle initializer" in
        let g = {
          AST.gvar_info = ty;
          AST.gvar_init = init;
          AST.gvar_readonly = false; (* TODO *)
          AST.gvar_volatile = false; (* TODO *)
        }
        in
        { acc with AST.prog_vars =
          (intern_string vi.vname, g)::acc.AST.prog_vars }
*)
     let _,pv = create_var_full vi in
     let sym = Mlw_expr.LetV pv in
     (theories,lemmas,(Mlw_decl.create_val_decl sym)::functions)

    | GFunDecl(_funspec,vi,_location) ->
      begin match vi.vname with
        | "Frama_C_bzero" | "Frama_C_copy_block" ->
          (theories,lemmas,functions)
        | _ ->
(*
          let f = fundecl vi in
 *)
          (theories,lemmas,functions)
      end
    | GVarDecl(vi,_location) ->
       let _,pv = create_var_full vi in
       let sym = Mlw_expr.LetV pv in
       (theories,lemmas,(Mlw_decl.create_val_decl sym)::functions)
    | GAnnot (a, loc) ->
      let (t,l) = logic_decl ~in_axiomatic:false a loc (theories,lemmas) in
      (t,l,functions)
    | GText _ ->
      Self.not_yet_implemented "global: GText"
    | GPragma (_, _) ->
      Self.not_yet_implemented "global: GPragma"
    | GAsm (_, _) ->
      Self.not_yet_implemented "global: GAsm"
    | GEnumTagDecl (_, _) ->
      Self.not_yet_implemented "global: GEnumTagDecl"
    | GEnumTag (_, _) ->
      Self.not_yet_implemented "global: GEnumTag"
    | GCompTagDecl (_, _) ->
      Self.not_yet_implemented "global: GCompTagDecl"
    | GCompTag (_, _) ->
      Self.not_yet_implemented "global: GCompTag"
    | GType (_, _)  ->
      Self.not_yet_implemented "global: GType"


let print_id fmt id = Format.fprintf fmt "%s" id.Ident.id_string

let add_pdecl m d =
  try
    Mlw_module.add_pdecl ~wp:true m d
  with
      Not_found ->
        Self.fatal "add_pdecl %a" (Pp.print_list Pp.comma print_id)
          (Ident.Sid.elements d.Mlw_decl.pd_news)

let use m th =
  let name = th.Theory.th_name in
  Mlw_module.close_namespace
    (Mlw_module.use_export_theory
       (Mlw_module.open_namespace m name.Ident.id_string)
       th)
    true

let use_module m modul =
  let name = modul.Mlw_module.mod_theory.Theory.th_name in
  Mlw_module.close_namespace
    (Mlw_module.use_export
       (Mlw_module.open_namespace m name.Ident.id_string)
       modul)
    true

let prog p =
   try
    (* Self.result "Starting translation"; *)
    let theories,decls,functions =
      List.fold_left global ([],[],[]) p.globals
    in
    Self.result "found %d logic decl(s)" (List.length decls);
    let theories =
      add_decls_as_theory theories
        (Ident.id_fresh global_logic_decls_theory_name) decls
    in
    Self.result "made %d theory(ies)" (List.length theories);
    let m = Mlw_module.create_module env
      (Ident.id_fresh programs_module_name)
    in
    let m = use m int_theory in
    let m = use m real_theory in
    let m = use m map_theory in
    let m = List.fold_left use m theories in
    let m = use_module m ref_module in
    let m = use_module m uint32_module in
    let m = List.fold_left add_pdecl m (List.rev functions) in
    Self.result "made %d function(s)" (List.length functions);
    let m = Mlw_module.close_module m in
    List.rev (m.Mlw_module.mod_theory :: theories) ;
  with (Exit | Not_found| Ty.TypeMismatch _
           | Mlw_ty.TypeMismatch _ | Decl.UnknownIdent _) as e  ->
    Self.fatal "Exception raised during translation to Why3:@ %a@."
      Exn_printer.exn_printer e
    (* | Mlw_ty.TypeMismatch(ity1,ity2,_ity_subst) ->  *)
    (*   Self.fatal "TypeMismatch(%a,%a,_)" *)
    (*         Mlw_pretty.print_ity ity1 Mlw_pretty.print_ity ity2 *)
