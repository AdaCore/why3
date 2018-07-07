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

open Ptree

let ident ?(loc=Loc.dummy_position) ?(lab=[]) s =
  { id_str = s; id_lab = lab; id_loc = loc }

let qualid l =
  let rec aux acc l =
    match l with
    | [] -> acc
    | s :: rem -> aux (Qdot(acc,ident s)) rem
  in
  match l with
    | [] -> assert false
    | s :: rem -> aux (Qident (ident s)) rem


let find m s =
  try
    Theory.ns_find_ls m.Pmodule.mod_theory.Theory.th_export [s]
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
let int_theory =
  try
    Pmodule.read_module env ["int"] "Int"
  with e ->
    Self.fatal "Exception raised while loading int theory:@ %a"
      Exn_printer.exn_printer e

let add_int : Term.lsymbol = find int_theory (Ident.op_infix "+")
let sub_int : Term.lsymbol = find int_theory (Ident.op_infix "-")
let minus_int : Term.lsymbol = find int_theory (Ident.op_prefix "-")
let mul_int : Term.lsymbol = find int_theory (Ident.op_infix "*")
let ge_int : Term.lsymbol = find int_theory (Ident.op_infix ">=")
let le_int : Term.lsymbol = find int_theory (Ident.op_infix "<=")
let gt_int : Term.lsymbol = find int_theory (Ident.op_infix ">")
let lt_int : Term.lsymbol = find int_theory (Ident.op_infix "<")

let computer_div_theory =
  Pmodule.read_module env ["int"] "ComputerDivision"
let div_int : Term.lsymbol = find computer_div_theory "div"

(* real.Real theory *)
let real_type : Ty.ty = Ty.ty_real
let real_theory = Pmodule.read_module env ["real"] "Real"
let add_real : Term.lsymbol = find real_theory (Ident.op_infix "+")
let sub_real : Term.lsymbol = find real_theory (Ident.op_infix "-")
let minus_real : Term.lsymbol = find real_theory (Ident.op_prefix "-")
let mul_real : Term.lsymbol = find real_theory (Ident.op_infix "*")
let ge_real : Term.lsymbol = find real_theory (Ident.op_infix ">=")

(* map.Map theory *)
(*
let map_theory : Theory.theory = Env.read_theory env ["map"] "Map"
let map_ts : Ty.tysymbol = find_type map_theory "map"
(* let map_type (t:Ty.ty) : Ty.ty = Ty.ty_app map_ts [t] *)
let map_get : Term.lsymbol = find map_theory "get"
 *)

let () = Self.result "Loading Why3 modules..."

let find_rs mo s =
  try
    Pmodule.ns_find_rs mo.Pmodule.mod_export [s]
  with e ->
    Self.fatal "Exception raised while loading Why3 program symbol %s:@ %a"
      s Exn_printer.exn_printer e

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
let ref_module : Pmodule.pmodule =
  Pmodule.read_module env ["ref"] "Ref"

let ref_type : Ity.itysymbol =
  Pmodule.ns_find_its ref_module.Pmodule.mod_export ["ref"]

let ref_fun : Expr.rsymbol = find_rs ref_module "ref"

let get_logic_fun : Term.lsymbol = find ref_module (Ident.op_prefix "!")

let get_fun : Expr.rsymbol = find_rs ref_module (Ident.op_prefix "!")

let set_fun : Expr.rsymbol = find_rs ref_module (Ident.op_infix ":=")

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
let int32_module : Pmodule.modul =
  try
    Self.result "Looking up module mach.int.Int32";
    Stdlib.Mstr.find "Int32" mach_int_modules
  with Not_found ->
    Self.fatal "Module mach.int.Int32 not found"
*)

let uint32_module =
  try
    Pmodule.read_module env ["mach";"bv"] "BVCheck32"
  with e ->
    Self.fatal "Exception raised while loading ref module:@ %a"
      Exn_printer.exn_printer e

let uint32_type : Why3.Ity.itysymbol =
  Pmodule.ns_find_its uint32_module.Pmodule.mod_export ["t"]

let uint32_to_int : Term.lsymbol = find uint32_module "to_uint"

let uint32_to_int_fun : Expr.rsymbol = find_rs uint32_module "to_uint"

let uadd32_fun : Expr.rsymbol = find_rs uint32_module "add_check"

let usub32_fun : Expr.rsymbol = find_rs uint32_module "sub_check"

let umul32_fun : Expr.rsymbol = find_rs uint32_module "mul_check"

(*let neg32_fun : Expr.rsymbol = find_rs uint32_module (Ident.op_prefix "-")
 *)

let ueq32_fun : Expr.rsymbol = find_rs uint32_module "eq_check"

let une32_fun : Expr.rsymbol = find_rs uint32_module "ne_check"

let ule32_fun : Expr.rsymbol = find_rs uint32_module "le_check"

let ult32_fun : Expr.rsymbol = find_rs uint32_module "lt_check"

let uge32_fun : Expr.rsymbol = find_rs uint32_module "ge_check"

let ugt32_fun : Expr.rsymbol = find_rs uint32_module "gt_check"

let uint32ofint_fun = qualid ["bv";"BV32";"of_int"]
(*
: Expr.rsymbol = find_rs uint32_module "int_check"
 *)
(* mach_int.Int64 module *)

(*
let int64_module : Pmodule.modul =
  try
    Self.result "Looking up module mach.int.Int64";
    Stdlib.Mstr.find "Int64" mach_int_modules
  with Not_found ->
    Self.fatal "Module mach.int.Int64 not found"
*)
let int64_module =
  Pmodule.read_module env ["mach";"int"] "Int64"

let int64_type : Why3.Ity.itysymbol =
  Pmodule.ns_find_its int64_module.Pmodule.mod_export ["int64"]

let int64_to_int : Term.lsymbol = find int64_module "to_int"

let add64_fun : Expr.rsymbol = find_rs int64_module (Ident.op_infix "+")

let sub64_fun : Expr.rsymbol = find_rs int64_module (Ident.op_infix "-")

let mul64_fun : Expr.rsymbol = find_rs int64_module (Ident.op_infix "*")

let le64_fun : Expr.rsymbol = find_rs int64_module (Ident.op_infix "<=")

let lt64_fun : Expr.rsymbol = find_rs int64_module (Ident.op_infix "<")

let int64ofint_fun = qualid ["bv";"BV64";"of_int"]

(* array.Array module *)

(*
let array_modules, array_theories =
  Env.read_lib_file (Mlw_main.library_of_env env) ["array"]

let array_module : Pmodule.modul = Stdlib.Mstr.find "Array" array_modules
*)

(*
let array_type : Ity.T.itysymbol =
  match
    Pmodule.ns_find_ts array_module.Pmodule.mod_export ["array"]
  with
    | Pmodule.PT itys -> itys
    | Pmodule.TS _ -> assert false
*)



let de_app e1 e2 = Dexpr.dexpr(Dexpr.DEapp(e1,e2))

let de_app1 rs e1 = de_app (Dexpr.dexpr(Dexpr.DErs rs)) e1

let de_app2 rs e1 e2 = de_app (de_app1 rs e1) e2


(*********)
(* types *)
(*********)

let ty_unit = Ty.ty_tuple []
let ity_unit = Ity.ity_tuple []
let mlw_int_type = Ity.ity_int
let mlw_uint32_type =  Ity.ity_app uint32_type [] []
let mlw_int64_type = Ity.ity_app int64_type [] []

let expr ?(loc=Loc.dummy_position) e = { expr_desc = e ; expr_loc = loc }

let e_void = expr (Etuple [])
let e_true = expr Etrue

let e_const_int s = expr (Econst (Number.ConstInt (Literals.integer s)))

let e_app1 id e = expr (Eidapp(id,[e]))

let (*rec*) ctype_and_default ty =
  match ty with
    | TVoid _attr -> Ity.ity_unit, e_void
    | TInt (IInt, _attr) ->
      let n = e_const_int "0" in
      mlw_uint32_type, e_app1 uint32ofint_fun n
    | TInt (ILong, _attr) ->
      let n = e_const_int "0" in
      mlw_int64_type, e_app1 int64ofint_fun n
    | TInt (_, _) ->
       Self.not_yet_implemented "ctype TInt"
    | TFloat (_, _) ->
       Self.not_yet_implemented "ctype TFloat"
(*
    | TPtr(TInt _ as t, _attr) ->
      let t,_ = ctype_and_default t in
      Ity.ity_pure map_ts [mlw_int_type ; t], Expr.e_void
 *)
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

let create_var v is_mutable =
(**)
 Self.result "create program variable %s (%d), mutable = %b" v.vname v.vid is_mutable;
(**)
(*
  let id = Ident.id_fresh v.vname in
  let ty,def = ctype_and_default v.vtype in
  let ref_ty = Ity.ity_app ref_type [ty] [] in
  let def = de_app1 ref_fun def in
  let dlet_defn : Dexpr.dlet_defn= (id,false,Expr.RKnone,def) in
  let let_defn = Dexpr.let_defn dlet_defn in
  let pvs = match let_defn with
      | Expr.LDvar (pvs,_) -> pvs
      | Expr.LDsym _ | Expr.LDrec _ -> assert false
  in
 *)
  Hashtbl.add program_vars v.vid is_mutable

let get_var denv v =
  try
    let is_mutable = Hashtbl.find program_vars v.vid in
    Self.result "get program variable %s (%d), mutable = %b" v.vname v.vid is_mutable;
    Dexpr.denv_get denv v.vname, is_mutable
  with Not_found ->
    Self.fatal "program variable %s (%d) not found" v.vname v.vid

(*let program_funs = Hashtbl.create 257
 *)
(*
let create_function v args spec ret_type body =
  let id = Ident.id_fresh v.vname in
  let ret_type = Dexpr.dity_of_ity ret_type in
  let mask = Ity.MaskVisible in
  let def denv (* : Dexpr.dspec Dexpr.later * variant list Dexpr.later * dexpr *) =
    (spec,(fun _ _ -> []), body)
  in
  let predef = (id,false,Expr.RKfunc,args,ret_type,mask,def) in
  let _,def = Dexpr.drec_defn Dexpr.denv_empty [predef] in
  let def = Dexpr.rec_defn def in
  let rs = match def with
      | Expr.LDvar _ -> assert false
      | Expr.LDrec _ -> assert false
      | Expr.LDsym (rs,cexp) ->
         Hashtbl.add program_funs v.vid (rs,cexp);
         rs
  in
  Self.result "created program function %s (%d)" v.vname v.vid;
  id
 *)

(*
  let cty = Ity.create_cty args pre post xpost Ity.Mpv.empty effect ret_type in
  let rs = Expr.create_rsymbol id cty in
(*
  let def = Expr.let_sym id cexp in
  let ps = def.Expr.fun_ps in
*)
  Self.result "created program function %s (%d)" v.vname v.vid;
  let arg_ty = List.map (fun v -> v.Ity.pv_ity) args in
  Hashtbl.add program_funs v.vid (rs,arg_ty,ret_type);
  rs
 *)

(*
let get_function v =
  try
    Hashtbl.find program_funs v.vid
  with Not_found ->
    Self.fatal "program function %s (%d) not found" v.vname v.vid
 *)


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

let result_pvsymbol =
  ref (Ity.create_pvsymbol (Ident.id_fresh "result") ity_unit)

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


(******************8

let rec term_node denv ~label t lvm old =
  match t with
    | TConst cst -> Term.t_const (logic_constant cst)
    | TLval lv -> tlval denv ~label lv lvm old
    | TBinOp (op, t1, t2) -> bin (term denv ~label t1 lvm old) op (term denv ~label t2 lvm old)
    | TUnOp (op, t) -> unary op (term denv ~label t lvm old)
    | TCastE (_, _) -> Self.not_yet_implemented "term_node TCastE"
    | Tapp (li, labels, args) ->
      begin
        match labels with
          | [] ->
            let ls = get_lsymbol li in
            let args = List.map (fun x ->
              let _ty,t = term denv ~label x lvm old in
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
          | LogicLabel(None, "Here") -> snd (term denv ~label:Here t lvm old)
          | LogicLabel(None, "Old") -> snd (term denv ~label:Old t lvm old)
          | LogicLabel(None, lab) -> snd (term denv ~label:(At lab) t lvm old)
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
      let _,t' = term denv ~label t lvm old in
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

and term denv ~label t lvm old =
(*
  Self.result "term %a: type = %a"
    Cil_printer.pp_term t Cil_printer.pp_logic_type t.term_type;
*)
  (t.term_type, term_node denv ~label t.term_node lvm old)

and tlval denv ~label (host,offset) _lvm _old =
  match host,offset with
    | TResult _, TNoOffset -> Term.t_var !result_pvsymbol.Ity.pv_vs
    | TVar lv, TNoOffset ->
      begin
        let t =
          match lv.lv_origin with
            | None -> Term.t_var (get_lvar lv)
            | Some v ->
              let e,is_mutable = get_var denv v in
              let pvs = match e with
                  | Dexpr.DEpv pvs -> pvs
                  | Dexpr.DEvar (s,_dvty) ->
                     Self.fatal "found var %s" s
                  | _ -> assert false
              in
              if is_mutable then
                t_app get_logic_fun [Term.t_var pvs.Ity.pv_vs]
              else
                Term.t_var pvs.Ity.pv_vs
        in
        match label with
          | Here -> t
          | Old ->
             Self.not_yet_implemented "tlval TVar/Old"
             (* label "0" in Why3 ? *)
          | At _lab ->
            (* t_app Mlw_wp.fs_at [t; ??? lab] *)
             Self.not_yet_implemented "tlval TVar/At"
      end
    | TVar _, (TField (_, _)|TModel (_, _)|TIndex (_, _)) ->
      Self.not_yet_implemented "tlval TVar"
    | TResult _, _ ->
      Self.not_yet_implemented "tlval Result"
(*
    | TMem({term_node = TBinOp((PlusPI|IndexPI),t,i)}), TNoOffset ->
      (* t[i] *)
      t_app map_get [snd(term ~label t lvm old);snd(term ~label i lvm old)]
 *)
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

let rec predicate denv ~label p lvm old =
  match p with
    | Pfalse -> Term.t_false
    | Ptrue -> Term.t_true
    | Prel (op, t1, t2) -> rel (term denv ~label t1 lvm old) op (term denv ~label t2 lvm old)
    | Pforall (lv, p) ->
      let l = List.map create_lvar lv in
      Term.t_forall_close l [] (predicate_named denv ~label p lvm old)
    | Pimplies (p1, p2) ->
      Term.t_implies (predicate_named denv ~label p1 lvm old) (predicate_named denv ~label p2 lvm old)
    | Pand (p1, p2) ->
      Term.t_and (predicate_named denv ~label p1 lvm old) (predicate_named denv ~label p2 lvm old)
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
    | Psubtype (_, _)
    | Pvalid_function _ ->
        Self.not_yet_implemented "predicate"

and predicate_named denv ~label p lvm old = predicate denv ~label p.content lvm old



(**********************)
(* logic declarations *)
(**********************)

let use th1 th2 =
  let name = th2.Theory.th_name in
  Theory.close_scope
    (Theory.use_export (Theory.open_scope th1 name.Ident.id_string) th2)
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
      let th = use th int_theory.Pmodule.mod_theory in
      let th = use th real_theory.Pmodule.mod_theory in
(*
      let th = use th map_theory.Pmodule.mod_theory in
 *)
      let th = List.fold_left use th theories in
      let th = List.fold_left add_decl th (List.rev decls) in
      let th = Theory.close_theory th in
      th :: theories

let rec logic_decl ~in_axiomatic a _loc (theories,decls) =
  let denv = Dexpr.denv_empty in
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
                  let _ty,d = term denv ~label:Here d Term.Mvs.empty (fun v _ -> v) in
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
                pr (predicate_named denv ~label:Here p Term.Mvs.empty (fun v _ -> v))
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




******)

(**************)
(* statements *)
(**************)


let seq ?loc e1 e2 =
  let letdefn = (Ident.id_fresh "_tmp", false, Expr.RKlocal,e1) in
  Dexpr.dexpr ?loc (Dexpr.DElet(letdefn,e2))


let annot denv a e =
  match a.annot_content with
  | AAssert ([],pred) ->
    Self.not_yet_implemented "annot AAssert"
(*
    let p = predicate_named denv ~label:Here pred in
    let a = Dexpr.dexpr (* todo ~loc *) (Dexpr.DEassert(Expr.Assert, p)) in
    seq ?loc:e.Dexpr.de_loc a e
 *)
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

let loop_annot denv a =
  let inv,var =
    List.fold_left
      (fun (inv,var) a ->
       match a.annot_content with
       | AAssert ([],_pred) ->
          Self.not_yet_implemented "loop_annot AAssert"
       | AAssert(_labels,_pred) ->
          Self.not_yet_implemented "loop_annot AAssert"
       | AStmtSpec _ ->
          Self.not_yet_implemented "loop_annot AStmtSpec"
       | AInvariant([],true,p) ->
          (p :: inv,var)
      | AInvariant _ ->
        Self.not_yet_implemented "loop_annot AInvariant"
      | AVariant (t, None) ->
        (inv,t :: var)
      | AVariant (_var, Some _) ->
        Self.not_yet_implemented "loop_annot AVariant/Some"
      | AAssigns _ ->
        Self.not_yet_implemented "loop_annot AAssigns"
      | AAllocation _ ->
        Self.not_yet_implemented "loop_annot AAllocation"
      | APragma _ ->
        Self.not_yet_implemented "loop_annot APragma")
    ([], []) a
  in
  ([],[])
(*
  (fun lvm old ->
   List.rev_map
     (fun p -> predicate_named denv ~label:Here p lvm old)
     inv),
  (fun lvm old ->
   List.rev_map
     (fun t -> (snd(term denv ~label:Here t lvm old),None))
     var)
 *)

let binop op e1 e2 =
  let rs,_ty,_ty' =
    match op with
      | PlusA -> uadd32_fun, mlw_uint32_type, mlw_uint32_type
      | MinusA -> usub32_fun, mlw_uint32_type, mlw_uint32_type
      | Mult -> umul32_fun, mlw_uint32_type, mlw_uint32_type
      | Lt -> ult32_fun, mlw_uint32_type, Ity.ity_bool
      | Le -> ule32_fun, mlw_uint32_type, Ity.ity_bool
      | Gt -> ugt32_fun, mlw_uint32_type, Ity.ity_bool
      | Ge -> uge32_fun, mlw_uint32_type, Ity.ity_bool
      | Eq -> ueq32_fun, mlw_uint32_type, Ity.ity_bool
      | Ne -> une32_fun, mlw_uint32_type, Ity.ity_bool
      | PlusPI|IndexPI|MinusPI|MinusPP ->
        Self.not_yet_implemented "binop plus/minus"
      | Div|Mod ->
        Self.not_yet_implemented "binop div/mod"
      | Shiftlt|Shiftrt ->
        Self.not_yet_implemented "binop shift"
      | BAnd|BXor|BOr|LAnd|LOr ->
        Self.not_yet_implemented "binop bool"
  in
  de_app2 rs e1 e2

let unop op e =
  let rs,_ty,_ty' =
    match op with
      | Neg -> (* Unary minus *)
        Self.not_yet_implemented "unop Neg"
      (*        neg32_fun, mlw_int32_type, mlw_int32_type*)
      | BNot -> (* Bitwise complement (~) *)
        Self.not_yet_implemented "unop BNot"
      | LNot -> (* Logical Not (!) *)
        Self.not_yet_implemented "unop LNot"
  in
  de_app1 rs e

let constant c =
  match c with
  | CInt64(t,IInt, sopt) ->
    let s =
      match sopt with
        | Some s -> s
        | None -> Integer.to_string t
    in
    let n = e_const_int s  in
    e_app1 uint32ofint_fun n
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
      unop op (expr denv e)
    | CastE (ty, e) ->
      let e' = expr denv e in
      begin
        match ty, Cil.typeOf e with
          | TInt(ILong,_attr1), TInt(IInt,_attr2) ->
            de_app1 int64ofint_fun (de_app1 uint32_to_int_fun e')
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

and lval denv (host,offset) =
  match host,offset with
    | Var v, NoOffset ->
      let e,is_mutable = get_var denv v in
      if is_mutable then
        begin try
                de_app1 get_fun (Dexpr.dexpr e)
          with e ->
            Self.fatal "Exception raised during application of !@ %a@."
              Exn_printer.exn_printer e
        end
      else (Dexpr.dexpr e)
    | Var _, (Field (_, _)|Index (_, _)) ->
      Self.not_yet_implemented "lval Var"
    | Mem({enode = BinOp((PlusPI|IndexPI),_e,_i,_ty)}), NoOffset ->
      (* e[i] -> Map.get e i *)
(*
      let e = expr e in
      let ity =
        match ty with
          | TPtr(t,_) -> ctype t
          | _ -> assert false
      in
      let i = expr i in
      let i = de_app1 uint32_to_int_fun i in
      de_app2 map_get e i
 *)
      Self.not_yet_implemented "lval Mem e+i"
  | Mem _, _ ->
      Self.not_yet_implemented "lval Mem"

let functional_expr e =
  match e.enode with
    | Lval (Var _v, NoOffset) ->
       Self.not_yet_implemented "functional_expr Lval"
(*
      let rs,_cexp = get_function v in
      Dexpr.dexpr(Dexpr.DErs rs) *)
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

let assignment denv (lhost,offset) e _loc =
  match lhost,offset with
    | Var v , NoOffset ->
      let v,is_mutable = get_var denv v in
      if is_mutable then
         begin
           Self.result "creating call to (:=)";
           let de = de_app2 set_fun (Dexpr.dexpr v) e in
           Self.result "OK";
           de
         end
      else
        Self.not_yet_implemented "mutation of formal parameters"
    | Var _ , Field _ ->
      Self.not_yet_implemented "assignment Var/Field"
    | Var _ , Index _ ->
      Self.not_yet_implemented "assignment Var/Index"
    | Mem _, _ ->
      Self.not_yet_implemented "assignment Mem"

let instr denv i =
  match i with
  | Set(lv,e,loc) -> assignment denv lv (expr denv e) loc
  | Call (None, e, el, _loc) ->
    let e = functional_expr e in
    List.fold_left
      (fun acc e -> de_app acc (expr denv e))
      e el
  | Call (Some lv, e, el, loc) ->
    let e = functional_expr e in
    let e =
    List.fold_left
      (fun acc e -> de_app acc (expr denv e))
      e el
    in
    assignment denv lv e loc
  | Asm _ ->
    Self.not_yet_implemented "instr Asm"
  | Skip _loc -> e_void
  | Code_annot (_, _) ->
    Self.not_yet_implemented "instr Code_annot"


let exc_break =
  Ity.create_xsymbol (Ident.id_fresh "Break") Ity.ity_unit

let rec stmt denv s =
  match s.skind with
    | Instr i ->
      let annotations = Annotations.code_annot s in
      let e =
        List.fold_right (annot denv) annotations (instr denv i)
      in e
    | Block b -> block denv b
    | Return (None, _loc) -> e_void
    | Return (Some e, _loc) ->
      expr denv e
    | Goto (_, _) ->
      Self.not_yet_implemented "stmt Goto"
    | Break _loc ->
      Dexpr.dexpr (Dexpr.DEraise(exc_break,e_void))
    | Continue _ ->
      Self.not_yet_implemented "stmt Continue"
    | If (c, e1, e2, _loc) ->
      Dexpr.dexpr(Dexpr.DEif(expr denv c,block denv e1,block denv e2))
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
      let inv, var = loop_annot denv annots in
      let v = Ident.id_fresh "_dummy" in
      let loop = Ewhile(e_true,inv,var,block body) in
      let pat = Dexpr.dpattern(Dexpr.DPvar(v,false)) in
      Dexpr.dexpr(Dexpr.DEtry(loop,[exc_break,pat,e_void]))
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
      | [] -> Etuple []
      | [s] -> stmt s
      | s::r -> seq (stmt s) (mk_seq r)
  in
  mk_seq b.bstmts






(*************)
(* contracts *)
(*************)

let extract_simple_contract c =
  let denv = Dexpr.denv_empty in
  let pre,post,ass = List.fold_left
    (fun (pre,post,ass) b ->
      if not (Cil.is_default_behavior b) then
        Self.not_yet_implemented "named behaviors";
      if b.b_assumes <> [] then
        Self.not_yet_implemented "assumes clause";
      let pre = []
(*
        List.fold_left
          (fun acc f -> (identified_proposition f) :: acc)
          pre b.b_requires
 *)
      in
      let post = []
(*
        List.fold_left
          (fun acc (k,f) ->
            if k <> Normal then
              Self.not_yet_implemented "abnormal termination post-condition";
            (identified_proposition f) :: acc)
          post b.b_post_cond
 *)
      in
(*
      let ass =
        match b.b_assigns with
        | WritesAny -> ass
        | Writes l ->
          let l = List.map (fun (t,_) ->
            term (* ~in_contract:true Logic_const.here_label *) denv t.it_content) l in
          match ass with
          | None -> Some l
          | Some l' -> Some (l@l')
      in
 *)
      (pre,post, ass))
    ([],[],None) c.spec_behavior
  in
  (pre, post, ass)


(*************************)
(* function declarations *)
(*************************)


let fundecl fdec :
      ident * ghost * Expr.rs_kind * binder list * pty option * Ity.mask * spec * expr
  =
  let fun_id = fdec.svar in
  let kf = Globals.Functions.get fun_id in
  Self.log "processing function %a" Kernel_function.pretty kf;
  let args = Kernel_function.get_formals kf in
  let body = fdec.sbody in
  let contract = Annotations.funspec kf in
  let pre,post,_ass = extract_simple_contract contract in
  let locals = Kernel_function.get_locals kf in
  let ret_type = Kernel_function.get_return_type kf in
  (* parameters *)
  let binders =
    if args = [] then ([Loc.dummy_position,None,false,None])
    else
      List.map
        (fun v -> (Loc.dummy_position,Some (ident v.vname),false,None))
        args
  in
  let spec =
    {
      sp_pre     = []; (* TODO*)
      sp_post    = []; (* TODO*)
      sp_xpost   = []; (* TODO*)
      sp_reads   = []; (* TODO*)
      sp_writes  = []; (* TODO*)
      sp_variant = []; (* TODO*)
      sp_checkrw = true;
      sp_diverge = false;  (* TODO*)
    }
  in
  let body = { expr_desc = block body ; expr_loc = Loc.dummy_position }
  in
  (ident fun_id.vname,
   false,
   Expr.RKfunc,
   binders,
   None,
   Ity.MaskVisible,
   spec,
   body)

(*
  let body denv =
    let rec add_locals denv l =
      match l with
      | [] -> block denv body
      | v::rem ->
         Self.log "local variable %s" v.vname;
         let _ity,def = ctype_and_default v.vtype in
         create_var v true;
         let def = de_app1 ref_fun def in
         let letdefn = (Ident.id_fresh v.vname,false,Expr.RKlocal,def) in
         let denv = Dexpr.denv_add_let denv letdefn in
         Dexpr.dexpr(Dexpr.DElet(letdefn,add_locals denv rem))
    in
(*
    let body =
      List.fold_right
        (fun v acc ->
         let _,letdef = create_var v in
         Dexpr.dexpr(Dexpr.DElet(letdef,acc)))
        (Kernel_function.get_locals kf) body
    in
 *)

    let body = add_locals denv locals in
    let spec_later lvm old (ret_type:Ity.ity) =
(**)
      let result =
        Ity.create_pvsymbol (Ident.id_fresh "result") ret_type
      in
      result_pvsymbol := result;
 (**)
      {
        Dexpr.ds_pre =
          List.map (fun t -> predicate_named denv ~label:Here t lvm old) pre;
        Dexpr.ds_post =
          List.map (fun t -> (result,predicate_named denv ~label:Here t lvm old)) post;
        Dexpr.ds_xpost = Ity.Mexn.empty;
        Dexpr.ds_reads = [];
        Dexpr.ds_writes = [];
        Dexpr.ds_diverge = false;
        Dexpr.ds_checkrw = true;
      }
    in
    let variants _lvm _old = [Term.t_nat_const 0,None] in
    (spec_later,variants,body)
  in
  let id = Ident.id_fresh fun_id.vname in
  let predef = (id,true,Expr.RKfunc,binders,Dexpr.dity_of_ity (ctype ret_type),Ity.MaskVisible, body) in
  let denv,def = Dexpr.drec_defn denv_global [predef] in
  denv,Dexpr.rec_defn def

       *)



(***********************)
(* global declarations *)
(***********************)


let global (theories,lemmas,functions) g =
  match g with
    | GFun (fdec,_) ->
      let f = fundecl fdec in
      (theories,lemmas, f ::functions)
   | GVar (_vi, _init, _loc) ->
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
      Self.not_yet_implemented "global: GVar"
(*
     let _,dlet = create_var vi in
     let d = Dexpr.let_defn dlet in
     (theories,lemmas,denv,(Pdecl.create_let_decl d)::functions)
 *)

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
    | GVarDecl(_vi,_location) ->
      Self.not_yet_implemented "global: GVarDecl"
(*
       let _,dlet = create_var vi in
       let d = Dexpr.let_defn dlet in
       (theories,lemmas,denv,(Pdecl.create_let_decl d)::functions)
 *)
    | GAnnot (a, loc) ->
      Self.not_yet_implemented "global: GAnnot"
(*
      let (t,l) = logic_decl ~in_axiomatic:false a loc (theories,lemmas) in
      (t,l,denv,functions)
 *)
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
    Pmodule.add_pdecl ~vc:true m d
  with
      Not_found ->
        Self.fatal "add_pdecl %a" (Pp.print_list Pp.comma print_id)
          (Ident.Sid.elements d.Pdecl.pd_news)

(*
let use m th =
  let name = th.Theory.th_name in
  Pmodule.close_scope
    (Pmodule.use_export
       (Pmodule.open_scope m name.Ident.id_string)
       th)
    true
 *)

(*
let use_module m modul =
  let name = modul.Pmodule.mod_theory.Theory.th_name in
  Pmodule.close_scope
    (Pmodule.use_export
       (Pmodule.open_scope m name.Ident.id_string)
       modul)
    true
 *)


let use_import_module m =
  let q = qualid_of_list m in
  Typing.add_decl Loc.dummy_position (Duse q)

let prog p =
   try
    (* Self.result "Starting translation"; *)
    let theories,decls,functions =
      List.fold_left global ([],[],[]) p.globals
    in
    Self.result "found %d logic decl(s)" (List.length decls);
(*
    let theories =
      add_decls_as_theory theories
        (Ident.id_fresh global_logic_decls_theory_name) decls
    in
 *)
    Self.result "made %d theory(ies)" (List.length theories);
(*
    let m = Pmodule.create_module env
      (Ident.id_fresh programs_module_name)
    in
 *)
    Typing.open_file env ["Jessie3"];
    Typing.open_module {
        id_str = programs_module_name;
        id_lab = [];
        id_loc = Loc.dummy_position;
      };
    use_import_module ["int";"Int"];
(*
    let m = use_module m real_theory in
    let m = use_module m map_theory in
 *)
(*
    let m = List.fold_left use_module m theories in
 *)
    use_import_module ["ref"; "Ref"];
    use_import_module ["bv"; "BV32"];
    List.iter
      (fun f ->
       Typing.add_decl Loc.dummy_position (Drec [f]))
      (List.rev functions);
    Self.result "made %d function(s)" (List.length functions);
    Typing.close_module Loc.dummy_position;
    let modules = Typing.close_file () in
    Stdlib.Mstr.fold
      (fun _ m acc -> m.Pmodule.mod_theory :: acc)
      modules []
(*
    List.rev (m.Pmodule.mod_theory :: theories)
 *)
  with (Exit | Not_found| Ty.TypeMismatch _
           | Ity.TypeMismatch _ | Decl.UnknownIdent _) as e  ->
    Self.fatal "Exception raised during translation to Why3:@ %a@."
      Exn_printer.exn_printer e

    (* | Ity.TypeMismatch(ity1,ity2,_ity_subst) ->  *)
    (*   Self.fatal "TypeMismatch(%a,%a,_)" *)
    (*         Mlw_pretty.print_ity ity1 Mlw_pretty.print_ity ity2 *)
