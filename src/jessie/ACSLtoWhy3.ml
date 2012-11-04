(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
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
    let config : Whyconf.config = Whyconf.read_config None in
    (* the [main] section of the config file *)
    let main : Whyconf.main = Whyconf.get_main config in
    let env : Env.env = Env.create_env (Whyconf.loadpath main) in
    env,config
  with e ->
    Self.fatal "Exception raised in Why3 env:@ %a" Exn_printer.exn_printer e

let find th s = Theory.ns_find_ls th.Theory.th_export [s]

(* int.Int theory *)
let int_type : Ty.ty = Ty.ty_int
let int_theory : Theory.theory = Env.find_theory env ["int"] "Int"
let add_int : Term.lsymbol = find int_theory "infix +"
let sub_int : Term.lsymbol = find int_theory "infix -"
let minus_int : Term.lsymbol = find int_theory "prefix -"
let mul_int : Term.lsymbol = find int_theory "infix *"
let ge_int : Term.lsymbol = find int_theory "infix >="

(* real.Real theory *)
let real_type : Ty.ty = Ty.ty_real
let real_theory : Theory.theory = Env.find_theory env ["real"] "Real"
let add_real : Term.lsymbol = find real_theory "infix +"
let sub_real : Term.lsymbol = find real_theory "infix -"
let minus_real : Term.lsymbol = find real_theory "prefix -"
let mul_real : Term.lsymbol = find real_theory "infix *"
let ge_real : Term.lsymbol = find real_theory "infix >="


(* ref.Ref module *)

let ref_modules, ref_theories = 
  Env.read_lib_file (Mlw_main.library_of_env env) ["ref"]

let ref_module : Mlw_module.modul = Stdlib.Mstr.find "Ref" ref_modules

let ref_type : Mlw_ty.T.itysymbol = 
  match
    Mlw_module.ns_find_ts ref_module.Mlw_module.mod_export ["ref"]
  with
    | Mlw_module.PT itys -> itys
    | Mlw_module.TS _ -> assert false

let ref_fun : Mlw_expr.psymbol = 
  match
    Mlw_module.ns_find_ps ref_module.Mlw_module.mod_export ["ref"]
  with
    | Mlw_module.PS p -> p
    | _ -> assert false


(*********)
(* types *)
(*********)

let unit_type = Ty.ty_tuple []

let ctype ty =
  match ty with
    | TVoid _attr -> Mlw_ty.ity_unit
    | TInt (_, _) -> Mlw_ty.ity_pur Ty.ts_int []
    | TFloat (_, _)
    | TPtr (_, _)
    | TArray (_, _, _, _)
    | TFun (_, _, _, _)
    | TNamed (_, _)
    | TComp (_, _, _)
    | TEnum (_, _)
    | TBuiltin_va_list _
    -> Self.not_yet_implemented "ctype"

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

let constant c =
  match c with
    | Integer(_value,Some s) -> 
      let c = Literals.integer s in Term.ConstInt c
    | Integer(_value,None) ->
      Self.not_yet_implemented "constant Integer None"
    | LReal(_value,s) ->
      let c = Literals.floating_point s in Term.ConstReal c
    | (LStr _|LWStr _|LChr _|LEnum _) ->
      Self.not_yet_implemented "constant"

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
      Cil.d_logic_type ty1 Cil.d_logic_type ty2
    | MinusA,_,_ -> Self.not_yet_implemented "bin MinusA"
    | Mult,_,_ -> Self.not_yet_implemented "bin Mult"
    | ((PlusPI|IndexPI|MinusPI|MinusPP|Div|Mod|Shiftlt|Shiftrt|Lt|Gt|
 Le|Ge|Eq|Ne|BAnd|BXor|BOr|LAnd|LOr),_, _)
      -> Self.not_yet_implemented "bin"

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
(*
  Self.result "create logic variable %d" v.lv_id;
*)
  Hashtbl.add bound_vars v.lv_id vs;
  vs

let get_lvar lv =
  try
    Hashtbl.find bound_vars lv.lv_id
  with Not_found ->
    Self.fatal "variable %d not found" lv.lv_id

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

let tlval (host,offset) =
  match host,offset with
    | TVar lv, TNoOffset -> Term.t_var (get_lvar lv)
    | TVar _, (TField (_, _)|TModel (_, _)|TIndex (_, _)) ->
      Self.not_yet_implemented "tlval TVar"
    | ((TResult _|TMem _), _) ->
      Self.not_yet_implemented "tlval"

let rec term_node t =
  match t with
    | TConst cst -> Term.t_const (constant cst)
    | TLval lv -> tlval lv
    | TBinOp (op, t1, t2) -> bin (term t1) op (term t2)
    | TUnOp (op, t) -> unary op (term t)
    | TCastE (_, _) -> Self.not_yet_implemented "term_node TCastE"
    | Tapp (li, labels, args) ->
      begin
        match labels with
          | [] ->
            let ls = get_lsymbol li in
            let args = List.map (fun x -> snd(term x)) args in
            t_app ls args
          | _ -> 
            Self.not_yet_implemented "term_node Tapp with labels"
      end
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
    | Tat (_, _)
    | Tbase_addr (_, _)
    | Toffset (_, _)
    | Tblock_length (_, _)
    | Tnull
    | TCoerce (_, _)
    | TCoerceE (_, _)
    | TUpdate (_, _, _)
    | Ttypeof _
    | Ttype _
    | Tempty_set
    | Tunion _
    | Tinter _
    | Tcomprehension (_, _, _)
    | Trange (_, _)
    | Tlet (_, _) ->
      Self.not_yet_implemented "term_node"

and term t = (t.term_type, term_node t.term_node)



(****************)
(* propositions *)
(****************)

let rel (ty1,t1) op (ty2,t2) =
  match op,ty1,ty2 with
    | Req,_,_ -> Term.t_equ t1 t2
    | Rneq,_,_ -> Term.t_neq t1 t2
    | Rge,Linteger,Linteger -> t_app ge_int [t1;t2]
    | Rge,Lreal,Lreal -> t_app ge_real [t1;t2]
    | Rge,_,_ ->
      Self.not_yet_implemented "rel Rge"
    | (Rlt|Rgt|Rle),_,_ ->
      Self.not_yet_implemented "rel"

let rec predicate p =
  match p with
    | Pfalse -> Term.t_false
    | Ptrue -> Term.t_true
    | Prel (op, t1, t2) -> rel (term t1) op (term t2)
    | Pforall (lv, p) ->
      let l = List.map create_lvar lv in
      Term.t_forall_close l [] (predicate_named p)
    | Pimplies (p1, p2) ->
      Term.t_implies (predicate_named p1) (predicate_named p2)
    | Papp (_, _, _)
    | Pseparated _
    | Pand (_, _)
    | Por (_, _)
    | Pxor (_, _)
    | Piff (_, _)
    | Pnot _
    | Pif (_, _, _)
    | Plet (_, _)
    | Pexists (_, _)
    | Pat (_, _)
    | Pvalid_read (_, _)
    | Pvalid (_, _)
    | Pinitialized (_, _)
    | Pallocable (_, _)
    | Pfreeable (_, _)
    | Pfresh (_, _, _, _)
    | Psubtype (_, _) ->
        Self.not_yet_implemented "predicate"

and predicate_named p = predicate p.content






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
                  let (_ty,d) = term d in
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
                pr (predicate_named p)
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

let program_vars = Hashtbl.create 257

let any _ty = Mlw_expr.e_int_const "0000" (* TODO : ref *)

let create_var v =
  let id = Ident.id_fresh v.vname in
  let ty = Mlw_ty.vty_value (ctype v.vtype) in
  let def = 
    Mlw_expr.e_app 
      (Mlw_expr.e_arrow ref_fun
         (Mlw_ty.vty_arrow [] (Mlw_ty.VTvalue ty))) 
      [any ty] 
  in
  let let_defn = Mlw_expr.create_let_defn id def in
  let vs = match let_defn.Mlw_expr.let_sym with
    | Mlw_expr.LetV vs -> vs
    | Mlw_expr.LetA _ -> assert false
  in
(*
  Self.result "create program variable %s (%d)" v.vname v.vid;
*)
  Hashtbl.add program_vars v.vid vs;
  let_defn

let get_var v =
  try
    Hashtbl.find program_vars v.vid
  with Not_found ->
    Self.fatal "program variable %s (%d) not found" v.vname v.vid


let lval (host,offset) =
  match host,offset with
    | Var v, NoOffset -> Mlw_expr.e_value (get_var v)
    | Var _, (Field (_, _)|Index (_, _)) ->
      Self.not_yet_implemented "lval Var"
    | Mem _, _ ->
      Self.not_yet_implemented "lval Mem"


let seq e1 e2 =
  let l = Mlw_expr.create_let_defn (Ident.id_fresh "_tmp") e1 in
  Mlw_expr.e_let l e2

let annot a e =
  match (Annotations.code_annotation_of_rooted a).annot_content with
  | AAssert ([],pred) ->
    let p = predicate_named pred in
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

let expr e =
  match e.enode with
    | Const _c -> (* constant c *)
      Self.not_yet_implemented "expr Const"
    | Lval lv -> lval lv
    | SizeOf _
    | SizeOfE _
    | SizeOfStr _
    | AlignOf _
    | AlignOfE _
    | UnOp (_, _, _)
    | BinOp (_, _, _, _)
    | CastE (_, _)
    | AddrOf _
    | StartOf _
    | Info (_, _)
      -> Self.not_yet_implemented "expr"

let instr i =
  match i with
  | Set(_lv,_e,_loc) ->
    Self.not_yet_implemented "instr Set"
  | Call (_, _, _, _) ->
    Self.not_yet_implemented "instr Call"
  | Asm (_, _, _, _, _, _) ->
    Self.not_yet_implemented "instr Asm"
  | Skip _loc ->
    Mlw_expr.e_void
  | Code_annot (_, _) ->
    Self.not_yet_implemented "instr Code_annot"

let stmt s =
  match s.skind with
    | Instr i ->
      let annotations = Annotations.code_annot s in
      let e =
        List.fold_right annot annotations (instr i)
      in e
    | Block _ ->
      Self.not_yet_implemented "stmt Block"
    | Return (None, _loc) ->
      Mlw_expr.e_void
    | Return (Some e, _loc) ->
      expr e
    | Goto (_, _) ->
      Self.not_yet_implemented "stmt Goto"
    | Break _ ->
      Self.not_yet_implemented "stmt Break"
    | Continue _ ->
      Self.not_yet_implemented "stmt Continue"
    | If (_, _, _, _) ->
      Self.not_yet_implemented "stmt If"
    | Switch (_, _, _, _) ->
      Self.not_yet_implemented "stmt Switch"
    | Loop (_, _, _, _, _) ->
      Self.not_yet_implemented "stmt Loop"
    | UnspecifiedSequence _ ->
      Self.not_yet_implemented "stmt UnspecifiedSequence"
    | TryFinally (_, _, _) ->
      Self.not_yet_implemented "stmt TryFinally"
    | TryExcept (_, _, _, _) ->
      Self.not_yet_implemented "stmt TryExcept"

let block b =
  List.fold_right (fun s e -> seq (stmt s) e) b.bstmts Mlw_expr.e_void







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
  let formals = 
    match Kernel_function.get_formals kf with
      | [] -> [ "_dummy", Mlw_ty.ity_unit ]
      | l -> List.map (fun v -> (v.vname, ctype v.vtype)) l
  in
  let body = fdec.sbody in
  let contract = Annotations.funspec kf in
  let _pre,_post,_ass = extract_simple_contract contract in
  let _ret_type = ctype (Kernel_function.get_return_type kf) in
  let args =
    List.map 
      (fun (id,ity) -> 
        Mlw_ty.create_pvsymbol (Ident.id_fresh id) (Mlw_ty.vty_value ity))
      formals
  in
  let result = Term.create_vsymbol (Ident.id_fresh "result") unit_type in
  let locals =
    List.map create_var (Kernel_function.get_locals kf)
  in
  let spec = {
    Mlw_ty.c_pre = Term.t_true;
    c_post = Term.t_eps (Term.t_close_bound result Term.t_true);
    c_xpost = Mlw_ty.Mexn.empty;
    c_effect = Mlw_ty.eff_empty;
    c_variant = [];
    c_letrec  = 0;
  }
  in
  let body = block body in
  let full_body = List.fold_right Mlw_expr.e_let locals body in
  let lambda = {
    Mlw_expr.l_args = args;
    l_expr = full_body;
    l_spec = spec;
  }
  in
  let def = Mlw_expr.create_fun_defn (Ident.id_fresh fun_id.vname) lambda in
  Mlw_decl.create_rec_decl [def]






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
     Self.not_yet_implemented "WARNING: Variable %s not translated" vi.vname

    | GVarDecl(_funspec,vi,_location) ->
      Self.error "WARNING: Variable %s not translated" vi.vname;
      (theories,lemmas,functions)
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

let prog p =
  try
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
    let m = List.fold_left use m theories in
    let m = List.fold_left add_pdecl m (List.rev functions) in
    Self.result "made %d function(s)" (List.length functions);
    let m = Mlw_module.close_module m in
    List.rev (m.Mlw_module.mod_theory :: theories) ;
  with
      Decl.UnknownIdent(s) ->
        Self.fatal "unknown identifier %s" s.Ident.id_string
