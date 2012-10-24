let help = "Checks ACSL contracts using Why3"

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

let unit_type = Ty.ty_tuple []

let ctype ty =
  match ty with
    | TVoid _attr -> unit_type
    | TInt (_, _)
    | TFloat (_, _)
    | TPtr (_, _)
    | TArray (_, _, _, _)
    | TFun (_, _, _, _)
    | TNamed (_, _)
    | TComp (_, _, _)
    | TEnum (_, _)
    | TBuiltin_va_list _
    -> Self.not_yet_implemented "ctype"

let logic_type ty =
  match ty with
    | Linteger -> int_type
    | Lreal -> real_type
    | Ctype _
    | Ltype (_, _)
    | Lvar _
    | Larrow (_, _) ->
        Self.not_yet_implemented "logic_type"

let constant c =
  match c with
    | Integer(_value,Some s) -> Term.ConstInt (Term.IConstDecimal s)
    | Integer(_value,None) ->
      Self.not_yet_implemented "constant Integer None"
    | LReal(_value,s) ->
      (* FIXME *)
      if s = "0.0" then
        Term.ConstReal (Term.RConstDecimal ("0","0",None))
      else
        Self.not_yet_implemented "constant LReal"
    | (LStr _|LWStr _|LChr _|LEnum _) ->
      Self.not_yet_implemented "constant"

let bin (ty1,t1) op (ty2,t2) =
  match op,ty1,ty2 with

    | PlusA,Linteger,Linteger -> Term.t_app_infer add_int [t1;t2]
    | PlusA,Lreal,Lreal -> Term.t_app_infer add_real [t1;t2]

    | MinusA,Linteger,Linteger -> Term.t_app_infer sub_int [t1;t2]
    | MinusA,Lreal,Lreal -> Term.t_app_infer sub_real [t1;t2]

    | Mult,Linteger,Linteger -> Term.t_app_infer mul_int [t1;t2]
    | Mult,Lreal,Lreal -> Term.t_app_infer mul_real [t1;t2]

    | PlusA,ty1,ty2 -> Self.not_yet_implemented "bin PlusA(%a,%a)"
      Cil.d_logic_type ty1 Cil.d_logic_type ty2
    | MinusA,_,_ -> Self.not_yet_implemented "bin MinusA"
    | Mult,_,_ -> Self.not_yet_implemented "bin Mult"
    | ((PlusPI|IndexPI|MinusPI|MinusPP|Div|Mod|Shiftlt|Shiftrt|Lt|Gt|
 Le|Ge|Eq|Ne|BAnd|BXor|BOr|LAnd|LOr),_, _)
      -> Self.not_yet_implemented "bin"

let unary op (ty,t) =
  match op,ty with
    | Neg,Linteger -> Term.t_app_infer minus_int [t]
    | Neg,Lreal -> Term.t_app_infer minus_real [t]
    | Neg,_ -> Self.not_yet_implemented "unary Neg,_"
    | BNot,_ -> Self.not_yet_implemented "unary BNot"
    | LNot,_ -> Self.not_yet_implemented "unary LNot"

let bound_vars = Hashtbl.create 257

let create_lvar v =
  let id = Ident.id_fresh v.lv_name in
  let vs = Term.create_vsymbol id (logic_type v.lv_type) in
(*
  Self.result "binding variable %d" v.lv_id;
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
  let id = Ident.id_fresh li.l_var_info.lv_name in
  let vs = Term.create_lsymbol id (logic_type v.lv_type) in
(* val create_lsymbol : preid -> ty list -> ty option -> lsymbol *)
(*
  Self.result "binding variable %d" v.lv_id;
*)
  Hashtbl.add bound_vars v.lv_id vs;
  vs

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
            Term.t_app_infer ls args
          | _ -> Self.not_yet_implemented "term_node Tapp with labels"
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

let rel (ty1,t1) op (ty2,t2) =
  match op,ty1,ty2 with
    | Req,_,_ -> Term.t_equ t1 t2
    | Rge,Linteger,Linteger -> Term.t_app_infer ge_int [t1;t2]
    | Rge,Lreal,Lreal -> Term.t_app_infer ge_real [t1;t2]
    | Rge,_,_ ->
      Self.not_yet_implemented "rel Rge"
    | (Rlt|Rgt|Rle|Rneq),_,_ ->
      Self.not_yet_implemented "rel"

let rec predicate p =
  match p with
    | Pfalse -> Term.t_false
    | Ptrue -> Term.t_true
    | Prel (op, t1, t2) -> rel (term t1) op (term t2)
    | Pforall (lv, p) ->
      let l = List.map create_lvar lv in
      Term.t_forall_close l [] (predicate_named p)
    | Papp (_, _, _)
    | Pseparated _
    | Pand (_, _)
    | Por (_, _)
    | Pxor (_, _)
    | Pimplies (_, _)
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

let use th1 th2 =
  let name = th2.Theory.th_name in
  Theory.close_namespace
    (Theory.use_export (Theory.open_namespace th1 name.Ident.id_string) th2)
    true

let add_decls_as_theory theories id decls =
  match decls with
    | [] -> theories
    | _ ->
      let th = Theory.create_theory id in
      let th = use th int_theory in
      let th = use th real_theory in
      let th = List.fold_left Theory.add_decl th decls in
      let th = Theory.close_theory th in
      th :: theories

let rec annot ~in_axiomatic a _loc (theories,decls) =
  match a with
    | Dtype (lt, loc) -> 
      let targs = 
        List.map (fun s -> Ty.create_tvsymbol (Ident.id_fresh s)) lt.lt_params 
      in
      let tdef = match lt.lt_def with
          | None -> None
          | Some _ -> Self.not_yet_implemented "annot Dtype non abstract"
      in
      let ts = 
        Ty.create_tysymbol 
          (Ident.id_user lt.lt_name (Loc.extract loc)) targs tdef 
      in
      let d = Decl.create_ty_decl ts in
      (theories,d::decls)
    | Dfun_or_pred (li, _loc) -> 
      begin
        match li.l_labels, li.l_tparams,li.l_body with
          | [],[],None ->
            Self.not_yet_implemented "Dfun_or_pred without body"
            (* create_param_decl : lsymbol -> decl *)
          | [],[],Some d ->
            (* make_ls_defn : lsymbol -> vsymbol list -> term -> logic_decl *)
            (* create_logic_decl : logic_decl list -> decl *)
          | _ ->
            Self.not_yet_implemented "Dfun_or_pred with labels or vars"

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
      let theories = add_decls_as_theory theories (Ident.id_fresh "Decls") decls in
      let (t,decls'') =
        List.fold_left
          (fun acc d -> annot ~in_axiomatic:true d loc acc)
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
        -> Self.not_yet_implemented "annot"

let identified_proposition p =
  { name = p.ip_name; loc = p.ip_loc; content = p.ip_content }

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

let fundecl fdec =
  let fun_id = fdec.svar in
  let kf = Globals.Functions.get fun_id in
  Self.log "processing function %a" Kernel_function.pretty kf;
  let _formals = List.map
      (fun v -> (v.vname, ctype v.vtype))
      (Kernel_function.get_formals kf)
  in
  let body = fdec.sbody in
  let _vars = List.map
      (fun v -> (v.vname, ctype v.vtype)) 
      (Kernel_function.get_locals kf)
  in
  let contract = Annotations.funspec kf in
  let _pre,_post,_ass = extract_simple_contract contract in
  let _ret_type = ctype (Kernel_function.get_return_type kf) in
  let _body = body.bstmts in
  ()

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
      let (t,l) = annot ~in_axiomatic:false a loc (theories,lemmas) in
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


let prog p =
  try
    let theories,decls,_functions =
      List.fold_left global ([],[],[]) p.globals 
    in
    Self.result "found %d decls" (List.length decls);
    let theories =
      add_decls_as_theory theories (Ident.id_fresh "Decls") decls
    in
    Self.result "made %d theories" (List.length theories);
    theories
  with
      Decl.UnknownIdent(s) ->
        Self.fatal "unknown identifier %s" s.Ident.id_string
