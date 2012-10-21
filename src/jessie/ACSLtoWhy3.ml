
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

(* int.Int theory *)
let int_type : Ty.ty = Ty.ty_int
let int_theory : Theory.theory = Env.find_theory env ["int"] "Int"
let find_int_theory s = Theory.ns_find_ls int_theory.Theory.th_export [s]
let add_int : Term.lsymbol = find_int_theory "infix +"
let mul_int : Term.lsymbol = find_int_theory "infix *"
let ge_int : Term.lsymbol = find_int_theory "infix >="


let logic_type ty =
  match ty with
    | Linteger -> int_type
    | Ctype _
    | Ltype (_, _)
    | Lvar _
    | Lreal
    | Larrow (_, _) ->
        Self.fatal "logic_type : not yet implemented"

let constant c =
  match c with
    | Integer(_value,Some s) -> Term.ConstInt (Term.IConstDecimal s)
    | Integer(_value,None) ->
      Self.fatal "constant Integer None : not yet implemented"
    | (LStr _|LWStr _|LChr _|LReal (_, _)|LEnum _) ->
      Self.fatal "constant : not yet implemented"

let bin (ty1,t1) op (ty2,t2) =
  match op,ty1,ty2 with
    | PlusA,Linteger,Linteger -> Term.t_app_infer add_int [t1;t2]
    | Mult,Linteger,Linteger -> Term.t_app_infer mul_int [t1;t2]
    | PlusA,_,_ -> Self.fatal "bin PlusA : not yet implemented"
    | Mult,_,_ -> Self.fatal "bin Mult : not yet implemented"
    | ((PlusPI|IndexPI|MinusA|MinusPI|MinusPP|Div|Mod|Shiftlt|Shiftrt|Lt|Gt|
 Le|Ge|Eq|Ne|BAnd|BXor|BOr|LAnd|LOr),_, _)
      -> Self.fatal "bin : not yet implemented"

let bound_vars = Hashtbl.create 257

let tlval (host,offset) =
  match host,offset with
    | TVar lv, TNoOffset ->
      begin
        try
          Term.t_var (Hashtbl.find bound_vars lv.lv_id)
        with Not_found ->
          Self.fatal "variable %d not found" lv.lv_id
      end
    | TVar _, (TField (_, _)|TModel (_, _)|TIndex (_, _)) ->
      Self.fatal "tlval TVar : not yet implemented"
    | ((TResult _|TMem _), _) ->
      Self.fatal "tlval : not yet implemented"

let rec term_node t =
  match t with
    | TConst cst -> Term.t_const (constant cst)
    | TLval lv -> tlval lv
    | TBinOp (op, t1, t2) -> bin (term t1) op (term t2)
    | TUnOp (_, _) -> Self.fatal "term_node TUnOp : not yet implemented"
    | TCastE (_, _) -> Self.fatal "term_node TCastE : not yet implemented"
    | TSizeOf _
    | TSizeOfE _
    | TSizeOfStr _
    | TAlignOf _
    | TAlignOfE _
    | TAddrOf _
    | TStartOf _
    | Tapp (_, _, _)
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
      Self.fatal "term_node : not yet implemented"

and term t = (t.term_type, term_node t.term_node)

let rel (ty1,t1) op (ty2,t2) =
  match op,ty1,ty2 with
    | Req,_,_ -> Term.t_equ t1 t2
    | Rge,Linteger,Linteger -> Term.t_app_infer ge_int [t1;t2]
    | Rge,_,_ ->
      Self.fatal "rel Rge : not yet implemented"
    | (Rlt|Rgt|Rle|Rneq),_,_ ->
      Self.fatal "rel : not yet implemented"

let bind_var v =
  let id = Ident.id_fresh v.lv_name in
  let vs = Term.create_vsymbol id (logic_type v.lv_type) in
  Self.result "binding variable %d" v.lv_id;
  Hashtbl.add bound_vars v.lv_id vs;
  vs

let rec predicate p =
  match p with
    | Pfalse -> Term.t_false
    | Ptrue -> Term.t_true
    | Prel (op, t1, t2) -> rel (term t1) op (term t2)
    | Pforall (lv, p) ->
      let l = List.map bind_var lv in
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
        Self.fatal "predicate : not yet implemented"

and predicate_named p = predicate p.content

let decl annot =
  match annot with
    | Dlemma(name,is_axiom,labels,vars,p,loc) ->
      begin
        if is_axiom then None else
          match labels,vars with
            | [],[] ->
              let pr = Decl.create_prsymbol 
                (Ident.id_user name (Loc.extract loc)) 
              in
              Some (Decl.create_prop_decl Decl.Plemma pr (predicate_named p))
            | _ ->
              Self.fatal "lemma with labels or vars: not yet implemented"
      end
    | Dfun_or_pred (_, _)
    | Dvolatile (_, _, _, _)
    | Daxiomatic (_, _, _)
    | Dtype (_, _)
    | Dinvariant (_, _)
    | Dtype_annot (_, _)
    | Dmodel_annot (_, _)
    | Dcustom_annot (_, _, _)
        -> Self.fatal "annot : not yet implemented"

let annot annot _loc (lemmas,functions) =
  let lemmas =
    match decl annot with
      | None -> lemmas
      | Some d -> Theory.add_decl lemmas d
  in
  (lemmas, functions)

let global g acc =
  match g with
    | GFun (fdec,_) ->
      begin
(*
        try
          { acc with AST.prog_funct =
              (intern_string fdec.svar.vname, Internal (translate_fundec fdec))
                ::acc.AST.prog_funct }
        with Unsupported msg->
*)
        let msg = "not yet implemented" in
        Self.fatal "Function %s not translated (%s)" fdec.svar.vname msg
      end
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
     Self.fatal "WARNING: Variable %s not translated" vi.vname

    | GVarDecl(_funspec,vi,_location) ->
      Self.error "WARNING: Variable %s not translated" vi.vname;
      acc
    | GAnnot (a, b) ->
      annot a b acc
    | GText _ ->
      Self.fatal "global: GText"
    | GPragma (_, _) ->
      Self.fatal "global: GPragma"
    | GAsm (_, _) ->
      Self.fatal "global: GAsm"
    | GEnumTagDecl (_, _) ->
      Self.fatal "global: GEnumTagDecl"
    | GEnumTag (_, _) ->
      Self.fatal "global: GEnumTag"
    | GCompTagDecl (_, _) ->
      Self.fatal "global: GCompTagDecl"
    | GCompTag (_, _) ->
      Self.fatal "global: GCompTag"
    | GType (_, _)  ->
      Self.fatal "global: GType"

let prog p =
  let lemmas = Theory.create_theory (Ident.id_fresh "Lemmas") in
  let lemmas = Theory.use_export lemmas int_theory in
  let lemmas, _functions =
    List.fold_right global p.globals (lemmas,[])
  in
  let lemmas = Theory.close_theory lemmas in
  lemmas
