(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)


open Format
open Ident
open Pp
open Ity
open Term
open Expr
open Ty
open Theory
open Pmodule
open Mltree
open Printer
open Pdriver

exception InternalError of string
let internal_error s = raise (InternalError s)
let unreachable s = internal_error ("unreachable code in ('" ^ s ^ "')")

exception Unsupported = Printer.Unsupported
let unsupported s = raise (Unsupported s)

let () = Exn_printer.register (fun fmt e -> match e with
  | Unsupported s -> fprintf fmt "unsupported: %s" s
  | _ -> raise e)

let debug_java_extraction =
  Debug.register_info_flag ~desc:"Java extraction" "java_extraction"

let debug fmt =
  Debug.dprintf debug_java_extraction fmt

let warn_void_result =
  Loc.register_warning "w_void_result" "return type is set to void."

let warn_default_method_redef =
  Loc.register_warning "w_default_method_redef" "redefinition of default method."

let search_attribute_prefix (attrs : Sattr.t) (prefix: string)
    : string option =
  let has_prefix (a : Ident.attribute) : string option =
    if Strings.has_prefix prefix a.attr_string then
      Some (Strings.remove_prefix prefix a.attr_string)
    else
      None
  in
  Ident.search_attribute_value has_prefix attrs

let array_attr = create_attribute "extraction:array"
let array_mk_attr = create_attribute "extraction:array_make"
let java_ignore = create_attribute "java:ignore"
let java_constructor = create_attribute "java:constructor"
let java_scalar_objects = create_attribute "java:scalar_objects"

let java_package_prefix = "java:package:"
let java_class_kind_prefix = "java:class_kind:"
let java_visibility_prefix = "java:visibility:"

(* The remain of the attribute specifies the inherited exception
   class. *)
let java_exception_prefix = "java:exception:"

let java_implements_prefix = "java:implements:"

let equals_method_id = Ident.id_register (Ident.id_fresh "equals")

let hashcode_method_id = Ident.id_register (Ident.id_fresh "hash_code")


let camelcase_string (s : string) : string =
  let subs = String.split_on_char '_' s in
  List.fold_left
    (fun acc s -> acc ^ String.capitalize_ascii s)
    (List.hd subs)
    (List.tl subs)

let get_module_package_name (m : Pmodule.pmodule) =
  let m_name = m.mod_theory.th_name in
  search_attribute_prefix m_name.id_attrs java_package_prefix

type visibility = PUBLIC | PRIVATE | PACKAGE
let global_default_visibility = PUBLIC

let get_visibility
      ?(default=global_default_visibility)
      (id: Ident.ident) : visibility =
  match search_attribute_prefix id.id_attrs java_visibility_prefix  with
  | None -> default
  | Some "public" -> PUBLIC
  | Some "private" -> PRIVATE
  | Some "package" -> PACKAGE
  | Some s -> Loc.errorm ?loc:id.id_loc "invalid visibility attribute '%s'" s

let get_exception_attr (id : Ident.ident) : string option =
  search_attribute_prefix id.id_attrs java_exception_prefix

let get_implement_attr (id : Ident.ident) : string list =
  match search_attribute_prefix id.id_attrs java_implements_prefix with
  | None -> []
  | Some s ->
     let interfaces = String.split_on_char ',' s in
     List.map String.trim interfaces


type info = {
  syntax : Printer.syntax_map;
  literal: Printer.syntax_map;
  kn     : Pdecl.known_map;
  prec   : (int list) Mid.t;
}

let mk_info (args : Pdriver.printer_args) m =
  debug "mkinfo %s@." m.mod_theory.th_name.id_string;
  {
    syntax = args.Pdriver.syntax;
    literal = args.Pdriver.literal;
    prec = args.Pdriver.prec;
    kn = m.Pmodule.mod_known
  }

module JavaAST = struct
  type is_static = bool

  type is_final = bool

  let return_id = "'Return"
  let continue_id = "'Continue"
  let break_id = "'Break"

  type type_definition =
    | VoidType
    | TypeFromDrv of string * type_definition list * scalar_objects
    | TypeAlias of ident
    | TypeEnum of ident
    | ThisType
  (*| ArrayType of type_definition *)
  and scalar_objects =
    bool

  let int_type_from_drv = TypeFromDrv ("int", [], false)
  let boolean_type_from_drv = TypeFromDrv ("boolean", [], false)
  let object_type_from_drv = TypeFromDrv ("Object", [], false)


  let is_boolean_type = function
    | TypeAlias id when String.equal id.id_string "bool" -> true
    | TypeFromDrv ("boolean", [], false) -> true
    | _ -> false

  type unop =
    (* e++ e-- *)
    UnOpPostIncr | UnOpPostDecr |
    (* ++e --e  *)
    (* UnOpPreIncr | UnOpPreDecr | *)
    (* +e -e *)
    (* UnOpPlus | UnOpMinus | *)
    (* ~e *)
    (* UnOpBNeg | *)
    (* ! e *)
    UnOpNot

  let unop_is_postfix = function
    | UnOpPostIncr | UnOpPostDecr  -> true
    | _ -> false

  let unop_precedence = function
    | UnOpPostIncr | UnOpPostDecr -> 1
(*
    | UnOpPreIncr | UnOpPreDecr -> 2
    | UnOpPlus | UnOpMinus -> 2
    | UnOpBNeg -> 3
 *)
    | UnOpNot -> 3

  type binop =
    (* multiplicative operators * / % *)
    BinOpMul | (* BinOpDiv | BinOpMod | *)
    (* additive operators + - *)
    BinOpAdd | BinOpSub |
    (* shift operators *)
    (*BinOpLShift | BinOpRShift | BinOpURShift | *)
    (* relational operators < > <= >= instanceof *)
    (* BinOpLT | BinOpGT | *) BinOpLEQ | BinOpGEQ | (* BinOpInstanceOf | *)
    (* equality = and disequality != *)
    BinOpEQ | (* BinOpNEQ | *)
    (* logical operators && || *)
    BinOpAnd | BinOpOr |
    (* assignments *)
    BinOpAssign      (* = *)
    (* bitwise operators & ^ | *)
    (* | BinOpBAnd | BinOpBXor | BinOpBOr | *)
    (* += -= *)
    (* BinOpAddAssign | BinOpSubAssign | *)
    (* *= /= %= *)
    (* BinOpMulAssign | BinOpDivAssign | BinOpModAssign |*)
    (* &= ^= |= *)
    (* BinOpBAndAssign | BinOpBXOrAssign | BinOpBOrAssign | *)
    (* <<= >>= >>>= *)
    (* BinOpLShiftAssign | BinOpRShiftAssign | BinOpURShiftAssign   *)

  let binop_precedence = function
    | BinOpMul (* | BinOpDiv | BinOpMod *) -> 4
    | BinOpAdd | BinOpSub -> 5
(*    | BinOpLShift | BinOpRShift | BinOpURShift -> 6 *)
(*    | BinOpLT | BinOpGT *)
    | BinOpLEQ | BinOpGEQ -> 7
(*    | BinOpInstanceOf -> 7 *)
    | BinOpEQ (*| BinOpNEQ*) -> 8
(*
    | BinOpBAnd -> 9
    | BinOpBXor -> 10
    | BinOpBOr -> 11
 *)
    | BinOpAnd -> 12
    | BinOpOr -> 13
    | BinOpAssign -> 15
(*
    | BinOpAddAssign | BinOpSubAssign -> 15
    | BinOpMulAssign | BinOpDivAssign | BinOpModAssign -> 15
    | BinOpBAndAssign | BinOpBXOrAssign | BinOpBOrAssign -> 15
    | BinOpLShiftAssign | BinOpRShiftAssign | BinOpURShiftAssign -> 15
 *)

  let ite_precedence = 14

  let is_assignment = function
    | BinOpAssign -> true
    (*
    | BinOpAddAssign | BinOpSubAssign | BinOpMulAssign -> true
    | BinOpDivAssign | BinOpModAssign | BinOpBAndAssign -> true

    | BinOpBXOrAssign | BinOpBOrAssign | BinOpLShiftAssign -> true
    | BinOpRShiftAssign | BinOpURShiftAssign -> true
   *)
    | _ -> false

  let right_assoc = is_assignment
  let left_assoc op = not (is_assignment op)

  type instance_variable = visibility * is_final * ident * type_definition

  type definition =
    | DeclEnum of visibility * ident * ident list
    | DeclInstanceVar of instance_variable
    | DeclConstructor of visibility * (ident * type_definition) list * xsymbol list * body
    | DeclMethod of is_final * visibility * is_static * ident * type_definition * (ident * type_definition) list * xsymbol list * body
    | DeclAbstractMethod of visibility * ident * type_definition * (ident * type_definition) list * xsymbol list
    | DeclLocalVar of type_definition * (ident * expression) list
    | DeclNotImplemented of string
  and statement =
    | StmtIf of expression * statement * statement
    | StmtWhile of expression * statement
    | StmtFor of ident * type_definition *
                   expression * expression * expression * statement
    | StmtReturn of expression (* return e; *)
    | StmtSequence of statement * statement (* [s1; s2] *)
    | StmtBlock of body (* { decl;* s } *)
    | StmtThisConstructor of statement
    | StmtExpr of expression (* e; *)
    | StmtBreak (* break; *)
    | StmtContinue (* continue; *)
    | StmtNop (* ; *)
    | StmtTODO of string (* ; *)
    | StmtThrow of Ity.xsymbol * expression
    | StmtTry of statement * catch list
  and catch =
    Ity.xsymbol * Ity.pvsymbol option * statement
  and expression =
    | ExprNop
    | ExprAbsurd
    (* | ExprTODO of string *)
    | ExprConst of constant
    | ExprUnOp of unop * expression
    | ExprBinOp of binop * expression * expression
    | ExprVar of Ident.ident * type_definition
    | ExprThis
    | ExprCast of type_definition * expression
    | ExprArraysEquals of expression * expression
    | ExprArraysHashCode of expression
    | ExprFromDrv of string * expression list * int list
    | ExprITE of expression * expression * expression
    | ExprFunCall of expression * expression list

    (* obj.m (args) or NOP.m (args) *)
    | ExprMethodCall of expression * Ident.ident * expression list

    | ExprNewArray of type_definition * expression
    | ExprArrayIndexing of expression * expression (* a[i] *)
    | ExprDot of expression * Ident.ident (* obj.field *)
    | ExprNewInstance of Ident.ident * expression list
    | ExprThisConstructorCall of expression list
    | ExprClassOf of expression (* e.class *)
  and constant =
    | CstNull
    | CstInt of string
    | CstStr of string
    | CstBool of bool
    | CstEnum of Ident.ident * type_definition (* enum value, type *)
  and body =
    definition list * statement

  let is_void = function
    | VoidType -> true
    | _ -> false

  let rec is_boolean_expr = function
    | ExprConst (CstBool _) -> true
    | ExprVar (_, vartype) -> is_boolean_type vartype
    | ExprUnOp (UnOpNot, _) -> true
    | ExprBinOp (BinOpOr,_, _) -> true
    | ExprBinOp (BinOpAnd,_, _) -> true
    | ExprBinOp (BinOpEQ,_, _) -> true
(*    | ExprBinOp (BinOpNEQ,_, _) -> true *)
    | ExprBinOp (BinOpLEQ,_, _) -> true
(*    | ExprBinOp (BinOpLT,_, _) -> true *)
    | ExprBinOp (BinOpGEQ,_, _) -> true
(*    | ExprBinOp (BinOpGT,_, _) -> true *)
    | ExprBinOp (BinOpAssign, v, _) -> is_boolean_expr v
    | ExprITE (_,t,e) -> is_boolean_expr t && is_boolean_expr e
    | _ -> false

  let is_ite (s : statement) =
    match s with
    | StmtIf _ -> true
    | _ -> false

  let rec is_nop (s : statement) =
    match s with
    | StmtNop -> true
    | StmtExpr ExprNop -> true
    | StmtBlock ([], s) -> is_nop s
    | StmtSequence (s1, s2) -> (is_nop s1) && (is_nop s2)
    | _ -> false


  let mk_int (i : int) = ExprConst (CstInt (string_of_int i))

  let zero_expr = mk_int 0
  let one_expr = mk_int 1

  let null_expr = ExprConst CstNull

  let mk_assign v b = ExprBinOp (BinOpAssign, v, b)

  let mk_add a b = ExprBinOp (BinOpAdd, a, b)

  let mk_mul a b = ExprBinOp (BinOpMul, a, b)

  let true_expr = ExprConst (CstBool true)
  let is_true_expr = function
    | ExprConst (CstBool true) -> true
    | _ -> false

  let is_true_stmt = function
    | StmtExpr e -> is_true_expr e
    | _ -> false

  let false_expr = ExprConst (CstBool false)
  let is_false_expr = function
    | ExprConst (CstBool false) -> true
    | _ -> false
  let is_false_stmt = function
    | StmtExpr e -> is_false_expr e
    | _ -> false

  let mk_and a b =
    match a, b with
    | ExprConst (CstBool true),_ -> b
    | _, ExprConst (CstBool true) -> a
    | ExprConst (CstBool false),_ -> false_expr
    | _, ExprConst (CstBool false) -> false_expr
    | _, _ -> ExprBinOp (BinOpAnd, a, b)

  let mk_or a b =
    match a, b with
    | ExprConst (CstBool true),_ -> true_expr
    | _, ExprConst (CstBool true) -> true_expr
    | ExprConst (CstBool false),_ -> b
    | _, ExprConst (CstBool false) -> a
    | _, _ -> ExprBinOp (BinOpOr, a, b)

  let mk_not a =
    match a with
    | ExprConst (CstBool true) -> false_expr
    | ExprConst (CstBool false) -> true_expr
    | _ -> ExprUnOp (UnOpNot, a)

  let mk_eq a b = ExprBinOp (BinOpEQ, a, b)

  let mk_neq a b = mk_not (mk_eq a b)

  let mk_ite i t e =
    match i, t, e with
    | ExprConst (CstBool true), _, _ -> t
    | ExprConst (CstBool false), _, _ -> e
    | _, ExprConst (CstBool true), _ -> mk_or i e
    | _, ExprConst (CstBool false), _ -> mk_and (mk_not i) e
    | _, _, ExprConst (CstBool true) -> mk_or (mk_not i) t
    | _, _, ExprConst (CstBool false) -> mk_and i t
    | _ -> ExprITE (i, t, e)

  let mk_if c t e =
    match t, e with
    (* | StmtExpr t', StmtExpr e' *)
    (*      when is_boolean_expr t' && is_boolean_expr e' -> *)
    (*    StmtExpr (mk_ite c t' e') *)
    | StmtReturn t', StmtReturn e'
          when is_boolean_expr t' && is_boolean_expr e' ->
        StmtReturn (mk_ite c t' e')
    | _, _ ->
        match c with
        | ExprConst (CstBool true) -> t
        | ExprConst (CstBool false) -> e
        | _ -> StmtIf (c, t, e)

  let rec mk_seq s1 s2 =
    if is_nop s1 then s2
    else if is_nop s2 then s1
    else match s1, s2 with
      | StmtBlock (d1, s1), StmtBlock ([], s2) ->
        StmtBlock (d1, mk_seq s1 s2)
      | StmtBlock (d1, s1), StmtBlock (d2, s2) when is_nop s1 ->
        StmtBlock (d1@d2, s2)
      | StmtBlock (d1, s1), _ when is_nop s1 -> StmtBlock (d1, s2)
      | _ -> StmtSequence (s1, s2)

  let rec mk_seq_of_list stmtlist =
    match stmtlist with
    | [] -> StmtNop
    | [s] when is_nop s -> StmtNop
    | [s] -> s
    | s :: tl -> mk_seq s (mk_seq_of_list tl)

  let rec assign v stmt : statement =
    match stmt with
    | StmtIf (c,t,e) -> StmtIf (c, assign v t, assign v e)
    | StmtSequence (s1, s2) -> mk_seq s1  (assign v s2)
    | StmtBlock (dl, s) -> StmtBlock (dl, assign v s)
    | StmtExpr e -> StmtExpr (ExprBinOp (BinOpAssign, v, e))
    | StmtWhile (cond, loopstmt) ->
        StmtWhile (cond, assign v loopstmt)
    | StmtFor (i, it, init, cond, step, loopstmt) ->
        StmtFor (i, it, init, cond, step, assign v loopstmt)
    | StmtThisConstructor _ ->
        internal_error "try to assign ThisConstructor statement"
    | StmtTry _ ->
        internal_error "try to assign try-catch statement"
    | StmtNop -> internal_error "try to assign NOP statement"
    | StmtBreak -> internal_error "try to assign 'break' statement"
    | StmtContinue -> internal_error "try to assign 'continue' statement"
    | StmtReturn _ -> internal_error "try to assign 'return' statement"
    | StmtThrow _ -> internal_error "try to assign 'throw' statement"
    | StmtTODO s -> StmtTODO s

  let rec get_last_expr (stmt : statement) : statement * expression =
    match stmt with
    | StmtIf (c, t, e) ->
        let st, t = get_last_expr t in
        let se, e = get_last_expr e in
        mk_seq st se, mk_ite c t e
    | StmtSequence (s, StmtNop) ->
        get_last_expr s
    | StmtSequence (s1, s2) ->
        let s2', e = get_last_expr s2 in
        (mk_seq s1 s2'), e
    | StmtBlock (dl, s) ->
        let s', e = get_last_expr s in
        StmtBlock (dl, s'), e
    | StmtExpr e ->
        StmtNop, e
    | StmtWhile (_, _) ->
        unsupported "while in condition expression"
    | StmtFor (_, _, _, _, _, _) ->
        unsupported "for in condition expression"
    | StmtThisConstructor _ ->
        internal_error "ThisConstructor in get_last_expr"
    | StmtNop ->
        internal_error "NOP in get_last_expr"
    | StmtBreak ->
        internal_error "break in get_last_expr"
    | StmtContinue ->
        internal_error "continue in get_last_expr"
    | StmtReturn _ ->
        internal_error "return in get_last_expr"
    | StmtThrow _ ->
        internal_error "throw in get_last_expr"
    | StmtTODO _ ->
        internal_error "TODO in get_last_expr"
    | StmtTry _ ->
        internal_error "try-catch in get_last_expr"


  (**
      Retrieve the expression from a simple body (i.e. without definitions)
    *)


  exception ExprOfBodyFailure
  let rec expr_of_body (d,s) : expression =
    match (d,s) with
    | [], StmtBlock([],s) -> expr_of_body ([],s)
    | [], StmtExpr e -> e
    | [], StmtIf (c,t,e) ->
        ExprITE (c, expr_of_body ([], t), expr_of_body ([],e))
    | _ -> raise ExprOfBodyFailure

  let rec elim_empty_blocks = function
    | StmtBlock ([], s) ->
        elim_empty_blocks s
    | StmtBlock (d,s) ->
        StmtBlock (d, elim_empty_blocks s)

    | StmtThisConstructor s ->
        StmtThisConstructor (elim_empty_blocks s)

    | StmtSequence(s1,s2) ->
          mk_seq (elim_empty_blocks s1)  (elim_empty_blocks s2)
    | StmtIf (c, t, e) ->
        mk_if c (elim_empty_blocks t) (elim_empty_blocks e)
    | StmtWhile (c, s) ->
        StmtWhile (c, elim_empty_blocks s)
    | StmtFor (i, it, e1, e2, e3, s) ->
          StmtFor (i, it, e1, e2, e3, elim_empty_blocks s)
    | StmtTry (s, cl) ->
        StmtTry (elim_empty_blocks s,
                List.map (fun (xs, pvs, st) ->
                    (xs, pvs, elim_empty_blocks st)) cl)
    | StmtThrow _ | StmtTODO _ | StmtNop | StmtBreak | StmtExpr _
      | StmtContinue | StmtReturn _ as s -> s

  let rec elim_nop = function
    | StmtIf (c, t, e) ->
        mk_if c (elim_nop t) (elim_nop e)
    | StmtSequence (s1, s2) ->
        mk_seq (elim_nop s1) (elim_nop s2)
    | StmtBlock ([], s) ->
        elim_nop s
    | StmtBlock (dl, s) ->
        StmtBlock (dl, elim_nop s)

    | StmtThisConstructor s ->
        StmtThisConstructor (elim_nop s)

    | StmtWhile (cond, loopstmt) ->
        StmtWhile (cond, elim_nop loopstmt)
    | StmtFor (i, it, init, cond, step, loopstmt) ->
        StmtFor (i, it, init, cond, step, elim_nop  loopstmt)
    | StmtTry (s, cl) ->
        StmtTry (elim_nop s,
                List.map (fun (xs, pvs, st) -> (xs, pvs, elim_nop st)) cl)
    | StmtThrow _ | StmtNop | StmtBreak | StmtContinue | StmtReturn _
      | StmtTODO _ | StmtExpr _ as s -> s

  let rec simplify_last_statement = function
    | StmtReturn ExprNop -> StmtNop
    | StmtBlock (d, s) -> StmtBlock (d, simplify_last_statement s)
    | StmtSequence (s1, StmtReturn ExprNop) -> simplify_last_statement s1
    | StmtSequence (s1, s2) -> mk_seq s1 (simplify_last_statement s2)
    | _ as s -> s


  let simplify_statement stmt =
    let pass1 = elim_nop stmt in
    let pass2 = elim_empty_blocks pass1 in
    let res = match pass2 with
    | StmtIf (c, t, e) ->
        mk_if c (simplify_last_statement t) (simplify_last_statement e)
    | StmtSequence _ as s -> simplify_last_statement s
    | StmtBlock ([], s) -> simplify_last_statement s
    | StmtBlock (dl, s) -> StmtBlock (dl, simplify_last_statement s)
    | StmtThisConstructor s ->
        StmtThisConstructor (elim_nop s)
    | StmtWhile (cond, loopstmt) ->
        StmtWhile (cond, elim_nop loopstmt)
    | StmtFor (i, it, init, cond, step, loopstmt) ->
        StmtFor (i, it, init, cond, step, elim_nop  loopstmt)
    | StmtTry (s, cl) ->
        StmtTry (elim_nop s,
                List.map (fun (xs, pvs, st) ->
                    (xs, pvs, simplify_last_statement st)) cl)
    | StmtReturn (ExprNop) -> StmtNop
    | StmtThrow _ | StmtNop | StmtBreak | StmtContinue | StmtReturn _
    | StmtTODO _ | StmtExpr _ as s -> s
  in
    res


  let rec mk_body ?(simplify=false) (d : definition list) (s : statement) : body =
    let res = match d, s with
    | [], StmtBlock (d, s) -> mk_body ~simplify:simplify d s
    | d, StmtBlock (d', s) -> mk_body ~simplify:simplify (d @ d') s
    | d, StmtSequence (StmtBlock (d', s), s2) ->
        mk_body ~simplify:simplify (d @ d') (mk_seq s s2)
    | _ -> (d, if simplify then simplify_statement s else s)
    in
      res

  (* Boolean expr may be encoded with ITE. Restore Boolean
      connectives *)
  let rec simplify_cond (cd, cs) =
    match cd, elim_empty_blocks (elim_nop cs) with
    | [], StmtExpr c -> ([], StmtExpr c)
    | [], StmtIf (c', t', e') as ite ->
        if is_true_expr c' then
          [], simplify_statement t'
        else if is_false_expr c' then
          [], simplify_statement e'
        else
        let _, t' = simplify_cond ([], t') in
        let _, e' = simplify_cond ([], e') in
        begin
          try
            if is_false_stmt e' then (* c' && t' *)
              [], StmtExpr (mk_and c' (expr_of_body ([], t')))
            else if is_true_stmt e' then (* !c' || t' *)
              [], StmtExpr (mk_or (mk_not c') (expr_of_body ([], t')))
            else if is_true_stmt t' then (* c' || e' *)
              [], StmtExpr (mk_or c' (expr_of_body ([], e')))
            else if is_false_stmt t' then (* !c' && e' *)
              [], StmtExpr (mk_and (mk_not c') (expr_of_body ([], e')))
            else ite
          with
          | ExprOfBodyFailure -> ite
        end
    | d, s -> d, s

  let mk_for (i : Ident.ident) (i_type : type_definition)
        (min : expression) (dir: Mltree.for_direction) (max : expression)
        (block : expression -> statement) : body =
    let i_var = ExprVar (i,i_type) in
    let initexpr = min in
    let cmpop, stepop = match dir with
      | To -> BinOpLEQ, UnOpPostIncr
      | DownTo -> BinOpGEQ, UnOpPostDecr in
    let condexpr = ExprBinOp (cmpop, i_var, max) in
    let stepexpr = ExprUnOp (stepop, i_var) in
    let fillstmt = StmtFor (i, i_type,
                            initexpr, condexpr, stepexpr, block i_var) in
    mk_body [] fillstmt
end

module JavaCompilerInfo = struct
  open JavaAST
  open Pmodule
  open Ident
  open Pdecl

  exception UnknownClass of string
  exception NoSuchEnumType of string
  exception EnumTypeAlreadyDefined of string
  exception ExceptionAlreadyDefined of string
  exception UnknownException of string

  type class_record = {
    m : Pmodule.pmodule;
    kind : class_kind;
    package_name : string option;
    class_name : Ident.ident;
    exception_parent : string option;
    implements : string list;
    mutable exn : Ity.xsymbol option;
    mutable this_type_id : Ident.ident option;
    mutable instance_vars : instance_variable list;
    mutable methods : class_method Mid.t;
    }
  and class_method = {
      this_index : int option;
      owner : class_record;
    }
  and class_kind = REGULAR | INTERFACE | ABSTRACT

  type enum_type = {
      owner : class_record;
      values : Sid.t;
    }

  type compiler_info = {
      mutable current_class : class_record option;
      mutable known_classes : class_record Mid.t;
      mutable known_methods : class_method Mid.t;
      mutable enum_types : enum_type Mid.t;
      mutable default_visibility : visibility;
      mutable imported_modules : Sid.t;
      mutable exceptions : class_record Mxs.t;
    }

  let compinfo : compiler_info = {
      current_class = None;
      known_classes = Mid.empty;
      known_methods = Mid.empty;
      enum_types = Mid.empty;
      default_visibility = global_default_visibility;
      imported_modules = Sid.empty;
      exceptions = Mxs.empty;
    }

  let this_id = "self"

  let get_class_kind (clsname : Ident.ident) : class_kind =
      match search_attribute_prefix clsname.id_attrs java_class_kind_prefix with
      | Some "abstract" -> ABSTRACT
      | Some "interface" -> INTERFACE
      | None | Some "class" -> REGULAR
      | Some s -> Loc.errorm ?loc:clsname.id_loc
                    "invalid class_kind attribute '%s'" s

  let init_compiler_info (m : Pmodule.pmodule) : unit =
    let clsname = m.mod_theory.th_name in
    compinfo.current_class <-
      Some {
          m = m;
          kind = get_class_kind clsname;
          package_name = get_module_package_name m;
          class_name = clsname;
          exception_parent = get_exception_attr clsname;
          implements = get_implement_attr clsname;
          exn = None;
          this_type_id = None;
          instance_vars = [];
          methods = Mid.empty;
        };
    compinfo.default_visibility <-
      get_visibility
        ~default:global_default_visibility
        m.mod_theory.th_name;
    compinfo.imported_modules <- Sid.empty

  let get_class (id : Ident.ident) : class_record =
    match Mid.find_opt id compinfo.known_classes with
    | Some c -> c
    | None -> raise (UnknownClass id.id_string)

  let get_current_class () : class_record =
    match compinfo.current_class with
    | Some c -> c
    | None -> internal_error "current_class is not defined."

  let is_interface () =
    match (get_current_class ()).kind with
    | INTERFACE -> true
    | _ -> false

  (* let is_abstract () =
     match (get_current_class ()).kind with
     | ABSTRACT -> true
     | _ -> false *)

  (* let is_exception () =
     Option.is_some (get_current_class ()).exception_parent *)

  let is_current_class (cls : class_record) : bool =
    Ident.id_equal cls.class_name (get_current_class ()).class_name

  let import_module (m : Pmodule.pmodule) =
    let m_name = m.mod_theory.th_name in
    debug "import module #%d: %s@\n"
      (Sid.cardinal compinfo.imported_modules)
      m_name.id_string;
    compinfo.imported_modules <- Sid.add m_name  compinfo.imported_modules

  let is_imported_module (m : Pmodule.pmodule) : bool =
    Sid.exists (fun id -> Ident.id_equal id m.mod_theory.th_name)
      compinfo.imported_modules

  let set_this_type (id : Ident.ident) (ivs : instance_variable list) =
    let cls = get_current_class () in
    if Option.is_some cls.this_type_id then
      Loc.errorm ?loc:id.id_loc "only one type can be declared in classes.";
    assert (not (Option.is_some (Mid.find_opt id compinfo.known_classes)));
    cls.this_type_id <- Some id;
    cls.instance_vars <- ivs;
    debug "register class id %s@%d -> %s@." id.id_string (Weakhtbl.tag_hash id.id_tag) cls.class_name.id_string;
    compinfo.known_classes <- Mid.add id cls compinfo.known_classes

  let get_this_type_opt () : Ident.ident option =
    (get_current_class ()).this_type_id

  let get_this_type () : Ident.ident =
    Option.get (get_this_type_opt ())

  let is_static_class () : bool =
    not (Option.is_some (get_this_type_opt ()))

  let get_current_class_name () : Ident.ident =
    (get_current_class ()).class_name

  let is_this_type (typeid : Ident.ident) : bool =
    try
      id_equal typeid (get_this_type ())
    with
      _ -> false

  let is_this_variable (id : Ident.ident) (typeid : Ident.ident) : bool =
    (id.id_string = this_id) && (is_this_type typeid)

  let is_constructor (info : info) (id : Ident.ident) : bool =
    let aux (its : Pdecl.its_defn) : bool =
      List.exists (fun rs -> id_equal rs.rs_name id) its.itd_constructors
    in
    match Mid.find_opt id info.kn with
      | Some { pd_node = PDtype its } ->
         List.exists aux its
      | _ -> false


  let is_dummy id = Sattr.mem Dexpr.dummy_var_attr id.id_attrs

  let get_enum_values_opt (id : Ident.ident) : Sid.t option =
    match Mid.find_opt id compinfo.enum_types with
    | None -> None
    | Some { values = sid } -> Some sid

  let is_enum_type (id : Ident.ident) : bool =
    Option.is_some (get_enum_values_opt id)

  let get_enum_values (id : Ident.ident) : Sid.t =
    match get_enum_values_opt id with
    | None -> raise (NoSuchEnumType id.id_string)
    | Some sid  -> sid

  let get_enum_owner (id : Ident.ident) : class_record =
    match Mid.find_opt id compinfo.enum_types with
    | None -> raise (NoSuchEnumType id.id_string)
    | Some { owner = cls } -> cls

  let set_enum_values (id : Ident.ident) (values : Sid.t) =
    if Mid.mem id compinfo.enum_types then
      raise (EnumTypeAlreadyDefined id.id_string)
    else let enum = { owner = get_current_class (); values = values } in
      compinfo.enum_types <- Mid.add id enum compinfo.enum_types

  exception MethodRedefinition of string

  let check_new_method_against_default (mid : Ident.ident) =
    if not (mid = equals_method_id || mid = hashcode_method_id) then
    begin
      let ccident = camelcase_string mid.id_string in
      if String.equal ccident (camelcase_string equals_method_id.id_string) then
        Loc.warning warn_default_method_redef ?loc:mid.id_loc "redefinition of default method '%s'." mid.id_string
      else if String.equal ccident (camelcase_string hashcode_method_id.id_string) then
        Loc.errorm ?loc:mid.id_loc "redefinition of default method '%s' is not allowed." mid.id_string
    end

  let add_method (this_index : int option) (ident : Ident.ident) =
    let cls = get_current_class () in
    check_new_method_against_default ident;
    match Mid.find_opt ident cls.methods with
    | Some _ -> raise (MethodRedefinition ident.id_string)
    | None ->
       let m = { this_index = this_index; owner = cls } in
       cls.methods <- Mid.add ident m cls.methods;
       compinfo.known_methods <- Mid.add ident m compinfo.known_methods

  exception NoSuchMethod of string

  let get_method_opt (mid : Ident.ident) : class_method option =
    Mid.find_opt mid compinfo.known_methods

  let get_method (mid : Ident.ident) : class_method =
    match get_method_opt mid with
    | Some m -> m
    | None -> raise (NoSuchMethod mid.id_string)

  let get_default_visibility () =
    compinfo.default_visibility

  let set_exception (exn : Ity.xsymbol) =
    let ccls = get_current_class () in

    match ccls.exn with
    | Some xs ->
       raise (ExceptionAlreadyDefined xs.xs_name.id_string)
    | None ->
       begin
         ccls.exn <- Some exn;
         compinfo.exceptions <- Mxs.add exn (get_current_class ())
                                  compinfo.exceptions
       end

  let get_exception_class_opt (exn : Ity.xsymbol) : class_record option =
    Mxs.find_opt exn compinfo.exceptions

  let get_exception_class (exn : Ity.xsymbol) : class_record =
    match get_exception_class_opt exn with
    | None -> raise (UnknownException exn.xs_name.id_string)
    | Some cls -> cls

  let is_known_java_exception (info : info) (exn : Ity.xsymbol) : bool =
    match query_syntax info.syntax exn.xs_name, get_exception_class_opt exn
    with
    | Some s, None ->
       debug "exception from syntax driver %s -> %s@\n"
         exn.xs_name.id_string s;
       true
    | None, Some cls ->
       debug "exception %s -> %s@\n"
         exn.xs_name.id_string cls.class_name.id_string; false
    | Some s, Some _ ->
       Loc.errorm ?loc:exn.xs_name.id_loc
         "conflict between exceptions %s (%s) vs Java." exn.xs_name.id_string s
    | None, None ->
       Loc.errorm ?loc:exn.xs_name.id_loc
         "unknown exception %s." exn.xs_name.id_string

end


module JavaPrint = struct
  open JavaAST
  open JavaCompilerInfo

  let java_keywords = [
    "abstract"; "continue"; "for"; "new"; "switch";
    "assert"; "default"; "goto"; "package";  "synchronized";
    "boolean"; "do"; "if"; "private"; "this";
    "break"; "double"; "implements"; "protected"; "throw";
    "byte"; "else"; "import"; "public"; "throws";
    "case"; "enum"; "instanceof"; "return"; "transient";
    "catch"; "extends"; "int"; "short"; "try";
    "char"; "final"; "interface"; "static"; "void";
    "class"; "finally"; "long"; "strictfp"; "volatile";
    "const"; "float"; "native"; "super";  "while";
  ]

  let anonymous_exception_id = Ident.id_register (Ident.id_fresh "e_x")

  let default_sanitizer = sanitizer char_to_alpha char_to_alnumus

  let enum_sanitizer s =
    String.uppercase_ascii (String.trim (default_sanitizer s))

  let camelcase_sanitizer s =
    camelcase_string (String.trim (default_sanitizer s))

  let classname_sanitizer s =
    String.capitalize_ascii (camelcase_sanitizer s)

  let instance_names_sanitizer = camelcase_sanitizer

  let print_ident_ ~sanitizer pr _ fmt id =
    let s = id_unique ~sanitizer pr id in
    pp_print_string fmt s;
    Ident.forget_id pr id

  let print_unique_ident_ ~sanitizer pr _ fmt id =
    let s = id_unique ~sanitizer pr id in
    pp_print_string fmt s

  (* namespace used to display identifiers in methods: parameters
     and local variables *)
  let local_names = create_ident_printer java_keywords
  let global_names = create_ident_printer java_keywords

  let default_ident_printer = print_unique_ident_
                                ~sanitizer:camelcase_sanitizer local_names

  let enum_ident_printer =  print_ident_ ~sanitizer:enum_sanitizer
                              global_names

  let classname_printer =  print_ident_ ~sanitizer:classname_sanitizer
                             global_names

  let instance_names_printer =  print_ident_ ~sanitizer:instance_names_sanitizer
                                  global_names

  let method_names_printer = instance_names_printer
  let instance_vars_names_printer = instance_names_printer

  let protect_on ?(boxed=false) cond s =
    if cond then "@[<1>(" ^^ s ^^ ")@]"
    else if not boxed then "@[" ^^ s ^^ "@]"
    else s

  let print_visibility fmt = function
    | PUBLIC -> fprintf fmt "public "
    | PRIVATE -> fprintf fmt "private "
    | PACKAGE -> ()

  let print_unop fmt op =
    let str_of_op = function
      | UnOpPostIncr (* | UnOpPreInc *) -> "++"
      | UnOpPostDecr (* | UnOpPreDecr *) -> "--"
(*
      | UnOpPlus -> "+"
      | UnOpMinus -> "-"
      | UnOpBNeg -> "~"
*)
      | UnOpNot -> "!"
    in pp_print_string fmt (str_of_op op)

  let print_binop fmt op =
    let str_of_op = function
      | BinOpMul -> "*"
(*      | BinOpDiv -> "/" *)
(*      | BinOpMod -> "%" *)
      | BinOpAdd -> "+"
      | BinOpSub -> "-"
(*      | BinOpLT -> "<" *)
(*      | BinOpGT -> ">" *)
      | BinOpLEQ -> "<="
      | BinOpGEQ -> ">="
      | BinOpEQ -> "=="
(*      | BinOpNEQ -> "!=" *)
      | BinOpAnd -> "&&"
      | BinOpOr -> "||"
      | BinOpAssign -> "="
(*
      | BinOpLShift -> "<<"
      | BinOpRShift -> ">>"
      | BinOpURShift -> ">>>"
      | BinOpInstanceOf -> "instanceof"
      | BinOpBAnd -> "&"
      | BinOpBXor -> "^"
      | BinOpBOr -> "|"
      | BinOpAddAssign -> "+="
      | BinOpSubAssign -> "-="
      | BinOpMulAssign -> "*="
      | BinOpDivAssign -> "+="
      | BinOpModAssign -> "%="
      | BinOpBAndAssign -> "&="
      | BinOpBXOrAssign -> "^="
      | BinOpBOrAssign -> "|="
      | BinOpLShiftAssign -> "<<="
      | BinOpRShiftAssign -> ">>="
      | BinOpURShiftAssign -> ">>>="
 *)
    in pp_print_string fmt (str_of_op op)

  let print_enum_decl (info : info) fmt (vis : visibility) (typeid : ident)
        (ident_list : ident list) =
    let pp_comma fmt () = Format.fprintf fmt ",@\n" in
    fprintf fmt "@[%aenum %a@\n{@[<2>@\n%a@]@\n}@]"
      print_visibility vis
      (classname_printer info) typeid
      (pp_print_list ~pp_sep:pp_comma (enum_ident_printer info)) ident_list

  let print_class_name (info : info) fmt (cls : class_record) =
    if is_imported_module cls.m || not (Option.is_some cls.package_name) ||
         is_current_class cls then
      default_ident_printer info fmt cls.class_name
    else
      fprintf fmt "%s.%a" (Option.get cls.package_name)
        (default_ident_printer info) cls.class_name

  let print_type_class_name (info : info) fmt (typeid: Ident.ident) =
    print_class_name info fmt (get_class typeid)

  let rec print_type (info : info) fmt (t : type_definition) =
    let scalar_to_object (s : string) : string =
      match s with
      | "int" -> "Integer"
      | "boolean" | "short" | "long" | "float" | "double" ->
         String.capitalize_ascii s
      | _ -> s
    in

    let print_from_syntax s typedef_list scalar_objects =
      let pr fmt t =
        match t with
        | TypeFromDrv (s, [], false) when scalar_objects ->
           fprintf fmt "%s" (scalar_to_object s)
        | TypeFromDrv (_, [], true) ->
           internal_error "non parameterized type with scalar_object"
        | _ -> print_type info fmt t
      in
      syntax_arguments s pr fmt typedef_list
    in
    match t with
    | VoidType -> fprintf fmt "void"
    | TypeFromDrv (s, typedef_list, scalar_objects) ->
       print_from_syntax s typedef_list scalar_objects
    | TypeEnum id ->
       let cls = get_enum_owner id in
       if not (is_current_class cls) then
         fprintf fmt "%a." (print_class_name info) cls;
       fprintf fmt "%a" (classname_printer info) id
    | TypeAlias id ->
       begin
         try
           print_type_class_name info fmt id
         with
           UnknownClass _ -> default_ident_printer info fmt id
       end
    | ThisType -> fprintf fmt "%a"
                    (default_ident_printer info) (get_current_class_name ())
  (* | ArrayType t -> fprintf fmt "%a[]" (print_type info) t *)

  let print_instance_var (info : info) fmt (vis : visibility) (id : ident)
        (typedef : type_definition) ~(isfinal : bool) =
    fprintf fmt "@[%a%a%a %a;@]"
      print_visibility vis
      (fun fmt () -> if isfinal then fprintf fmt "final ") ()
      (print_type info) typedef
      (instance_vars_names_printer info) id

  let print_function_args (info : info) fmt
        (args : (ident * type_definition) list) =
    let print_arg info fmt (id, ty) =
      if not (is_void ty) then
        fprintf fmt "@[%a %a@]" (print_type info) ty
          (default_ident_printer info) id in
    pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ",@ ")
      (print_arg info) fmt args

  let print_static_spec fmt is_static =
    if is_static then
      fprintf fmt "static "

  let print_abstract_spec fmt _ =
    if not (is_interface ()) then
      fprintf fmt "abstract "

  let print_class_kind fmt cls =
    match cls.kind with
    | INTERFACE -> fprintf fmt "interface "
    | ABSTRACT -> fprintf fmt "abstract class "
    | REGULAR -> fprintf fmt "class "

  let print_exception_parent fmt cls =
    match cls.exception_parent with
    | None -> ()
    | Some classname -> fprintf fmt " extends %s" classname

  let print_implements fmt cls =
    let rec prl fmt l =
      match l with
      | [] -> ()
      | [s] -> fprintf fmt "%s" s
      | s::tl -> fprintf fmt "%s, " s; prl fmt tl
    in
    if List.length cls.implements > 0 then
      fprintf fmt " implements %a" prl cls.implements

  let rec print_expression ~(prec:int) (info : info) fmt (e : expression) =
    let print_unop_expr (op : unop) (e : expression) =
      let p = unop_precedence op in
      if unop_is_postfix op
      then fprintf fmt (protect_on (prec < p) "%a%a")
             (print_expression ~prec:(p-1) info) e print_unop op
      else fprintf fmt (protect_on (prec < p) "%a%a")
             print_unop op (print_expression ~prec:(p-1) info) e
    and print_binop_expr (op : binop) (e1 : expression) (e2 : expression) =
      let p = binop_precedence op in
      let pleft = if left_assoc op then p else p-1 in
      let pright = if right_assoc op then p else p-1 in
      fprintf fmt (protect_on (prec < p) "%a %a %a")
        (print_expression ~prec:pleft info) e1
        print_binop op
        (print_expression ~prec:pright info) e2
    and print_ite (i : expression) (t : expression) (e : expression) =
      let p = ite_precedence in
      fprintf fmt (protect_on (prec < p) "%a ? %a : %a")
         (print_expression ~prec:(p-1) info) i
         (print_expression ~prec:(p+1) info) t
         (print_expression ~prec:p info) e
    and print_call (f : expression) (params : expression list) =
      fprintf fmt (protect_on (prec < 1) "%a (%a)")
        (print_expression ~prec:1 info) f
        (print_list comma (print_expression ~prec:15 info)) params
    and print_method_call (e : expression) (mid : Ident.ident)
                           (params : expression list) =
      let print_method_ctx fmt e =
        let m = get_method mid in
        match e with
        | ExprNop -> assert (not (Option.is_some m.this_index));
                     (* classname_printer info fmt m.owner.class_name*)
                       print_class_name info fmt m.owner
        | _ -> print_expression ~prec:1 info fmt e
      in
      fprintf fmt (protect_on (prec < 1) "%a.%a(%a)")
        print_method_ctx e
        (method_names_printer info) mid
        (print_list comma (print_expression ~prec:15 info)) params
    and print_new (id : Ident.ident) (params : expression list) =
      try
        fprintf fmt (protect_on (prec < 1) "new %a(%a)")
          (print_type_class_name info) id
          (print_list comma (print_expression ~prec:15 info)) params
      with
        UnknownClass _ ->
        Loc.errorm ?loc:id.id_loc
          "no class attached to constructor %s (tag %d).@."
          id.id_string (Weakhtbl.tag_hash id.id_tag)

    and print_this_cstr_call (params : expression list) =
        fprintf fmt (protect_on (prec < 1) "this (%a)")
          (print_list comma (print_expression ~prec:15 info)) params

    and print_expr_from_driver (s : string) (args : expression list)
                                (pl : int list) =
      let s =
        if pl = [] || prec < List.hd pl
        then Format.sprintf "(%s)" s
        else s in
      let lte = Array.of_list args in
      let pr fmt p c i =
        match c with
        | None -> print_expression ~prec:p info fmt lte.(i - 1)
        | Some c ->
           internal_error ("bad syntax char '" ^ (String.make 1 c) ^ "'")
      in
      gen_syntax_arguments_prec fmt s pr pl

    in begin match e with
       | ExprNop -> ()
       | ExprAbsurd ->
        fprintf fmt "throw new RuntimeException(\"unreachable statement\")"
        | ExprThis -> fprintf fmt "this"
        (* | ExprTODO s -> fprintf fmt "TODO expr %s" s *)
        | ExprConst CstNull -> fprintf fmt "null"
        | ExprConst (CstInt s) -> fprintf fmt "%s" s
        | ExprConst (CstStr s) -> fprintf fmt "\"%s\"" s
        | ExprConst (CstBool true) -> fprintf fmt "true"
        | ExprConst (CstBool false) -> fprintf fmt "false"
        | ExprConst (CstEnum (id, enumtype)) ->
          fprintf fmt "%a.%a" (print_type info) enumtype
          (enum_ident_printer info) id
        | ExprUnOp (op, e) -> print_unop_expr op e
        | ExprBinOp (op, e1, e2) -> print_binop_expr op e1 e2
        | ExprITE (i, t, e) -> print_ite i t e
        | ExprFunCall (f, params) -> print_call f params
        | ExprMethodCall (ctx, m, params) -> print_method_call ctx m params
        | ExprClassOf e ->
            fprintf fmt (protect_on (prec < 1) "%a.getClass()")  (print_expression ~prec:1 info) e
       | ExprNewInstance (id, params) -> print_new id params
       | ExprThisConstructorCall (params) -> print_this_cstr_call params
       | ExprVar (vid,_) -> default_ident_printer info fmt vid
       | ExprFromDrv (s, elist, plist) -> print_expr_from_driver s elist plist
       | ExprNewArray (eltype, size) ->
          fprintf fmt "new %a[%a]"
            (print_type info) eltype
            (print_expression_no_par info) size
       | ExprArrayIndexing (array, index) ->
          fprintf fmt "%a[%a]"
            (print_expression ~prec:1 info) array
            (print_expression_no_par info) index
       | ExprDot (structexpr, field)  ->
          fprintf fmt (protect_on (prec < 1) "%a.%a")
            (print_expression ~prec:1 info) structexpr
            (instance_vars_names_printer info) field
        | ExprCast (t, e) ->
          fprintf fmt (protect_on (prec < 1) "(%a) %a")
            (print_type info) t
            (print_expression ~prec:1 info) e
        | ExprArraysEquals (a1, a2) ->
          (* fprintf fmt (protect_on (prec < 1) "Arrays.deepEquals(%a, %a)")   *)
          fprintf fmt (protect_on (prec < 1) "(%a).equals(%a)")
            (print_expression ~prec:1 info) a1
            (print_expression ~prec:1 info) a2
        | ExprArraysHashCode a ->
          fprintf fmt (protect_on (prec < 1) "(%a).hashCode()")
            (print_expression ~prec:1 info) a
       end
  and print_expression_no_par (info : info) fmt (e : expression) =
    print_expression ~prec:max_int info fmt e

  let rec print_statement ?(braces_on=true) (info : info) fmt
            (stmt : statement) =
    match stmt with
    | StmtTODO s ->
       fprintf fmt "/* TODO %s */@." s;
        unsupported "TODO Stmt"

    | StmtIf (i, t, e) -> print_if_then_else info fmt i t e
    | StmtReturn ExprNop -> fprintf fmt "@[return;@]"

    | StmtReturn e ->
       fprintf fmt "@[return %a;@]" (print_expression_no_par info) e

    | StmtSequence (s1, s2) ->
       begin
         match s1, s2 with
         | StmtNop, _ | _, StmtNop -> assert false
         | _ ->
            fprintf fmt "%a@\n%a"
              (print_statement ~braces_on:braces_on info) s1
              (print_statement ~braces_on:braces_on info) s2
       end
    | StmtExpr e ->
       fprintf fmt "@[%a;@]" (print_expression_no_par info) e

    | StmtNop -> fprintf fmt "/* nop */"

    | StmtBlock ([], s) -> print_statement ~braces_on:false info fmt s
    | StmtBlock (decllist, s) ->
       let fpf =
         if braces_on then
           fprintf fmt "@[<2>{@\n%a@\n%a@]@\n}"
         else fprintf fmt "@\n%a@\n%a@\n" in

       fpf
         (* (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "@\n") *)
         (pp_print_list ~pp_sep:newline
            (print_definition info)) decllist
         (print_statement ~braces_on:false info) s

    | StmtThisConstructor s ->
       print_statement ~braces_on:braces_on info fmt s

    | StmtWhile (cond, loopstmt) ->
       fprintf fmt "@[@[<2>while (%a) {@\n%a@]@\n}@]"
         (print_expression_no_par info) cond
         (print_statement ~braces_on:false info) loopstmt

    | StmtFor (i, it, init, cond, step, loopstmt) ->
       fprintf fmt "@[@[<2>for (%a %a = %a; %a; %a) {@\n%a@]@\n}@]"
         (print_type info) it
         (default_ident_printer info) i
         (print_expression_no_par info) init
         (print_expression_no_par info) cond
         (print_expression_no_par info) step
         (print_statement ~braces_on:false info) loopstmt

    | StmtBreak -> fprintf fmt "@[break;@]"
    | StmtContinue -> fprintf fmt "@[continue;@]"
    | StmtThrow (xs, ExprNop) ->
       if is_known_java_exception info xs then
         let sopt = query_syntax info.syntax xs.xs_name in
         fprintf fmt "@[throw new %s ();@]" (Option.get sopt)
       else
         fprintf fmt "@[throw new %a ();@]"
                (print_class_name info) (get_exception_class xs)
    | StmtThrow (xs, v) ->
       if is_known_java_exception info xs then
         internal_error "java exception with arguments"
       else
         fprintf fmt "@[throw %a;@]" (print_expression_no_par info) v
    | StmtTry (st, cl) ->
       fprintf fmt "@[@[<hov 2>try {@\n%a@]@\n} %a@]"
         (print_statement ~braces_on:false info) st
         (pp_print_list ~pp_sep:space (print_catch_clause info)) cl
  and print_catch_clause (info : info) fmt (xs, pvs, st) =
    debug "print_catch_clause@.";
    let javaex = is_known_java_exception info xs in
    match pvs with
    | None ->
       if javaex then
         let sopt = query_syntax info.syntax xs.xs_name in
         fprintf fmt "@[catch (%s %a) {@\n%a@]@\n}"
           (Option.get sopt) (default_ident_printer info) anonymous_exception_id
           (print_statement info) st
       else
         fprintf fmt "@[catch (%a %a) {@\n%a@]@\n}"
           (print_class_name info) (get_exception_class xs)
           (default_ident_printer info) anonymous_exception_id
           (print_statement info) st
    | Some p ->
       if javaex then
         internal_error "java exception with arguments in catch"
       else
         fprintf fmt "@[catch (%a %a) {@\n%a@]@\n}"
           (print_class_name info) (get_exception_class xs)
           (default_ident_printer info) p.pv_vs.vs_name
           (print_statement info) st
  and print_if_then_else (info : info) fmt i t e =
    if is_nop e then
      fprintf fmt "@[<hov 2>if (%a) {@\n@[<hov>%a@]@]@\n}"
        (print_expression_no_par info) i
        (print_statement ~braces_on:false info) t
    else if is_ite e then
       begin
         let rec decompose_cascading_ite i t e =
           match e with
           | StmtIf (i', t', e') ->
              let first_cond, elses, last = decompose_cascading_ite i' t' e' in
              (i,t), first_cond:: elses, last
           | _ -> (i,t), [] , e
         in
         let print_cascading_ite i t e =
           let (i,t), elselist, last = decompose_cascading_ite i t e in
           fprintf fmt "@[<hov 2>if (%a) {@\n%a@]@\n"
             (print_expression_no_par info) i
             (print_statement info) t;
           pp_print_list ~pp_sep:newline
             (fun fmt (i,t) ->  fprintf fmt "@[<hov 2>} else if (%a) {@\n%a@]"
                                  (print_expression_no_par info) i
                                  (print_statement ~braces_on:false info) t)
             fmt elselist;
           fprintf fmt "@\n@[<hov 2>}";
           if is_nop last then
             fprintf fmt "@]@\n"
           else
             fprintf fmt " else {@\n%a@]@\n}@\n"
               (print_statement ~braces_on:false info) last

         in
         print_cascading_ite i t e
       end
    else match t, e with
         | StmtReturn te, StmtReturn ee
              when is_true_expr te && is_false_expr ee
           -> fprintf fmt "@[return %a;@]" (print_expression_no_par info) i
         | StmtReturn te, StmtReturn ee
              when is_false_expr te && is_true_expr ee
           -> fprintf fmt "@[return ! (%a);@]" (print_expression_no_par info) i
         | _ ->
            fprintf fmt
              "@[<hov 2>if (%a) {@\n@[<hov>%a@]@]@\n@[<hov 2>} else {@\n@[<hov>%a@]@]@\n}"
              (print_expression_no_par info) i
              (print_statement ~braces_on:false info) t
              (print_statement ~braces_on:false info) e
  and print_method_body (info : info) fmt ((dl,s) : body) =
    fprintf fmt "%a@\n%a"
      (pp_print_list ~pp_sep:newline (print_definition info)) dl
      (print_statement ~braces_on:false info) s

  and print_raised_exception (info : info) fmt (exlist : xsymbol list) =
    let print_ex fmt (ex : xsymbol) =
      match query_syntax info.syntax ex.xs_name with
      | Some s -> pp_print_string fmt s
      | None -> print_class_name info fmt (get_exception_class ex)
    in
    if List.length exlist > 0 then
      fprintf fmt "@[ throws %a@]"
        (pp_print_list ~pp_sep:comma print_ex) exlist

  and print_method (info : info) fmt (is_final : is_final) (vis : visibility) is_static (id : ident)
        (restype : type_definition)
        (args : (ident * type_definition) list)
        (exlist : xsymbol list)
        (body : body) =
    fprintf fmt "@[@[<2>%a%s%a%a %a(@[%a@])%a {@\n@[%a@]@]@\n}@]"
      print_visibility vis
      (if is_final then "final " else "")
      print_static_spec is_static
      (print_type info) restype
      (method_names_printer info) id
      (print_function_args info) args
      (print_raised_exception info) exlist
      (print_method_body info) body
  and print_abstract_method (info : info) fmt (vis : visibility) (id : ident)
        (restype : type_definition)
        (args : (ident * type_definition) list)
        (exlist : xsymbol list) =
    fprintf fmt "@[%a%a%a %a(@[%a@])%a;@]"
      print_visibility vis
      print_abstract_spec ()
      (print_type info) restype
      (method_names_printer info) id
      (print_function_args info) args
      (print_raised_exception info) exlist

  and print_constructor (info : info) fmt  (vis : visibility)
                         (args : (ident * type_definition) list)
                         (exlist : xsymbol list)
                         (body : body) =
    fprintf fmt "@[@[<2>%a%a(@[%a@])%a {@\n@[%a@]@]@\n}@]"
      print_visibility vis
      (classname_printer info) (get_current_class_name ())
      (print_function_args info) args
      (print_raised_exception info) exlist
      (print_method_body info) body
  and print_local_var_decl (info : info) fmt (tdef : type_definition)
                         (idval_list : (ident * expression) list) =
    let print_init info fmt (id, value : ident * expression) =
      default_ident_printer info fmt id;
      match value with
      | ExprNop -> ()
      | _ -> fprintf fmt " = %a" (print_expression_no_par info) value
    in
    fprintf fmt "@[%a %a;@]"
      (print_type info) tdef
      (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ",@ ")
         (print_init info)) idval_list

  and print_definition (info : info) fmt (def : JavaAST.definition) =
    match def with
    | DeclEnum (vis, id, ident_list) ->
       print_enum_decl info fmt  vis id ident_list
    | DeclInstanceVar (vis, is_final, ident, typedef) ->
       print_instance_var info fmt vis ident typedef ~isfinal:is_final
    | DeclNotImplemented s ->
       fprintf fmt "/* %s: not implemented */" s
    | DeclMethod (is_final, vis, is_static, id, restype, parameters, exlist, body) ->
       print_method info fmt is_final vis is_static id restype parameters exlist body
    | DeclAbstractMethod (vis, id, restype, parameters, exlist) ->
       print_abstract_method info fmt vis id restype parameters exlist
    | DeclConstructor (vis, parameters, exlist, body) ->
       print_constructor info fmt vis parameters exlist body
    | DeclLocalVar (typedef, idval_list) ->
       print_local_var_decl info fmt typedef idval_list

end


module MLW2Java = struct
  open JavaAST
  open JavaCompilerInfo
  open Number

  type translation_env = {
      info : info;
      is_return : bool;
      in_constructor : bool;
    }

  let rec translate_type (info : info) (t : Mltree.ty)
          : JavaAST.type_definition =
    match t with
    | Tvar tvs ->
       Loc.errorm ?loc:tvs.tv_name.id_loc "unsupported type variable '%s'"
         tvs.tv_name.id_string
    | Ttuple ([]) ->
       VoidType
    | Ttuple ([ty]) ->
       translate_type info ty
    | Ttuple _ ->
       unsupported "tuples type"
    | Tapp (id, []) when is_this_type id ->
       ThisType
    | Tapp (id, []) when is_enum_type id ->
       TypeEnum id
    | Tapp (id, ty_list) ->
       begin
         match (query_syntax info.syntax id) with
         | Some s ->
            let args = List.map (translate_type info) ty_list in
            let so = Sattr.mem java_scalar_objects id.id_attrs in
            TypeFromDrv (s, args, so)
         | None ->
            if List.length ty_list = 0 then
              TypeAlias id
            else
              unsupported ("app type '" ^ id.id_string ^ "'")
       end
    | Tarrow (ty1, ty2) ->
       let _ = translate_type info ty1 in
       let _ = translate_type info ty2 in
       unsupported "arrow type"

  (**
     Translate an algebraic type containing only 0-ary constructors as an enum
     type. The enum type is declared inside the genrated class as an inner
     class.
     @param info syntax driver data
     @param id name of the enum  type
     @param clist list of contructors
     @raise Unsupported if a conbstructor takes arguments
   *)
  let translate_enum_def (_ : info) (id : ident)
        (clist : (ident * ty list) list)
      : JavaAST.definition list =
    let get_enum_value (constr_id, constr_args) : ident =
      if List.length constr_args = 0 then
        constr_id
      else
        unsupported ("non enum algebraic types (type '" ^ id.id_string ^ "')")
    in
    let enums = List.map get_enum_value clist in
    let visibility = get_visibility ~default:(get_default_visibility ()) id in
    set_enum_values id (Sid.of_list enums);
    [ DeclEnum (visibility, id, enums) ]


  exception EqualsTypeFailure
  let obj_id = Ident.id_register (Ident.id_fresh "obj")
  let obj_var = ExprVar(obj_id, object_type_from_drv)
  let other_id = Ident.id_register (Ident.id_fresh "other")
  let other_var = ExprVar(other_id, ThisType)

  let is_array_type (tdef : ty) : bool =
    match tdef with
    | Tapp (id, _) when Sattr.mem array_attr id.id_attrs -> true
    | _ -> false

  let add_equals_method (info : info) (fields : (is_mutable * ident * ty) list) : JavaAST.definition =
    let compare_fields ((_ : is_mutable), (id : Ident.ident), (tdef : ty)) : statement =
      let this_field = ExprDot (ExprThis, id) in
      let other_field = ExprDot (other_var, id) in
      let mk_check_null e = mk_ite (mk_eq this_field null_expr) (mk_eq other_field null_expr) e in
      let cond =
        if is_array_type tdef then ExprArraysEquals (this_field, other_field)
        else match translate_type info tdef with
        | TypeEnum _
        | TypeFromDrv ("int", [], false)
        | TypeFromDrv ("boolean", [], false) -> mk_eq this_field other_field
        | TypeFromDrv _
        | TypeAlias _ -> mk_check_null (ExprMethodCall (this_field, equals_method_id, [other_field]))
        | VoidType
        | ThisType -> raise EqualsTypeFailure
      in mk_if (mk_not cond) (StmtReturn false_expr) (StmtNop)
    in
    let body = mk_seq_of_list [
      mk_if (mk_eq ExprThis obj_var) (StmtReturn true_expr) (StmtNop);
      mk_if (mk_eq obj_var (ExprConst CstNull)) (StmtReturn false_expr) (StmtNop);
      mk_if (mk_neq (ExprClassOf ExprThis) (ExprClassOf obj_var)) (StmtReturn false_expr) (StmtNop);
      StmtBlock (mk_body
        [ DeclLocalVar (ThisType, [ (other_id, ExprCast (ThisType, obj_var)) ]) ]
        (mk_seq_of_list (List.append (List.map compare_fields fields) [ (StmtReturn true_expr)]))
        )
      ]
    in
    let equals_ast = DeclMethod (
      true,
      PUBLIC,
      false, (* not a static method *)
      equals_method_id,  (* method id *)
      boolean_type_from_drv, (* return type *)
      [(obj_id, object_type_from_drv)], (* parameters *)
      [], (* no exception *)
      mk_body [] body
      )
    in
      add_method (Some 0) equals_method_id;
      equals_ast

  exception HashCodeTypeFailure
  let local_hash_value_id = Ident.id_register (Ident.id_fresh "hash_value")
  let local_hash_value_var = ExprVar(local_hash_value_id, int_type_from_drv)

  let add_hashcode_method (info : info) (fields : (is_mutable * ident * ty) list) : JavaAST.definition =
    let hash_code_field ((_ : is_mutable), (id : Ident.ident), (tdef : ty)) : statement =
      let this_field = ExprDot (ExprThis, id) in
      let mk_if_not_null e = mk_ite (mk_eq this_field null_expr) zero_expr e in
      let hvalue =
        if is_array_type tdef then mk_if_not_null (ExprArraysHashCode this_field)
        else
          match translate_type info tdef with
          | TypeEnum _ -> ExprMethodCall (this_field, hashcode_method_id, [])
          | TypeFromDrv ("int", [], false) -> this_field
          | TypeFromDrv ("boolean", [], false) -> mk_ite this_field one_expr zero_expr
          | TypeAlias _
          | TypeFromDrv _ -> mk_if_not_null (ExprMethodCall (this_field, hashcode_method_id, []))
          | VoidType
          | ThisType -> raise HashCodeTypeFailure
      in
        StmtExpr (mk_assign
                  local_hash_value_var
                  (mk_add (mk_mul (mk_int 31) local_hash_value_var) hvalue))
    in
    let body =
      mk_seq_of_list (List.append (List.map hash_code_field fields) [ (StmtReturn local_hash_value_var)])
    in
    let hashcode_ast = DeclMethod (
      true,
      PUBLIC,
      false, (* not a static method *)
      hashcode_method_id,  (* method id *)
      int_type_from_drv, (* return type *)
      [], (* no arguments *)
      [], (* no exception *)
      mk_body
       [DeclLocalVar (int_type_from_drv, [ (local_hash_value_id, one_expr) ])]
       body
      )
    in
      add_method (Some 0) hashcode_method_id;
      hashcode_ast

  let add_default_methods (info : info) (fields : (is_mutable * ident * ty) list) : JavaAST.definition list =
    [
      add_equals_method info fields;
      add_hashcode_method info fields;
    ]

  (**
     Translate a record type as a list of instance variables. If a field isn't
     declared as mutable it is compiled as a 'final' instance variable.

     @param info syntax driver data
     @param id identifier of the declared type
     @param fieldlist list of fields in the record
     @raise Unsupported if the type of the field is not supported or several
       record types are defined.
   *)
  let translate_record_def (info : info) (id : ident)
            (fieldlist : (is_mutable * ident * ty) list)
      : JavaAST.definition list =
    if is_static_class () then (* The type of 'this' is not yet defined. *)
      begin
        let visibility =
          get_visibility ~default:(get_default_visibility ()) id in
        let translate_field (not_final, field_ident, field_type)
            : instance_variable =
          let jtype = translate_type info field_type in
          let is_final = not not_final in
          let fvis = get_visibility ~default:visibility field_ident in
          (fvis, is_final, field_ident, jtype)
        in
        let fields = List.map translate_field fieldlist in

        set_this_type id fields;
        List.append (List.map (fun iv -> DeclInstanceVar iv) fields)
                               (add_default_methods info fieldlist)
      end
    else
      unsupported "declaration of several record types"

  let translate_type_decl (info : info) (tdef : Mltree.its_defn)
      : JavaAST.definition list =
    let type_id = tdef.its_name in
    if Sattr.mem java_ignore type_id.id_attrs then
      []
    else if not (Option.is_some tdef.its_def) then
      begin
        set_this_type type_id [];
        []
      end
    else match Option.get tdef.its_def with
         | Ddata constructor_list ->
            translate_enum_def info type_id constructor_list
         | Drecord field_list ->
            if is_interface () then
              Loc.errorm ?loc:type_id.id_loc
                "fields are not allowed in interface";
            translate_record_def info type_id field_list
         | Dalias t ->
            let tt = translate_type info t in
            Loc.errorm ?loc:type_id.id_loc "unsupported alias type %a = %a@."
              (JavaPrint.default_ident_printer info) type_id
              (JavaPrint.print_type info) tt
         | Drange _ -> unsupported "range type"
         | Dfloat _ -> unsupported "float type"

  let translate_function_arguments ~(is_cstr:bool)
        (info : info) (vlist : var list)
        (_ : Ty.Stv.t)  : (ident * type_definition) list * int option =

    let rec aux vl res has_unit this_index =
      match vl with
      | [] -> res, this_index
      | (id, ty, is_ghost) :: tl ->
         assert (not is_ghost);
         match ty with
         | Tapp (typeid, []) when is_this_variable id typeid ->
            if is_cstr then
              unsupported ("'" ^ this_id ^ "' is not allowed in constructors")
            else if not (Option.is_some this_index) then
              aux tl res has_unit (Some (List.length res))
            else
              internal_error "self occurs twice in arguments"
         | Tapp (typeid, _)
              when Ident.id_equal typeid Pmodule.ts_ref.ts_name ->
            unsupported "function with ref arguments"
         | _ ->
            let jtype = translate_type info ty in
            if is_void jtype then
              begin
                if has_unit then
                  unsupported "function with multiple unit parameters";
                if not (is_dummy id) then
                  unsupported ("non-dummy parameter '" ^ id.id_string ^ "'");
                aux tl (res @ [ (id, jtype) ]) true this_index
              end
            else
              aux tl (res @ [ (id, jtype) ]) has_unit this_index
    in
    aux vlist [] false None

  let expr_or_return (e: expression) (env : translation_env) : statement =
    if env.is_return then
      StmtReturn e
    else
      StmtExpr e

  (** Convert an integer constant into a string according to rules specified
      in the driver file. The rules use the format:
      syntax literal <a type> <fmtstring>
      The format string is processed with Printer.syntax_range_literal.
   *)
  let integer_constant_to_string
        (env : translation_env)
        (ic : Number.int_constant)
        (csttype : Mltree.ty) =
    let open Number in
    let print fmt ic =
      let n = ic.il_int in
      if BigInt.lt n BigInt.zero
      then
        (* default to base 10 for negative literals *)
        Format.fprintf fmt "-%a" (print_in_base 10 None) (BigInt.abs n)
      else
        match ic.il_kind with
        | ILitHex | ILitBin
          -> Format.fprintf fmt "0x%a" (print_in_base 16 None) n
        | ILitOct -> Format.fprintf fmt "0%a" (print_in_base 8 None) n
        | ILitDec | ILitUnk ->
           (* default to base 10 *)
           print_in_base 10 None fmt n in
    let tname = match csttype with
      | Tapp (id, _) -> id
      | _ -> assert false in
    match query_syntax env.info.literal tname with
    | Some st ->
       Format.asprintf "%a" (syntax_range_literal ~cb:(Some print) st) ic
    | _ ->
       unsupported ("unspecified number format for type " ^ tname.id_string)

  let rec translate_body ~(cstr : bool) (info : info) (expr : Mltree.expr)
          : body =
    let env = { info = info; is_return = true; in_constructor = cstr } in
    let d, s = translate_expression expr env in
    mk_body ~simplify:true d s
  and translate_constant (cst : expr) (env : translation_env) : body =
    let e = match cst.e_node with
    | Econst (Constant.ConstInt (icst:Number.int_constant)) ->
       let cststr = integer_constant_to_string env icst cst.e_mlty in
      ExprConst (CstInt cststr)
    | Econst (Constant.ConstStr s)  ->
      ExprConst (CstStr s)
    | Econst (Constant.ConstReal _) ->
       unsupported "floating point values"
    | _ -> unreachable "translate_constant"
    in mk_body [] (expr_or_return e env)
  and translate_if cond then_expr else_expr env : body =
    debug "IF@.";
    let cbody =
      translate_expression cond { env with is_return = false } in
    let cbody = simplify_cond cbody in
    let tblock = StmtBlock (translate_expression then_expr env) in
    let eblock = StmtBlock (translate_expression else_expr env) in
    begin
      match cbody with
      | [], StmtExpr c ->
         debug "IF done@.";
         mk_body [] (mk_if c tblock eblock)
      | decllist, condstmt ->
         (* TODO: generate a safe variable "cond_" that does not clash
            with another one. *)
         let cid = id_register (id_fresh "cond_") in
         let cidtype = boolean_type_from_drv in
         let cidvar = ExprVar (cid, cidtype) in
         let ciddecl = DeclLocalVar (cidtype, [cid, ExprNop]) in
         debug "IF done@.";
         mk_body
           (ciddecl :: decllist)
           (mk_seq (assign cidvar condstmt) (mk_if cidvar tblock eblock))
    end
  and translate_while (cond : expr) (loop : expr) (env : translation_env)
      : body =
    debug "WHILE@.";

    let env_nr = { env with is_return = false} in
    let b = StmtBlock (translate_expression loop env_nr) in
    let cdecl, cstmt = simplify_cond (translate_expression cond env_nr) in
    let whilestmt =
      match get_last_expr cstmt with
      | StmtNop, e ->
         StmtWhile (e, b)
      | stmt, e ->
         StmtWhile (true_expr,
                    mk_seq_of_list [stmt; StmtIf (e, StmtBreak, StmtNop); b ] )
    in
    debug "WHILE Done@.";
    mk_body cdecl whilestmt

    and translate_array_make (a_id : Ident.ident) (a_type : type_definition)
                            (n : expr) (v : expr)
                            (env : translation_env) : expression * body =
    let env_nr = { env with is_return = false } in
    let vtype = translate_type env.info v.e_mlty in
    let ndecl, nstmt, n = translate_expression_and_get_last_expr n env_nr in
    let vdecl, vstmt, v = translate_expression_and_get_last_expr v env_nr in
    (* declaration of the array 'a' *)
    let arr_var = ExprVar (a_id, a_type) in
    let arr_decl = [DeclLocalVar (a_type, [a_id, ExprNewArray (vtype, n)])] in
    (* Fill a_ with v *)
    let i_id = id_register (id_fresh "i_") in
    let i_type = int_type_from_drv in
    let filldecl, fillstmt =
      mk_for i_id i_type zero_expr To (ExprBinOp (BinOpSub, n, one_expr))
        (fun iexpr ->
          StmtExpr(ExprBinOp (BinOpAssign, ExprArrayIndexing (arr_var, iexpr),
                              v)))
    in
    arr_var, mk_body
               (ndecl @ vdecl @ arr_decl @ filldecl)
               (mk_seq_of_list [nstmt; vstmt; fillstmt])
  and translate_array_constructor (e : expr) (n : expr) (v : expr)
      (env : translation_env) : body =
    let arr_id = id_register (id_fresh "a_") in
    let etype = translate_type env.info e.e_mlty in
    let var, (d, s) = translate_array_make arr_id etype n v env in
    mk_body d (mk_seq s (expr_or_return var env))

  and translate_app_arg_list (args : expr list) (env : translation_env)
      : body * expression list =
    let rec aux (accdefs : definition list) (accstmt : statement)
              (accparams : expression list) = function
      | [] -> ((accdefs, accstmt), accparams)
      | arg :: tl ->
         let decllist, stmt, e =
           translate_expression_and_get_last_expr arg env in

         aux (accdefs@decllist) (mk_seq accstmt stmt) (accparams @ [e]) tl
    in aux [] StmtNop [] args
  and translate_app_call (e : expr) (rs : rsymbol) (params : expression list)
                          (env : translation_env) : expression =
    match query_syntax env.info.syntax rs.rs_name with
    | Some s ->
       let p = Mid.find rs.rs_name env.info.prec in
       ExprFromDrv (s, params, p)
    | None ->
       match rs.rs_field with
       | None ->
          if Sattr.mem java_constructor rs.rs_name.id_attrs then
            begin
            match translate_type env.info e.e_mlty with
            | TypeAlias id ->
               ExprNewInstance (id, params)
            | ThisType when env.in_constructor && env.is_return ->
               ExprThisConstructorCall (params)
            | ThisType ->
               ExprNewInstance (get_this_type (), params)
            | _ ->
               internal_error "bad type for constructor invocation"
            end
          else
            let ftype = translate_type env.info e.e_mlty in
            begin
            match get_method_opt rs.rs_name with
            | Some { this_index = None } ->
               ExprMethodCall (ExprNop, rs.rs_name, params)
            | Some { this_index = Some index } ->
               begin
                 try
                   let this = List.nth params index in
                   let params =
                     Lists.fold_lefti
                       (fun acc i param ->
                         if i = index then acc else acc @ [param])
                       [] params in
                   ExprMethodCall (this, rs.rs_name, params)
                 with
                 | Failure _ | Invalid_argument _
                   -> internal_error "wrong 'this' index"
               end
            | None -> ExprFunCall (ExprVar (rs.rs_name, ftype), params)
            end
       | Some _ when List.length params = 1 ->
          (* Accesses to field of record use function call *)
          ExprDot (List.hd params, rs.rs_name)
       | Some pv ->
          debug "arglist=%d@." (List.length params);
          unsupported ("field '" ^ (pv.pv_vs.vs_name.id_string) ^
                         "' of structure '" ^ rs.rs_name.id_string ^ "'")

  and translate_this_constructor (e : expr) (rs : rsymbol) (args : expr list)
                                  (env : translation_env) : body =
       debug "this constructor '%s'@." rs.rs_name.id_string;
       let env_nr = { env with is_return = false } in
       let (decls, stmt), params = translate_app_arg_list args env_nr in
       let tid = match e.e_mlty with
         | Tapp (id, []) -> id
         | _ -> internal_error "this_constructor: expr has bad type"
       in
       try
         let clsrec = get_class tid in
         let assign_instance_var ((_, _, idv, _) : instance_variable) (value : expression) : statement =
           StmtExpr(ExprBinOp (BinOpAssign, ExprDot (ExprThis, idv), value))
         in
         let assignments = List.map2 assign_instance_var clsrec.instance_vars params in
         mk_body decls
           (StmtThisConstructor (mk_seq_of_list ([stmt] @ assignments)))

       with
         UnknownClass _ -> internal_error "this_constructor: unknown type id"

  (**
     Translate expression 'e' that is the application of 'rs' to 'args'
   *)
  and translate_app (e : expr) (rs : rsymbol) (args : expr list)
                     (is_partial : bool) (env : translation_env) : body =
    if is_partial then
      unsupported "partial application";

    let is_record_cstr =
      is_constructor env.info rs.rs_name
      && query_syntax env.info.syntax rs.rs_name = None in
    match args with
    (* true -> true *)
    | []  when rs_equal rs rs_true  ->
       mk_body []  (expr_or_return (ExprConst (CstBool true)) env)
    (* false -> false *)
    | []  when rs_equal rs rs_false  ->
       mk_body [] (expr_or_return (ExprConst (CstBool false)) env)
    (* id -> id *)
    | [] ->
       let res = match translate_type env.info e.e_mlty with
         | TypeEnum _ as enumtype ->
            ExprConst(CstEnum (rs.rs_name, enumtype))
         | vtype ->
            debug "EVAR %s\n" rs.rs_name.id_string;
            begin
              match query_syntax env.info.syntax rs.rs_name with
                None ->  ExprVar (rs.rs_name, vtype)
              | Some s ->
                 let p = Mid.find rs.rs_name env.info.prec in
                 ExprFromDrv (s, [], p)
            end
       in
       mk_body [] (expr_or_return res env)
    (* ref expr -> expr *)
    | [arg] when rs_equal rs Pmodule.rs_ref ->
       begin
         try
           let env_nr = { env with is_return = false } in
           let e = expr_of_body (translate_expression arg env_nr) in
           mk_body [] (expr_or_return e env)
         with ExprOfBodyFailure -> unsupported "argument to ref"
       end
    | [n; v] when  Sattr.mem array_mk_attr rs.rs_name.id_attrs ->
       translate_array_constructor e n v env

    | _ when is_record_cstr && env.in_constructor ->
       if env.is_return then
         translate_this_constructor e rs args env
       else
         Loc.errorm "record constructor are allowed as return values only."

    | _ when is_record_cstr && not env.in_constructor  ->
       debug "call record constructor '%s'@." rs.rs_name.id_string;
       unsupported ("record constructor ('" ^ rs.rs_name.id_string ^ "') call out of a java constructor")
    | _ ->
       (* f a_1 ... a_n *)
       (* WARNING: tuples are not handled *)
       debug "call to '%s' @." rs.rs_name.id_string;
       let env_nr = { env with is_return = false } in
       let (decls, stmt), params = translate_app_arg_list args env_nr in
       let appcall = translate_app_call e rs params env in
       let callstmt = match appcall with
         | ExprThisConstructorCall _-> StmtExpr appcall
         | _ -> begin
             match e.e_mlty with
             | Ttuple [] when env.is_return -> (* unit case *)
                mk_seq (StmtExpr appcall) (StmtReturn ExprNop)
             | _ -> expr_or_return appcall env
           end
       in
       mk_body decls (mk_seq stmt callstmt)

  and translate_block (elist : expr list) (env : translation_env) : body =
    match elist with
    | [] -> mk_body [] (expr_or_return ExprNop env)
    | [e] -> translate_expression e env
    | e :: tl ->
       let env_nr = { env with is_return = false } in
       mk_body [] (mk_seq (StmtBlock (translate_expression e env_nr))
                     (StmtBlock (translate_block tl env)))

  and translate_for (it : Ity.pvsymbol) (it_type : ty)
                     (firstval : expr)
                     (dir : Mltree.for_direction)
                     (lastval : expr)
                     (body : expr)
                     (env : translation_env) : body =
    debug "FOR@.";
    match it.pv_vs.vs_ty.ty_node with
    | Tyapp ({ ts_def = Range { ir_lower = _; ir_upper = _ }},_) ->
       let env_nr = { env with is_return = false } in
       let it_id = it.pv_vs.vs_name in
       let j_it_type = translate_type env.info it_type in
       let ds, ss, es =
         translate_expression_and_get_last_expr firstval env_nr in
       let de, se, ee =
         translate_expression_and_get_last_expr lastval env_nr in
       let sfor = mk_for it_id j_it_type es dir ee
         (fun _ ->
           StmtBlock (translate_expression body env_nr)) in
       mk_body [] (mk_seq_of_list [ (StmtBlock (mk_body ds ss));
                                    (StmtBlock (mk_body de se));
                                    (StmtBlock sfor) ])
    | _ -> unsupported "for loops where loop index is not a range type"

  and translate_pvsymb_for (it : Ity.pvsymbol) (it_type : ty)
                           (firstval : Ity.pvsymbol)
                           (dir : Mltree.for_direction)
                           (lastval : Ity.pvsymbol)
                           (body : expr)
                     (env : translation_env) : body =
    debug "FOR@.";
    match it.pv_vs.vs_ty.ty_node with
    | Tyapp ({ ts_def = Range { ir_lower = lb; ir_upper = ub }},_) ->
       debug "range %s [%d %d] %s %s\n"
         it.pv_vs.vs_name.id_string
         (BigInt.to_int lb) (BigInt.to_int ub)
         firstval.pv_vs.vs_name.id_string lastval.pv_vs.vs_name.id_string ;
       let it_id = it.pv_vs.vs_name in
       let j_it_type = translate_type env.info it_type in
       let first_var = ExprVar (firstval.pv_vs.vs_name, j_it_type) in
       let last_var = ExprVar (lastval.pv_vs.vs_name, j_it_type) in
       mk_for it_id j_it_type first_var dir last_var
         (fun _ ->
           StmtBlock (translate_expression body { env with is_return = false }))
    | _ -> unsupported "for loops where loop index is not a range type"

  and translate_let (ldef : let_def) (inexpr : expr)
                    (env : translation_env) : body =
    debug "LET@.";
    let env_nr = { env with is_return = false } in
    match ldef with
    | Lsym (rs, _, _, _, _) ->
       unsupported ("let '" ^ rs.rs_name.id_string ^ "'")
    | Lrec _ -> unsupported "let LDrec"
    | Lany _ -> unsupported "let Lany"
    | Lvar (pv, le) -> (* not a block *)
       let id = pv.pv_vs.vs_name in
       debug "let %s \n" id.id_string ;
       let jtype = translate_type env.info le.e_mlty in
       let arrdecl, initblock =
         match le with
         | { e_node = Eapp (rs, [n; v], _) }
              when Sattr.mem array_mk_attr rs.rs_name.id_attrs ->
            debug "new array '%s' \n" id.id_string;
            let _, (d, s) = translate_array_make id jtype n v env_nr in
            true, (d, s)
         | _ ->
            let (d,s) = translate_expression le env_nr in
            false, (d, assign (ExprVar (id, jtype)) s)
       in
       let inexprbody = translate_expression inexpr env in
       match initblock with
       | d, StmtExpr(ExprBinOp(BinOpAssign, (ExprVar (id, _)), valid))
            when not arrdecl ->
          mk_body (d@[ DeclLocalVar (jtype, [ id, valid ]) ])
            (StmtBlock inexprbody)
       | _ when arrdecl ->
          mk_body [] (mk_seq (StmtBlock initblock) (StmtBlock inexprbody))
       | _ ->
          mk_body [ DeclLocalVar (jtype, [ id, ExprNop ]) ]
            (mk_seq (StmtBlock initblock) (StmtBlock inexprbody))

  and translate_single_assign (lv : expr) (_ : ty) (field: rsymbol)
                               (rv : expr) (env : translation_env) : body =
    debug "assign a mutable field '%a'@."
      (JavaPrint.default_ident_printer env.info) field.rs_name;
    let env_nr = { env with is_return = false } in
    let rvd, rvs, rve = translate_expression_and_get_last_expr rv env_nr in
    let lvd, lvs, lve = translate_expression_and_get_last_expr lv env_nr in
    let field = ExprDot (lve, field.rs_name) in
    let fieldassign = StmtExpr(ExprBinOp (BinOpAssign, field, rve)) in
    debug "assignment is  %a@." (JavaPrint.print_statement env.info) fieldassign;
    mk_body (rvd @ lvd) (mk_seq_of_list [rvs; lvs; fieldassign ])

  and translate_assign (assignlist : (expr * ty * rsymbol * expr) list)
(env : translation_env) : body =
    match assignlist with
    | [ (e1,ty,rs,e2) ] -> translate_single_assign e1 ty rs e2 env
    | _ -> unsupported "parallel assignment of mutables"

  and translate_raise (xs : Ity.xsymbol) (value : expr option)
                      (env : translation_env) : body =
    debug "RAISE %s@." xs.xs_name.id_string;
    if String.equal xs.xs_name.id_string break_id then
      mk_body [] StmtBreak
    else if String.equal xs.xs_name.id_string continue_id then
      mk_body [] StmtContinue
    else if String.equal xs.xs_name.id_string return_id then
      match value with
      | Some e ->
         translate_expression e { env with is_return = true }
      | None ->
         (* TODO: is it necessary to check the return type of the
            currently translated function ? *)
      mk_body ~simplify:false [] (StmtReturn ExprNop)
    else let javaex = is_known_java_exception env.info xs in
      match value with
         | None ->
            mk_body [] (StmtThrow (xs, ExprNop))
         | Some v ->
            if javaex then
              Loc.errorm ?loc:xs.xs_name.id_loc
                "Java exceptions with arguments not supported."
                xs.xs_name.id_string
            else
              let env_nr = { env with is_return = false } in
              let dme, sme, me =
                translate_expression_and_get_last_expr v env_nr in
              mk_body dme (mk_seq sme (StmtThrow (xs, me)))

  and translate_catch_clauses (xl : exn_branch list) (env : translation_env)
      : catch list =
    match xl with
    | [] -> []
    | (xs, pvsl, e)::l ->
       debug "catch_clauses %s @." xs.xs_name.id_string;
       if String.equal xs.xs_name.id_string break_id ||
             String.equal xs.xs_name.id_string continue_id ||
               String.equal xs.xs_name.id_string return_id
       then raise (UnknownException xs.xs_name.id_string)
       else
         let _ = is_known_java_exception env.info xs in
         let cl = translate_catch_clauses l env in
         let st = StmtBlock (translate_expression e env) in
         debug "catch_clauses II @.";
         let cc =
           match pvsl with
           | [] -> (xs, None, st)
           | [pvs] -> (xs, Some pvs, st)
           | _ -> Loc.errorm ?loc:xs.xs_name.id_loc
                    "unsupported multiple pvsymbol in try-catch pattern matching."
         in cc :: cl
  and translate_match_exceptions (mexpr : expr) (xl : exn_branch list)
                                 (env : translation_env) : body =
    let b = translate_expression mexpr env in
    try
      let cclist = translate_catch_clauses xl env in
      mk_body [] (StmtTry (StmtBlock b, cclist))
    with
      UnknownException _ -> b (* for special exceptions like Return *)


  and translate_match_constructors (mexpr : expr) (patterns : reg_branch list)
      (env : translation_env) : body =
    let enumtype = translate_type env.info mexpr.e_mlty in
    let enumvalues = match enumtype with
      | TypeEnum typeid -> get_enum_values typeid
      | _ -> unsupported "non enum type in pattern matching"
    in
    let env_nr = { env with is_return = false } in
    let dme, sme, me =
      translate_expression_and_get_last_expr mexpr env_nr in
    let rec pattern_cond (p : pat) =
      match p with
      | Pwild -> true_expr
      | Papp (ls, []) when Mid.mem ls.ls_name enumvalues ->
         ExprBinOp (BinOpEQ, me, ExprConst (CstEnum (ls.ls_name, enumtype)))
      | Por (p1, p2) ->
         let p1c = pattern_cond p1 in
         let p2c = pattern_cond p2 in
         ExprBinOp (BinOpOr, p1c, p2c)
      | _ -> unsupported "non enum in pattern-matching"
    in
    let rec aux (patterns : reg_branch list) =
      match patterns with
      | [] -> StmtNop
      | [(_, pe)] ->
         let bpe = translate_expression pe env in
         (StmtBlock bpe)
      | (p, pe)::tl ->
         let tlstmt = aux tl in
         let bpe = translate_expression pe env in
         let cond = pattern_cond p in
         mk_if cond (StmtBlock bpe) tlstmt
    in
    let switch = aux patterns in
    mk_body dme (mk_seq sme switch)
  and translate_match (mexpr : expr) (patterns : reg_branch list)
                       (xn : exn_branch list)
                       (env : translation_env) : body =
    match patterns, xn with
    | _::_, [] ->
       translate_match_constructors mexpr patterns env;
    | [], _::_ ->
       translate_match_exceptions mexpr xn env;
    | _ -> unsupported "mixed patterns and exceptions in pattern matching"

  and translate_exception (_ : Ity.xsymbol) (_ : ty option) (value : expr)
                           (env : translation_env) : body =
    (* -> match *)
    debug "EEXN@.";
    translate_expression value env

  and translate_lambda (_ : var list) (_ : expr)
                       (_ : translation_env) : body =
    unsupported "lambda expressions"

  and translate_ignore (e : expr)
                       (env : translation_env) : body =
    let retstmt = if env.is_return then StmtReturn ExprNop else StmtNop in
    mk_body [] (mk_seq (StmtBlock (translate_expression e env)) retstmt)
  and translate_variable (e : expr) (pvs : Ity.pvsymbol)
(env : translation_env) : body =
    let varid = pvs.pv_vs.vs_name in
    let vartype = translate_type env.info e.e_mlty in
    let varexpr = match vartype with
    | ThisType when String.equal varid.id_string this_id -> ExprThis
    | _ ->
      begin
        match query_syntax env.info.syntax varid with
          None ->  ExprVar (varid, vartype)
        | Some s ->
           let p = Mid.find varid env.info.prec in
           ExprFromDrv (s, [], p)
      end
    in
    mk_body [] (expr_or_return varexpr env)

  and translate_expression (expr : expr) (env : translation_env) : body =
    match expr.e_node with
    | Econst _ ->
       debug "EConst@.";
       translate_constant expr env
    | Evar (pvs : Ity.pvsymbol) ->
       debug "EVar@.";
       translate_variable expr pvs env
    | Eapp ((rs : Expr.rsymbol), (args : expr list), (is_partial:bool)) ->
       debug "EApp@.";
       translate_app expr rs args is_partial env
    | Elet (Lvar(eb, ee),
            { e_node = Elet(Lvar (sb, se),
                 { e_node = Efor (i, ty, sb', dir, eb', body) })})
         when pv_equal sb sb' && pv_equal eb eb' ->
       (* pattern taken from C extraction *)
       debug "LETLETFOR@.";
       translate_for i ty se dir ee body env
    | Elet ((letdef : let_def), (inexpr : expr)) ->
       debug "ELet@.";
       translate_let letdef inexpr env
    | Eif (cond, thenexpr, elseexpr) ->
       debug "EIf@.";
       translate_if cond thenexpr elseexpr env
    | Eassign (assignlist : ( expr * ty * rsymbol * expr) list) ->
       debug "EAssign@.";
       translate_assign assignlist env
    | Ematch ((mexpr : expr), (patterns : reg_branch list),
              (xn : exn_branch list)) ->
       debug "EMatch@.";
       translate_match mexpr patterns xn env
    | Eblock (expr_list : expr list) ->
       debug "EBlock@.";
       translate_block expr_list env
    | Ewhile ((cond : expr), (body : expr)) ->
       debug "EWhile@.";
       translate_while cond body env
    | Efor ((it : Ity.pvsymbol), (it_type : ty), (firstval : Ity.pvsymbol),
            (dir : for_direction), (lastval : Ity.pvsymbol), (body : expr)) ->
       translate_pvsymb_for it it_type firstval dir lastval body env
    | Eraise ((e : Ity.xsymbol), (value : expr option)) ->
       debug "ERaise@.";
       translate_raise e value env
    | Eexn ((e : Ity.xsymbol), (etype : ty option), (value : expr)) ->
       translate_exception e etype value env
    | Efun ((vlist : var list), (body : expr)) ->
       debug "EFun@.";
       translate_lambda vlist body env
    | Eignore (e : expr) ->
       debug "EIgnore@.";
       translate_ignore e env
    | Eabsurd ->
       debug "EAbsurd@.";
       mk_body [] (StmtExpr ExprAbsurd)
  (*Loc.errorm "translation of Eabsurd (non-exhaustive pattern-matching ?)" *)

  and translate_expression_and_get_last_expr (expr : expr) (env : translation_env) : (definition list) * statement * expression =
    let d, s = translate_expression expr env in
    let s, e = get_last_expr s in
    d, s, e

  let translate_raised_exceptions (info : info) (rs: rsymbol) : xsymbol list =
    let aux xs =
      let _ = is_known_java_exception info xs in
      xs
    in
    List.map aux (Mxs.keys rs.rs_cty.cty_xpost)

  let translate_let_decl (info : info) (ldef : let_def)
      : JavaAST.definition list =
    let translate_method_proto ~(is_cstr:bool) rs stv restype varlist =
       let vlist, this_index =
         translate_function_arguments ~is_cstr:is_cstr info varlist stv in
       let visibility = get_visibility
                          ~default:(get_default_visibility ()) rs.rs_name in
       let jrestype = match restype with
         | Tvar _ ->
            Loc.warning warn_void_result  "return type of '%s' is set to void."
              rs.rs_name.id_string;
            VoidType
         | _ -> translate_type info restype in
       let exlist = translate_raised_exceptions info rs in
       (vlist, this_index, jrestype, visibility, exlist)
    in
    let translate_lrec (info : info) ({rec_sym = rs; rec_args = varlist; rec_exp = body;
    rec_res = restype; rec_svar = stv } : rdef) : JavaAST.definition =
      let rsid = rs.rs_name in
      if is_interface () then
        Loc.errorm ?loc:rsid.id_loc
       "concrete methods are not allowed in interface";
        begin
          debug "Lrec %s %d@." rsid.id_string (Stv.cardinal stv);
          let vlist, this_index, jrestype, visibility, exlist =
          translate_method_proto ~is_cstr:false rs stv restype varlist in
          add_method this_index rsid;
          let static = not (Option.is_some this_index) in
          let jbody = translate_body ~cstr:false info body in
          debug "method %s is_static=%B@." rsid.id_string static;
          DeclMethod (false, visibility, static, rsid, jrestype, vlist, exlist, jbody)
      end
        in
      match ldef with
    | Lvar (_, _) -> unsupported "let var"
    | Lsym (rs, _, _, _ , _) when  Sattr.mem java_ignore rs.rs_name.id_attrs -> []
    | Lsym (rs, stv, restype, varlist, body) when
           Sattr.mem java_constructor rs.rs_name.id_attrs ->
       let rsid = rs.rs_name in
       if is_interface () then
         Loc.errorm ?loc:rsid.id_loc
           "constructors are not allowed in interface";
       begin
         debug "JavaConstructor %s %d@." rsid.id_string (Stv.cardinal stv);
         let vlist, this_index, jrestype, visibility, exlist =
           translate_method_proto ~is_cstr:true rs stv restype varlist in
         match jrestype with
         | ThisType ->
            let jbody = translate_body ~cstr:true info body in
            assert (not (Option.is_some this_index));
            [ DeclConstructor (visibility, vlist, exlist, jbody) ]
         | _ -> unsupported "constructor with wrong return type"
       end

    | Lsym (rs, stv, restype, varlist, body) ->
       let rsid = rs.rs_name in
       if is_interface () then
         Loc.errorm ?loc:rsid.id_loc
           "concrete methods are not allowed in interface";
       begin
         debug "Lsym %s %d@." rsid.id_string (Stv.cardinal stv);
         let vlist, this_index, jrestype, visibility, exlist =
           translate_method_proto ~is_cstr:false rs stv restype varlist in
         let static = not (Option.is_some this_index) in
         let jbody = translate_body ~cstr:false info body in
         add_method this_index rsid;
         debug "method %s is_static=%B@." rsid.id_string static;
         [ DeclMethod (false, visibility, static, rsid, jrestype, vlist, exlist, jbody) ]
       end
    | Lany (rs, _, _ , _) when  Sattr.mem java_ignore rs.rs_name.id_attrs -> []
    | Lany (rs, stv, restype, varlist) ->
       let rsid = rs.rs_name in
       debug "Lany %s %d@." rsid.id_string (Stv.cardinal stv);
       let vlist, this_index, jrestype, visibility, exlist =
         translate_method_proto ~is_cstr:false rs stv restype varlist in
       if not (Option.is_some this_index) then
         Loc.errorm ?loc:rsid.id_loc
           "static abstract method (%s) is not allowed."
           rsid.id_string;
       add_method this_index rs.rs_name;
       [ DeclAbstractMethod (visibility, rs.rs_name, jrestype, vlist, exlist) ]
    | Lrec (rdefs) -> List.map (translate_lrec info) rdefs


  let translate_val_decl (_ : info) (_ : pvsymbol) (_ : ty) =
    [ DeclNotImplemented "Dval" ]

  let translate_exception_decl (info : info) (exc : xsymbol) (t : ty option) =
    try
       match translate_type info (Option.get t) with
       | ThisType -> set_exception exc; []
       | _ -> Loc.errorm ?loc:exc.xs_name.id_loc
                "The argument of exception '%s' must have type '%s'."
                exc.xs_name.id_string (get_this_type ()).id_string;
    with
    | ExceptionAlreadyDefined s ->
       Loc.errorm ?loc:exc.xs_name.id_loc
         "Exception has already been defined as '%s'." s
    | _ ->
       set_exception exc; []

  let translate_module_decl (_ : info) (_ : string) (_ : decl list) =
    [ DeclNotImplemented "nested modules" ]


  let translate_decl (info : info) (decl : Mltree.decl)
      : JavaAST.definition list =
    begin
      match decl with
      | Dtype [itsdefn] -> translate_type_decl info itsdefn
      | Dtype _ -> unsupported "multiple types declaration"
      | Dlet ldef -> translate_let_decl info ldef
      | Dval (pv, ty) -> translate_val_decl info pv ty
      | Dexn (xs, ty) -> translate_exception_decl info xs ty
      | Dmodule (s, dl) -> translate_module_decl info s dl
    end

end


module ExtractJava = struct
  open JavaCompilerInfo
  open JavaPrint

  (** Change a package `pkg` name into a path *)
  let package_name_to_path pkg = match pkg with
    | None -> ""
    | Some p ->
       let dirs = String.split_on_char '.' p in
       List.fold_left (fun a s -> a ^ s ^ "/") "" dirs

  let filename_for_class ?fname:_ m =
    let pkg = package_name_to_path (get_module_package_name m) in
    let n = m.mod_theory.th_name.id_string in
    let r = n (*match fname with
      | None -> n
      | Some f -> f ^ "__" ^ n*) in
    pkg ^ r ^ ".java"

  let class_header_printer : Pdriver.border_printer =

    fun _args ?old:_ ?fname fmt m ->
    init_compiler_info m;
    fprintf fmt "@[/* This file has been extracted from module %s. */@]@."
      (get_current_class_name ()).id_string;
    if Option.is_some fname then
      fprintf fmt "@[/* The module was located in file %s */@]@."
        (Option.get fname)

  let print_prelude _ ?old:_ ?fname:_ ~deps ~global_prelude ~prelude fmt m =
    let print_pkg_name fmt m =
      match get_module_package_name m with
      | None -> ()
      | Some p -> fprintf fmt "@[package %s;@]@\n@\n" p;
    in
    let print_deps fmt deps =
      let print_module_dep fmt (pm : Pmodule.pmodule) =
        import_module pm;
        let pm_name = pm.mod_theory.th_name in
        match get_module_package_name pm with
        | None -> (*fprintf fmt "@[import %s;@]" pm_name.id_string*)
           internal_error "import of a class with no package spec"
        | Some pkg -> fprintf fmt "@[import %s.%s;@]" pkg pm_name.id_string;
      in
      let deps = List.filter
                   (fun m -> Option.is_some (get_module_package_name m)) deps
      in
      pp_print_list ~pp_sep:newline print_module_dep fmt deps;
      if List.length deps > 0 then
        fprintf fmt "@\n@\n"
    in

    let default_visibility = get_default_visibility () in
    let visibility = get_visibility ~default:default_visibility
                       m.mod_theory.th_name in
    let cls = get_current_class () in
    let clsname = (get_current_class_name ()).id_string in
    debug "extract module %s@." clsname;

    fprintf fmt "%a%a%a%a@[%a%a%s%a%a {@\n@[<2>@\n"
      print_pkg_name m
      print_prelude global_prelude
      print_prelude prelude
      print_deps deps
      print_visibility visibility
      print_class_kind cls
      clsname
      print_exception_parent cls
      print_implements cls

  let print_decl =
    let memo = Hashtbl.create 16 in
    fun args ?old:_ ?fname:_ m fmt d ->
    if not (Hashtbl.mem memo d) then
      begin
        Hashtbl.add memo d ();
        let info = mk_info args m in
        let java_decl_list = MLW2Java.translate_decl info d in
        Ident.forget_all JavaPrint.local_names;
        let print_java_decl fmt jdecl =
          fprintf fmt "%a" (JavaPrint.print_definition info) jdecl in
        pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "@\n")
          print_java_decl fmt java_decl_list;
        fprintf fmt "@\n@\n";
      end

  let print_decl_flat _ ?old:_ ?fname:_ _ _ _ =
    unsupported "flat extraction"

  let class_footer_printer : Pdriver.border_printer =
    fun _args ?old:_ ?fname:_ fmt _ ->
    Format.fprintf fmt "@]@\n}@]@."

  let java_printer : Pdriver.printer = {
      desc = "printer for Java code";
      implem_printer = {
          filename_generator = filename_for_class;
          decl_printer = print_decl;
          prelude_printer = print_prelude;
          header_printer = class_header_printer;
          footer_printer = class_footer_printer;
        };

      flat_printer = {
          filename_generator = filename_for_class;
          decl_printer = print_decl_flat;
          prelude_printer = Pdriver.dummy_prelude_printer;
          header_printer = Pdriver.dummy_border_printer;
          footer_printer = Pdriver.dummy_border_printer;
        };
      interf_printer = None ;
    }

  let register_printer () =
    Pdriver.register_printer "java" java_printer
end

let () =
  ExtractJava.register_printer ()
