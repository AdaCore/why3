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

(**

{1 Inference of loop invariants for WhyML code, using bddinfer
   subcomponent}

TODO list:

- do not identify library symbols using string names. In other words,
   get rid of all `when` clause using `id_string`

*)

(* open Why3 *)
(* to comment out when inside Why3 *)


(* term printer *)

let rec ext_printer print_any fmt a =
  let open Term in
  let open Pretty in
  match a with
  | Pp_term (t, pri) ->
      begin match t.t_node with
        | Tapp (ls, [{t_node = Tvar v} as t]) when Term.ls_equal ls Pmodule.ls_ref_proj ->
          if Ident.Sattr.mem Pmodule.ref_attr v.vs_name.Ident.id_attrs
          then
            ext_printer print_any fmt (Pp_term(t,pri))
          else
            Format.fprintf fmt "!%a" (ext_printer print_any) (Pp_term(t,pri))
        | _ -> print_any fmt a
      end
  | _ -> print_any fmt a


module Pretty =
  (val (let sprinter,aprinter,tprinter,pprinter =
          let open Ident in
          let open Pretty in
    let same = fun x -> x in
    create_ident_printer why3_keywords ~sanitizer:same,
    create_ident_printer why3_keywords ~sanitizer:same,
    create_ident_printer why3_keywords ~sanitizer:same,
    create_ident_printer why3_keywords ~sanitizer:same
  in
  Pretty.create ~print_ext_any:ext_printer sprinter aprinter tprinter pprinter))


open Expr
open Ast
open Abstract

let verbose_level = ref 0 (* see .mli for details *)

exception Error of string * string

let translation_error fmt =
  Format.kasprintf
    (fun msg -> raise (Error("translation error",msg)))
    fmt

let unsupported fmt =
  Format.kasprintf
    (fun msg -> raise (Error("unsupported feature",msg)))
    fmt

let engine_error fmt =
  Format.kasprintf
    (fun msg -> raise (Error("engine error",msg)))
    fmt

type var_data = {
    why_var : Abstract.why_var;
    is_global : bool;
    is_mutable : bool;
    is_old_for : Term.vsymbol option;
  }



let type_of_ty ty =
  let open Ty in
  match ty.ty_node with
  | Tyapp(id,[]) when ts_equal id Ty.ts_int -> Tint
  | Tyapp(id,[]) when ts_equal id Ty.ts_bool -> Tbool
  | _ -> invalid_arg "type_of_ty"


let is_ty_int ty =
  let open Ty in
  match ty.ty_node with
  | Tyapp(id,[]) when ts_equal id Ty.ts_int -> true
  | _ -> false

let is_ty_option_int ty =
  match ty with
  | Some ty -> is_ty_int ty
  | None -> false

let is_ty_bool ty =
  let open Ty in
  match ty.ty_node with
  | Tyapp(id,[]) when ts_equal id Ty.ts_bool -> true
  | _ -> false

let is_ty_option_bool ty =
  match ty with
  | Some ty -> is_ty_bool ty
  | None -> false


          let is_type_int ity =
  let open Ity in
  match ity.ity_node with
  | Ityapp(id,[],[]) when its_equal id Ity.its_int -> true
  | _ -> false

let is_type_bool ity =
  let open Ity in
  match ity.ity_node with
  | Ityapp(id,[],[]) when its_equal id Ity.its_bool -> true
  | _ -> false

let is_type_unit ity =
  let open Ity in
  match ity.ity_node with
  | Ityapp(id,[],[]) when its_equal id Ity.its_unit -> true
  | _ -> false

let rec type_of ity =
  let open Ity in
  match ity.ity_node with
  | Ityapp(id,[],[]) when its_equal id Ity.its_unit -> (false,Tunit)
  | Ityapp(id,[],[]) when its_equal id Ity.its_int -> (false,Tint)
  | Ityapp(id,[],[]) when its_equal id Ity.its_bool -> (false,Tbool)
  | Ityapp(id,[t1],[]) when id.Ity.its_ts.Ty.ts_name.Ident.id_string = "ref"->
     let _, ty = type_of t1 in (true,ty)
  | Ityapp(id,l1,l2) ->
     unsupported "@[type_of:@ @[`Ityapp(%a,@[[%a]@],@[[%a]@])`@]@]"
       Pretty.print_ts id.Ity.its_ts
       Pp.(print_list semi Ity.print_ity) l1
       Pp.(print_list semi Ity.print_ity) l2
  | Ityreg { reg_its; reg_args = [ty]; _ } when
         reg_its.its_ts.Ty.ts_name.Ident.id_string = "ref" && is_type_int ty ->
     (true,Tint)
  | Ityreg { reg_its; reg_args = [ty]; _ } when
         reg_its.its_ts.Ty.ts_name.Ident.id_string = "ref" && is_type_bool ty ->
     (true,Tbool)
  | Ityreg _r ->
     unsupported "@[type_of:@ region type @[`%a`@]@]" Ity.print_ity ity
  | Ityvar _ ->
     unsupported "@[type_of:@ type variable @[`%a`@]@]" Ity.print_ity ity


let print_vs fmt vs =
  Format.fprintf fmt "%a@@%d" Pretty.print_vs vs
    (Weakhtbl.tag_hash vs.Term.vs_name.Ident.id_tag)

let print_pv fmt pv =
  Format.fprintf fmt "pv@@%a" print_vs pv.Ity.pv_vs

(* not used anymore for the moment
let print_pvty fmt pv =
  Format.fprintf fmt "pv@@%a : %a" print_vs pv.Ity.pv_vs
  Ity.print_ity_full pv.Ity.pv_ity
 *)

type context = {
  known : Decl.known_map;
  env  : var_data Term.Mvs.t;
}

let declare_why_var_for_vs ctx ~is_global ~is_mutable ?is_old_for ?(is_result=false) vs =
  let open Term in
  try
    (* Format.eprintf "vs_table: querying %s@." vs.Term.vs_name.id_string; *)
    let _ = Term.Mvs.find vs ctx.env in
    translation_error "variable %a already declared@." print_vs vs
  with Not_found ->
    let n = if is_result then "result" else vs.Term.vs_name.Ident.id_string in
    (* Format.eprintf "declare_why_var: adding %a -> %s@." print_vs vs n; *)
    let why_var = create_var n in
    let env = Mvs.add vs { why_var; is_global; is_mutable ; is_old_for } ctx.env in
    let ctx = { ctx with env } in
    ctx, why_var

let declare_why_var_for_pv ctx ~is_global ~is_mutable ?is_old_for pv =
  declare_why_var_for_vs ctx ~is_global ~is_mutable ?is_old_for pv.Ity.pv_vs

let get_or_declare_why_var_for_pv ctx pv =
  let vs = pv.Ity.pv_vs in
  try
    let d = Term.Mvs.find vs ctx.env in
    ctx, d.why_var
  with Not_found ->
    let (is_mutable,_) = type_of pv.Ity.pv_ity in
    (* Format.eprintf "Declaring global variable for %a@." print_vs vs; *)
    declare_why_var_for_vs ctx ~is_global:true ~is_mutable vs

let mlw_vs_to_why1_expr ctx vs =
  try
    let d = Term.Mvs.find vs ctx.env in
    match d.is_old_for with
    | None -> ctx, e_var d.why_var Here
    | Some vs ->
       let d = Term.Mvs.find vs ctx.env in
       ctx, e_var d.why_var Old
  with Not_found ->
    (* it may happen that a global variable is first seen in an assertion *)
    let ctx,v = declare_why_var_for_vs ctx ~is_global:true ~is_mutable:true vs in
    ctx, e_var v Here

let rs_table = ref Expr.Mrs.empty

let get_or_declare_function rs : Ast.fun_id =
  try
    Expr.Mrs.find rs !rs_table
  with Not_found ->
    let n = create_fun_id rs.rs_name.Ident.id_string in
    (* Format.eprintf "rs_table: adding %s -> %s@." rs.rs_name.id_string n; *)
    rs_table := Mrs.add rs n !rs_table;
    n



let rec normalized_term_to_why1_expr ctx t =
  let open Term in
  let ctx, t' =
  match t.t_node with
  | Ttrue -> ctx, e_bwtrue
  | Tfalse -> ctx, e_bwfalse
  | Tvar vs -> mlw_vs_to_why1_expr ctx vs
  | Tconst (Constant.ConstInt c) -> ctx, e_cst (BigInt.to_string c.Number.il_int)
  | Tconst (Constant.ConstReal _) (* Constant.constant *) ->
     unsupported "normalized_term_to_why1_expr: real literals"
  | Tconst (Constant.ConstStr _) (* Constant.constant *) ->
     unsupported "normalized_term_to_why1_expr: string literals"
  | Tapp(ls, []) when ls.ls_name.Ident.id_string = "True" ->
     ctx, e_bwtrue
  | Tapp(ls, []) when ls.ls_name.Ident.id_string = "False" ->
     ctx, e_bwfalse
  | Tapp(ls, [t]) when ls.ls_name.Ident.id_string = "contents" ->
    let ctx, e = normalized_term_to_why1_expr ctx t in
     ctx, e
  | Tapp(ls, [t]) when ls.ls_name.Ident.id_string = "prefix !" ->
     let ctx, e = normalized_term_to_why1_expr ctx t in
     ctx, e
  | Tapp(ls, [t1;t2]) when ls.ls_name.Ident.id_string = "infix +" ->
     let ctx, e1 = normalized_term_to_why1_expr ctx t1 in
     let ctx, e2 = normalized_term_to_why1_expr ctx t2 in
     ctx, e_add e1 e2
  | Tapp(ls, [t1;t2]) when ls.ls_name.Ident.id_string = "infix -" ->
     let ctx, e1 = normalized_term_to_why1_expr ctx t1 in
     let ctx, e2 = normalized_term_to_why1_expr ctx t2 in
     ctx, e_sub e1 e2
  | Tapp(ls, [t1]) when ls.ls_name.Ident.id_string = "prefix -" ->
     let ctx, e1 = normalized_term_to_why1_expr ctx t1 in
     ctx, e_sub (e_cst "0") e1
  | Tapp(ls, [t1;t2]) when ls.ls_name.Ident.id_string = "infix *" ->
     let ctx, e1 = normalized_term_to_why1_expr ctx t1 in
     let ctx, e2 = normalized_term_to_why1_expr ctx t2 in
     ctx, e_mul e1 e2
  | Tapp(ls, [t1;t2]) when ls.ls_name.Ident.id_string = "div" ->
     let ctx, e1 = normalized_term_to_why1_expr ctx t1 in
     let ctx, e2 = normalized_term_to_why1_expr ctx t2 in
     ctx, e_div e1 e2
  | Tapp(ls, [t1;t2]) when ls.ls_name.Ident.id_string = "mod" ->
     let ctx, e1 = normalized_term_to_why1_expr ctx t1 in
     let ctx, e2 = normalized_term_to_why1_expr ctx t2 in
     ctx, e_mod e1 e2
  | Tapp(ls, [t1;t2]) when ls.ls_name.Ident.id_string = "andb" ->
     let ctx, e1 = normalized_term_to_why1_expr ctx t1 in
     let ctx, e2 = normalized_term_to_why1_expr ctx t2 in
     ctx, bwand_simp e1 e2
  | Tapp(ls, [t1;t2]) when ls.ls_name.Ident.id_string = "orb" ->
     let ctx, e1 = normalized_term_to_why1_expr ctx t1 in
     let ctx, e2 = normalized_term_to_why1_expr ctx t2 in
     ctx, bwor_simp e1 e2
  | Tapp(ls, [t1]) when ls.ls_name.Ident.id_string = "notb" ->
     let ctx, e1 = normalized_term_to_why1_expr ctx t1 in
     ctx, bwnot_simp e1
  | Tapp(ls,args) ->
    begin
      match Decl.find_logic_definition ctx.known ls with
      | Some ls_def ->
        let vl,body = Decl.open_ls_defn ls_def in
        let subst = List.fold_left2
            (fun acc vs t -> Mvs.add vs t acc)
            Mvs.empty vl args
        in
        let t = Term.t_subst subst body in
        normalized_term_to_why1_expr ctx t
      | None ->
        unsupported "normalized_term_to_why1_expr: application of logic function `%a` without concrete definition" Pretty.print_ls ls
    end
  | Tif _ (* term * term * term *)
  | Tlet _ (* term * term_bound *)
  | Tcase _ (* term * term_branch list *)
  | Teps _ (* term_bound *)
  | Tquant _ (* quant * term_quant *)
  | Tbinop _ (* binop * term * term *)
  | Tnot _ (* term *) ->
     unsupported "normalized_term_to_why1_expr: term `%a`" Pretty.print_term t
  in ctx, t'

let p_atomic_operator ctx op t1 t2 =
  let ctx, t1 = normalized_term_to_why1_expr ctx t1 in
  let ctx, t2 = normalized_term_to_why1_expr ctx t2 in
  ctx,
  atomic_cond (op t1 t2)

let rec normalized_fmla_to_why1_cond ctx t =
  let open Term in
  let ctx, t' =
  match t.t_node with
  | Tvar vs ->
     unsupported "normalized_fmla_to_why1_cond: variable `%a`" print_vs vs
  | Tconst _ ->
     unsupported "normalized_fmla_to_why1_cond: constant `%a`" Pretty.print_term t
  | Tapp(ls,[t1;t2]) when ls_equal ls ps_equ ->
     let ty = t1.t_ty in
     let op t1 t2 =
       if is_ty_option_int ty then c_eq_int t1 t2 else
         if is_ty_option_bool ty then c_eq_bool t1 t2 else
           unsupported "normalized_fmla_to_why1_cond: equality on type `%a` other than int or bool"
             (Pp.print_option Pretty.print_ty) ty
     in
     p_atomic_operator ctx op t1 t2
  | Tapp(ls, [t1; t2]) when ls.ls_name.Ident.id_string = "infix >=" ->
     p_atomic_operator ctx c_ge t1 t2
  | Tapp(ls, [t1; t2]) when ls.ls_name.Ident.id_string = "infix >" ->
     p_atomic_operator ctx c_gt t1 t2
  | Tapp(ls, [t1; t2]) when ls.ls_name.Ident.id_string = "infix <=" ->
     p_atomic_operator ctx c_le t1 t2
  | Tapp(ls, [t1; t2]) when ls.ls_name.Ident.id_string = "infix <" ->
     p_atomic_operator ctx c_lt t1 t2
  | Tapp(ls,_args) ->
     unsupported "normalized_fmla_to_why1_cond: application of logic function `%a`" Pretty.print_ls ls
  | Tbinop(Tand,t1,t2) ->
     let ctx, t1 = normalized_fmla_to_why1_cond ctx t1 in
     let ctx, t2 = normalized_fmla_to_why1_cond ctx t2 in
     ctx, and_cond t1 t2
  | Tbinop(Tor,t1,t2) ->
     let ctx, t1 = normalized_fmla_to_why1_cond ctx t1 in
     let ctx, t2 = normalized_fmla_to_why1_cond ctx t2 in
     ctx, or_cond t1 t2
  | Tbinop(Timplies,t1,t2) ->
     let ctx, t1 = normalized_fmla_to_why1_cond ctx t1 in
     let ctx, t2 = normalized_fmla_to_why1_cond ctx t2 in
     ctx, or_cond (neg_cond t1) t2
  | Tbinop(Tiff,t1,t2) ->
     let ctx, t1 = normalized_fmla_to_why1_cond ctx t1 in
     let ctx, t2 = normalized_fmla_to_why1_cond ctx t2 in
     ctx, or_cond (and_cond t1 t2) (and_cond (neg_cond t1) (neg_cond t2))
  | Tnot c ->
      let ctx, tc = normalized_fmla_to_why1_cond ctx c in
      ctx, neg_cond tc
  | Ttrue -> ctx, true_cond
  | Tfalse -> ctx, false_cond
  | Tif(t1,t2,t3) ->
     begin
       try (* if is_ty_option_bool t2.t_ty && is_ty_option_bool t3.t_ty then *)
         let ctx, t1 = normalized_fmla_to_why1_cond ctx t1 in
         let ctx, t2 = normalized_fmla_to_why1_cond ctx t2 in
         let ctx, t3 = normalized_fmla_to_why1_cond ctx t3 in
         ctx, ternary_condition t1 t2 t3
       with _ -> (*  else *)
         unsupported "normalized_fmla_to_why1_cond: if expression on type `%a`"
           Pp.(print_option Pretty.print_ty) t2.t_ty
     end
  | Tlet _ (* term * term_bound *)
  | Tcase _ (* term * term_branch list *)
  | Teps _ (* term_bound *)
  | Tquant _ (* quant * term_quant *)
      -> unsupported "normalized_fmla_to_why1_cond: term `%a`" Pretty.print_term t
  in ctx, t'


let is_t_true t =
  let open Term in
  match t.t_node with
  | Tapp(ls, []) -> ls.ls_name.Ident.id_string = "True"
  | _ -> false

let is_t_false t =
  let open Term in
  match t.t_node with
  | Tapp(ls, []) -> ls.ls_name.Ident.id_string = "False"
  | _ -> false

let mk_if t = Term.(t_if t t_bool_true t_bool_false)

let rec normalize_term t =
  let open Term in
  match t.t_node with
  | Tapp(ls,[t1;t2]) when ls.ls_name.Ident.id_string = "orb" ->
    let t1 = normalize_term t1 in
    let t2 = normalize_term t2 in
    begin
      match t1.t_node, t2.t_node with
      | Tif(c1,t11,t12), Tif(c2,t21,t22)
        when is_t_true t11 && is_t_false t12 && is_t_true t21 && is_t_false t22 ->
        mk_if (t_or c1 c2)
      | Tif(c1,t11,t12), _
        when is_t_true t11 && is_t_false t12 ->
        mk_if (t_or c1 (t_equ t2 t11))
      | _, Tif(c2,t21,t22)
        when is_t_true t21 && is_t_false t22 ->
        mk_if (t_or (t_equ t1 t21) c2)
      | _ -> t_app ls [t1;t2] t.t_ty
    end
  | Tapp(ls,[t1;t2]) when ls.ls_name.Ident.id_string = "andb" ->
    let t1 = normalize_term t1 in
    let t2 = normalize_term t2 in
    begin
      match t1.t_node, t2.t_node with
      | Tif(c1,t11,t12), Tif(c2,t21,t22)
        when is_t_true t11 && is_t_false t12 && is_t_true t21 && is_t_false t22 ->
        mk_if (t_and c1 c2)
      | Tif(c1,t11,t12), _
        when is_t_true t11 && is_t_false t12 ->
        mk_if (t_and c1 (t_equ t2 t11))
      | _, Tif(c2,t21,t22)
        when is_t_true t21 && is_t_false t22 ->
        mk_if (t_and (t_equ t1 t21) c2)
      | _ -> t_app ls [t1;t2] t.t_ty
    end
  | Tapp(ls,[t1]) when ls.ls_name.Ident.id_string = "notb" ->
    let t1 = normalize_term t1 in
    begin
      match t1.t_node with
      | Tif(c1,t11,t12)
        when is_t_true t11 && is_t_false t12 ->
        mk_if (t_not c1)
      | _ -> t_app ls [t1] t.t_ty
    end
  | _ -> TermTF.t_map normalize_term normalize_fmla t


and normalize_fmla t =
  let open Term in
  match t.t_node with
  | Tapp(ls,[t1;t2]) when ls_equal ls ps_equ && is_t_true t2 ->
    let t1 = normalize_term t1 in
    begin
      match t1.t_node with
      | Tif(c,t3,t4) when is_t_true t3 && is_t_false t4 ->
        c
      | _ -> t_equ t1 t2
    end
  | _ -> TermTF.t_map normalize_term normalize_fmla t



let mlw_fmla_to_why1_cond ctx t =
  let nt = normalize_fmla t in
(*
  Format.printf "@[mlw_fmla_to_why1_cond:@ `@[%a@]` ->@ `@[%a@]`@."
    Pretty.print_term t Pretty.print_term nt;
*)
  normalized_fmla_to_why1_cond ctx nt





let mlw_pv_to_why1_expr ctx pv =
  let ctx, n = get_or_declare_why_var_for_pv ctx pv in
  ctx, e_var n Here

let p_expr_operator ctx op pv1 pv2 =
  let ctx, v1 = mlw_pv_to_why1_expr ctx pv1 in
  let ctx, v2 = mlw_pv_to_why1_expr ctx pv2 in
  ctx, op v1 v2

exception NotExpression

type simple_expr_node =
  | SEvar of Ity.pvsymbol
  | SEconst of Constant.constant
  | SEexec of Expr.cexp * Ity.cty
  | SEassign of Expr.assign list
  | SEseq of simple_expr * simple_expr
  | SElet of Ity.pvsymbol * simple_expr * simple_expr
  | SEif of simple_expr * simple_expr * simple_expr
  | SEwhile of simple_expr * Expr.invariant list * Expr.variant list * simple_expr
  | SEassert of assertion_kind * Term.term
  | SEbreak

and simple_expr =
  { simple_expr_tag : string;
    simple_expr_node : simple_expr_node;
  }

let rec print_simple_expr fmt e =
  let open Format in
  let open Expr in
  match e.simple_expr_node with
  | SEvar pv -> fprintf fmt "%a" Ity.print_pv pv
  | SEconst c -> fprintf fmt "%a" Constant.print_def c
  | SEexec(cexp,_cty) -> fprintf fmt "@[exec %a@]" (print_cexp true 0) cexp
  | SEassign l ->
    fprintf fmt "@[%a@]"
      (Pp.print_list Pp.comma (fun fmt (pv1,_,pv2) ->
          fprintf fmt "%a <- %a" Ity.print_pv pv1 Ity.print_pv pv2)) l
  | SEseq(e1,e2) ->
    fprintf fmt "@[%a ;@ %a@]" print_simple_expr e1 print_simple_expr e2
  | SElet(pv,e1,e2) ->
    fprintf fmt "@[let %a = %a in@ %a@]" Ity.print_pv pv print_simple_expr e1 print_simple_expr e2
  | SEif(e1,e2,e3) ->
    fprintf fmt "@[<hv 2>if @[%a@]@ then @[%a@]@ else @[%a@]@ endif@]" print_simple_expr e1 print_simple_expr e2 print_simple_expr e3
  | SEwhile(c,_invs,_vars,b) ->
    fprintf fmt "@[while %a <invs> <vars> do@ %a@ done@]" print_simple_expr c print_simple_expr b
  | SEassert(Assert,t) ->
    fprintf fmt "@[assert %a@]" Pretty.print_term t
  | SEassert(Assume,t) ->
    fprintf fmt "@[assume %a@]" Pretty.print_term t
  | SEassert(Check,t) ->
    fprintf fmt "@[check %a@]" Pretty.print_term t
  | SEbreak ->
    fprintf fmt "break;"


let rec simple_expr_to_why1_expr ctx e =
  let ctx, e' =
  match e.simple_expr_node with
  | SEvar pv -> mlw_pv_to_why1_expr ctx pv
  | SEconst (Constant.ConstInt c) -> ctx, e_cst (BigInt.to_string c.Number.il_int)
  | SEconst (Constant.ConstReal _) (* Constant.constant *) ->
     unsupported "simple_expr_to_why1_expr: real literals"
  | SEconst (Constant.ConstStr _) (* Constant.constant *) ->
     unsupported "simple_expr_to_why1_expr: string literals"
  | SEexec(cexp,_cty) ->
     begin match cexp.c_node with
     (* FIXME do not match on rs names *)
     | Capp(rs, [pv]) when rs.rs_name.Ident.id_string = "ref" ->
        mlw_pv_to_why1_expr ctx pv
     | Capp(rs, [pv]) when rs.rs_name.Ident.id_string = "contents" ->
        mlw_pv_to_why1_expr ctx pv
     | Capp(rs, [pv]) when rs.rs_name.Ident.id_string = "prefix !" ->
        mlw_pv_to_why1_expr ctx pv
     | Capp(rs, [pv1;pv2]) when rs.rs_name.Ident.id_string = "infix +" ->
        p_expr_operator ctx e_add pv1 pv2
     | Capp(rs, [pv1;pv2]) when rs.rs_name.Ident.id_string = "infix -" ->
        p_expr_operator ctx e_sub pv1 pv2
     | Capp(rs, [pv1;pv2]) when rs.rs_name.Ident.id_string = "infix *" ->
        p_expr_operator ctx e_mul pv1 pv2
     | Capp(rs, [pv1;pv2]) when rs.rs_name.Ident.id_string = "infix /" ->
        p_expr_operator ctx e_div pv1 pv2
     | Capp(rs, [pv1;pv2]) when rs.rs_name.Ident.id_string = "andb" ->
        p_expr_operator ctx bwand_simp pv1 pv2
     | Capp(rs, [pv1;pv2]) when rs.rs_name.Ident.id_string = "orb" ->
        p_expr_operator ctx bwor_simp pv1 pv2
     | Capp(rs, [pv]) when rs.rs_name.Ident.id_string = "notb" ->
        let ctx, v = mlw_pv_to_why1_expr ctx pv in
        ctx, bwnot_simp v
     | Capp(rs, []) when rs.rs_name.Ident.id_string = "True" ->
        ctx, e_bwtrue
     | Capp(rs, []) when rs.rs_name.Ident.id_string = "False" ->
        ctx, e_bwfalse
     | Capp(rs, [_; _]) when rs.rs_name.Ident.id_string = "infix =" ->
        raise NotExpression
     | Capp(rs, [_; _]) when rs.rs_name.Ident.id_string = "infix <=" ->
        raise NotExpression
     | Capp(rs, [_; _]) when rs.rs_name.Ident.id_string = "infix <" ->
        raise NotExpression
     | Capp(rs, [_; _]) when rs.rs_name.Ident.id_string = "infix >=" ->
        raise NotExpression
     | Capp(rs, [_; _]) when rs.rs_name.Ident.id_string = "infix >" ->
        raise NotExpression
     | Capp(rs,_args) ->
        unsupported "simple_expr_to_why1_expr: execution of call to function `%a`" Expr.print_rs rs
     | Cpur(ls,_l) ->
        unsupported "simple_expr_to_why1_expr: execution of call to pure function `%a`" Pretty.print_ls ls
     | Cfun e ->
        unsupported "simple_expr_to_why1_expr: execution of call to expression `%a`" Expr.print_expr e
     | Cany ->
        unsupported "simple_expr_to_why1_expr: execution of call to `any`"
     end
  | SEassign _ (* assign list *) ->
     unsupported "simple_expr_to_why1_expr: assignments"
  | SElet(x,{simple_expr_node = SElet(y,e1,e2); _},e3) ->
    (* we interpret
       let x = (let y = e1 in e2) in e3
       as
       let y = e1 in let x = e2 in e3
    *)
    simple_expr_to_why1_expr ctx
      { simple_expr_tag = "";
        simple_expr_node =
          SElet(y,e1,{ simple_expr_tag = "";
                       simple_expr_node =
                         SElet(x,e2,e3)})}
  | SElet(pv,e1,e2) ->
     if is_type_int pv.Ity.pv_ity || is_type_bool pv.Ity.pv_ity then
       let ctx, n = declare_why_var_for_pv ctx ~is_global:false ~is_mutable:false pv in
        let ctx, e1 = simple_expr_to_why1_expr ctx e1 in
        let ctx, e2 = simple_expr_to_why1_expr ctx e2 in
        ctx, e_let_in_expression n e1 e2
     else
       unsupported
         "simple_expr_to_why1_expr: let on variable `%a` of type `%a`"
         print_vs pv.Ity.pv_vs Ity.print_ity pv.Ity.pv_ity
  | SEif(e1,e2,e3) ->
(*
if is_type_bool e2.e_ity && is_type_bool e3.e_ity then
*)
    let ctx, e1 = simple_expr_to_why1_expr ctx e1 in
    let ctx, e2 = simple_expr_to_why1_expr ctx e2 in
    let ctx, e3 = simple_expr_to_why1_expr ctx e3 in
    (* `if e1 then e2 else e3` is equivalent to
           `(e1 /\ e2) \/ (not e1 /\ e3)` *)
    let c =
      bwor_simp
        (bwand_simp e1 e2)
        (bwand_simp (bwnot_simp e1) e3)
    in ctx, c
(*
else
      unsupported
        "simple_expr_to_why1_expr: if statement on type `%a`"
        Ity.print_ity e1.e_ity
*)
  | SEwhile  _ (* expr * invariant list * variant list * expr *) ->
      unsupported "simple_expr_to_why1_expr: SEwhile"
  | SEassert _ (* assertion_kind * term *) ->
      unsupported "simple_expr_to_why1_expr: SEassert"
  | SEbreak ->
      unsupported "simple_expr_to_why1_expr: SEbreak"
  | SEseq(e1,e2) ->
    (* raise NotExpression *)
    unsupported "simple_expr_to_why1_expr: SEseq(%a,%a)"
      print_simple_expr e1 print_simple_expr e2
  in ctx, e'

let p_expr_bool_operator ctx op pv1 pv2 =
  let ctx, v1 = mlw_pv_to_why1_expr ctx pv1 in
  let ctx, v2 = mlw_pv_to_why1_expr ctx pv2 in
  ctx, atomic_cond (op v1 v2)

let rec simple_expr_to_why1_cond ctx e =
  let ctx, c' =
    try
      (*      if is_type_bool e.e_ity then *)
      let ctx, t = simple_expr_to_why1_expr ctx e in
      ctx, atomic_cond (c_is_true t)
    (*      else raise NotExpression *)
    with NotExpression ->
    match e.simple_expr_node with
    | SEvar _pv ->
      unsupported "simple_expr_to_why1_cond: Evar"
    | SEconst _ ->
      unsupported "simple_expr_to_why1_cond: Econst"
    | SEexec(cexp,_cty) ->
     begin match cexp.c_node with
     (* FIXME do not match on rs names *)
     | Capp(rs,[pv1;pv2]) when rs.rs_name.Ident.id_string = "infix =" ->
        begin
          match type_of pv1.Ity.pv_ity with
          | _,Tunit ->
            unsupported "simple_expr_to_why1_cond: equality on type unit"
          | _,Tint -> p_expr_bool_operator ctx c_eq_int pv1 pv2
          | _,Tbool -> p_expr_bool_operator ctx c_eq_bool pv1 pv2
        end
     | Capp(rs, [pv1;pv2]) when rs.rs_name.Ident.id_string = "infix <=" ->
        p_expr_bool_operator ctx c_le pv1 pv2
     | Capp(rs, [pv1;pv2]) when rs.rs_name.Ident.id_string = "infix <" ->
        p_expr_bool_operator ctx c_lt pv1 pv2
     | Capp(rs, [pv1;pv2]) when rs.rs_name.Ident.id_string = "infix >=" ->
        p_expr_bool_operator ctx c_ge pv1 pv2
     | Capp(rs, [pv1;pv2]) when rs.rs_name.Ident.id_string = "infix >" ->
        p_expr_bool_operator ctx c_gt pv1 pv2
     | Capp(rs, []) when rs.rs_name.Ident.id_string = "True" ->
        ctx, true_cond
     | Capp(rs, []) when rs.rs_name.Ident.id_string = "False" ->
        ctx, false_cond
     | Capp(rs,_args) ->
        unsupported "simple_expr_to_why1_cond: execution of function `%a`" Expr.print_rs rs
     | Cpur(ls,_l) (* lsymbol * pvsymbol list *) ->
        unsupported "simple_expr_to_why1_cond: execution of pure function `%a`" Pretty.print_ls ls
     | Cfun e (* expr *) ->
        unsupported "simple_expr_to_why1_cond: execution of expression `Cfun %a`" Expr.print_expr e
     | Cany ->
        unsupported "simple_expr_to_why1_cond: execution of `any`"
     end
  | SEassign _ (* assign list *) ->
     unsupported "simple_expr_to_why1_cond: assignments"
  | SElet(x,{simple_expr_node = SElet(y,e1,e2); _},e3) ->
    (* we interpret
       let x = (let y = e1 in e2) in e3
       as
       let y = e1 in let x = e2 in e3
    *)
    simple_expr_to_why1_cond ctx
      { simple_expr_tag = "";
        simple_expr_node =
          SElet(y,e1,{ simple_expr_tag = "";
                       simple_expr_node =
                         SElet(x,e2,e3)})}
  | SElet(pv,e1,e2) ->
    (*     if is_type_int pv.Ity.pv_ity || is_type_bool pv.Ity.pv_ity then *)
       let ctx, n = declare_why_var_for_pv ctx ~is_global:false ~is_mutable:false pv in
       let ctx, e = simple_expr_to_why1_expr ctx e1 in
       let ctx, c = simple_expr_to_why1_cond ctx e2 in
       ctx, e_let_in_condition n e c
(*
     else
       unsupported "simple_expr_to_why1_cond: local let on type `%a`" Ity.print_ity pv.Ity.pv_ity
*)
  | SEif(e1,e2,e3) ->
     (*     if is_type_bool e2.e_ity && is_type_bool e3.e_ity then *)
     let ctx, e1 = simple_expr_to_why1_cond ctx e1 in
          let ctx, e2 = simple_expr_to_why1_cond ctx e2 in
          let ctx, e3 = simple_expr_to_why1_cond ctx e3 in
          ctx, ternary_condition e1 e2 e3
(*      else
        unsupported "simple_expr_to_why1_cond: if expression on type `%a`"
          Ity.print_ity e2.e_ity *)
  | SEwhile  _ (* expr * invariant list * variant list * expr *) ->
     unsupported "simple_expr_to_why1_cond: SEwhile"
  | SEassert _ (* assertion_kind * term *) ->
     unsupported "simple_expr_to_why1_cond: SEassert"
  | SEbreak ->
     unsupported "simple_expr_to_why1_cond: SEbreak"
  | SEseq(_e1,e2) ->
    (* workaround for the time we don't support the unit type as a value
          useful for the shape `let o = () in f o`
    *)
    simple_expr_to_why1_cond ctx e2
  in ctx, c'



let mk_instr tag i = { simple_expr_tag = tag ; simple_expr_node = i }

exception NotAFunctionCall

let rec simple_expr_to_function_call acc ctx i
  =
  match i.simple_expr_node with
  | SEexec(cexp,_cty) ->
     begin match cexp.c_node with
     (* FIXME do not match on rs names *)
     | Capp(_rs, []) -> raise NotAFunctionCall
     | Capp(rs, _) when List.mem rs.rs_name.Ident.id_string
                          [ "ref"; "infix +" ; "infix -" ; "infix *" ;
                            "infix <"; "infix >" ; "infix <=" ; "infix >=" ;
                            "contents" ; Ident.op_prefix "!";
                            "andb" ; "orb" ; "notb" ]
       ->
        raise NotAFunctionCall
     | Capp(rs,args) ->
        let args =
          match args with
          | [pv] when is_type_unit pv.Ity.pv_ity ->
             (* call to `f ()` should be seen as a call to an empty
                list of arguments *)
             []
          | _ -> args
        in
        ctx, rs, acc, args
     | Cpur _ (* lsymbol * pvsymbol list *) ->
        unsupported "mlw_expr_to_function_call: Cpur"
     | Cfun _ (* expr *) ->
        unsupported "mlw_expr_to_function_call: Cfun"
     | Cany ->
        unsupported "mlw_expr_to_function_call: Cany"
     end
  | SEseq(_,e2) ->
    (* workaround for the time we don't support the unit type as a value
          useful for the shape `let o = () in f o`
    *)
    simple_expr_to_function_call acc ctx e2
  | SElet(pv,e1,e2) ->
       simple_expr_to_function_call ((pv,e1)::acc) ctx e2
  | _ -> raise NotAFunctionCall



let rec simple_expr_to_why1_stmt ctx vars i =
  let tag = i.simple_expr_tag in
  match i.simple_expr_node with
  | SEvar _ ->
    unsupported "simple_expr_to_why1_stmt: SEvar"
  | SEconst _ ->
    unsupported "simple_expr_to_why1_stmt: SEconst"
  | SEexec(cexp,_cty) ->
     begin match cexp.c_node with
     (* FIXME do not match on rs names *)
     | Capp(rs,[]) when rs.rs_name.Ident.id_string = "Tuple0" ->
        ctx, vars, s_block tag []
     | Capp(rs,[]) ->
        unsupported
          "simple_expr_to_why1_stmt: execution of nullary function `%a`" Expr.print_rs rs
     | Capp(rs, [_pv]) when rs.rs_name.Ident.id_string = "prefix !" ->
        (* FIXME: we assume it is the returned value, we just ignore it *)
        ctx, vars, s_block tag []
     | Capp(rs, [_pv]) when rs.rs_name.Ident.id_string = "contents" ->
        (* FIXME: we assume it is the returned value, we just ignore it *)
        ctx, vars, s_block tag []
     | Capp(rs, [pv1;pv2]) when rs.rs_name.Ident.id_string = "infix :=" ->
        let is_ref,ty = type_of pv1.Ity.pv_ity in
        assert is_ref;
        let ctx, x = get_or_declare_why_var_for_pv ctx pv1 in
        let ctx, v2 = mlw_pv_to_why1_expr ctx pv2 in
        ctx, Ity.Spv.(add pv1 (add pv2 vars)), s_assign tag ty x v2
     | Capp(rs,args) ->
        let name = get_or_declare_function rs in
        let ctx,args =
          match args with
          | [pv] when is_type_unit pv.Ity.pv_ity -> ctx,[]
          | _ ->
             List.fold_right
               (fun pv (ctx, args) ->
                 let ctx, v = mlw_pv_to_why1_expr ctx pv in
                 ctx, v :: args)
               args (ctx, [])
        in
        ctx, vars, s_call tag None [] name args
     | Cpur _ (* lsymbol * pvsymbol list *) ->
        unsupported "simple_expr_to_why1_stmt: Cpur"
     | Cfun _ (* expr *) ->
        unsupported "simple_expr_to_why1_stmt: Cfun"
     | Cany ->
        unsupported "simple_expr_to_why1_stmt: Cany"
     end
  | SEassign [(var,_f,value)] ->
     (* TODO: check that var as type ref int or ref bool, and that f is "contents" *)
     let is_ref,ty = type_of var.Ity.pv_ity in
     assert is_ref;
     let ctx, n = get_or_declare_why_var_for_pv ctx var in
     let ctx, value' = mlw_pv_to_why1_expr ctx value in
     ctx, Ity.Spv.(add var (add value vars)), s_assign tag ty n value'
  | SEassign _ (* assign list *) ->
    unsupported "simple_expr_to_why1_stmt: SEassign (parallel)"
  | SEseq(i1,i2) ->
    let ctx, vars, s1 = simple_expr_to_why1_stmt ctx vars i1 in
    let ctx, vars, s2 = simple_expr_to_why1_stmt ctx vars i2 in
    let s = s_sequence tag s1 s2 in
    ctx, vars, s
  | SElet(x,{simple_expr_node = SElet(y,e1,e2); _},e3) ->
    (* we interpret
       [tag] let x = (let y = e1 in e2) in e3
       as
       [tag] let y = e1 in let x = e2 in e3
    *)
    simple_expr_to_why1_stmt ctx vars
      { simple_expr_tag = tag;
        simple_expr_node =
          SElet(y,e1,{ simple_expr_tag = "";
                       simple_expr_node =
                         SElet(x,e2,e3)})}
  | SElet(pv,e,i) ->
    begin
      match type_of pv.Ity.pv_ity with
      | exception (Error(_msg,expl)) ->
        unsupported
          "@[<hov 2>simple_expr_to_why1_stmt:@ let on type@ @[`%a`@] (%s)@]"
          Ity.print_ity pv.Ity.pv_ity expl
      | (is_mutable,ty) ->
        let ctx, res_var = declare_why_var_for_pv ctx ~is_global:false ~is_mutable pv in
        begin
          try
            let ctx, rs, lets, args = simple_expr_to_function_call [] ctx e in
            let ctx,vars,s = simple_expr_to_why1_stmt ctx vars i in
            let name = get_or_declare_function rs in
            let ctx, lets =
              List.fold_right
                (fun (pv,e) (ctx, lets) ->
                   let ctx, e' = simple_expr_to_why1_expr ctx e in
                   let is_mutable,ty = type_of pv.Ity.pv_ity in
                   let ctx, n = declare_why_var_for_pv ctx ~is_global:false ~is_mutable pv in
                   (ctx, (ty,n,e') :: lets))
                 lets (ctx, [])
             in
             let ctx,args =
               List.fold_right
                 (fun pv (ctx,args) ->
                    let ctx,a = mlw_pv_to_why1_expr ctx pv in
                    ctx,a::args) args (ctx,[])
             in
             let call = s_call tag (Some(ty,res_var,s)) lets name args in
             ctx,vars,call
           with NotAFunctionCall ->
             try
               let ctx, e = simple_expr_to_why1_expr ctx e in
               let ctx,vars,s = simple_expr_to_why1_stmt ctx vars i in
               ctx,vars,s_let_in tag ty res_var e s
             with NotExpression ->
               begin
                 let ctx, e = simple_expr_to_why1_cond ctx e in
                 let ctx,vars,s = simple_expr_to_why1_stmt ctx vars i in
                 let pb = s_block "" [] in
                 let pa = s_assign "" ty res_var e_bwtrue in
                 let pite = s_ite "" e pa pb in
                 let pb = s_block "" [pite; s] in
                 ctx,vars,s_let_in tag ty res_var e_bwfalse pb
               end
         end
    end
  | SEif(e1,e2,e3) ->
    begin
      match simple_expr_to_why1_cond ctx e1 with
      | ctx, c ->
        let ctx,vars,s1 = simple_expr_to_why1_stmt ctx vars e2 in
        let ctx,vars,s2 = simple_expr_to_why1_stmt ctx vars e3 in
        ctx,vars,s_ite tag c s1 s2
      | exception (Error ("unsupported feature",_)) ->
        let pv = Ity.create_pvsymbol (Ident.id_fresh "cond") Ity.ity_bool in
        let s =
          mk_instr tag
            (SElet(pv, e1,mk_instr tag (SEif(mk_instr "" (SEvar pv),e2,e3))))
        in
        if !verbose_level >= 4 then
          Format.eprintf "@[converting if expression into@ `@[%a@]`@]@."
            print_simple_expr s;
        simple_expr_to_why1_stmt ctx vars s
    end
  | SEwhile(cond,invs,_vars,body) ->
    let ctx, c = simple_expr_to_why1_cond ctx cond in
    let ctx, i =
      List.fold_right (fun inv (ctx, invs)  ->
          let ctx, v = mlw_fmla_to_why1_cond ctx inv in
          (* TODO get the name of the invariants from Why3? *)
          (ctx, (None, v)::invs)) invs (ctx, [])
    in
    let ctx,vars,b = simple_expr_to_why1_stmt ctx vars body in
    ctx,vars,s_while tag c i b
  | SEassert(Assert,t) ->
    let ctx, c = mlw_fmla_to_why1_cond ctx t in
    ctx,vars,s_assert tag c
  | SEassert(Assume,t) ->
    let ctx, c = mlw_fmla_to_why1_cond ctx t in
    ctx,vars,s_assume tag c
  | SEassert(Check,t) ->
    let ctx, c = mlw_fmla_to_why1_cond ctx t in
    ctx,vars,s_assert tag c
  | SEbreak -> ctx, vars, s_break tag



let loop_tags = ref Wstdlib.Mstr.empty
let loop_tags_counter = ref 0

let record_loop tag e =
  let n =
    match tag with
    | "" ->
       let a = "anonymous_loop_" ^ string_of_int !loop_tags_counter in
       incr loop_tags_counter;
       a
    | n -> n
  in
  loop_tags := Wstdlib.Mstr.add n e !loop_tags;
  n



let rec mlw_expr_to_simple_expr (* ctx vars *)e =
  let tag =
    Ident.Sattr.fold
      (fun a acc ->
        let s = a.Ident.attr_string in
        try Strings.remove_prefix "bddinfer:" s
        with Not_found -> acc)
      e.e_attrs ""
  in
  let open Expr in
  match e.e_node with
  | Evar pv -> mk_instr tag (SEvar pv)
  | Econst c -> mk_instr tag (SEconst c)
  | Eexec(cexp,cty) -> mk_instr tag (SEexec(cexp,cty))
  | Eassign l -> mk_instr tag (SEassign l)
  | Elet(LDvar(pv,e1),e2) ->
    if is_type_unit pv.Ity.pv_ity then
       let s1 = mlw_expr_to_simple_expr e1 in
       let s2 = mlw_expr_to_simple_expr e2 in
       begin
(* not a good solution to example/whyml/support5.mlw
         match s1.simple_expr_node with
         | SEexec({Expr.c_node=Capp(rs,[])},_) when Expr.is_rs_tuple rs -> s2
         | SEexec({Expr.c_node=Cpur(ls,[])},_) when Term.is_fs_tuple ls -> s2
         | _ -> *)
         mk_instr tag (SEseq(s1,s2))
       end
     else
    let s1 = mlw_expr_to_simple_expr e1 in
       let s2 = mlw_expr_to_simple_expr e2 in
       mk_instr tag (SElet(pv,s1,s2))
  | Elet(LDsym _,_) ->
     unsupported "mlw_expr_to_simple_expr: execution of local sym"
  | Elet(LDrec _,_) ->
     unsupported "mlw_expr_to_simple_expr: execution of local rec"
  | Eif(e1,e2,e3) ->
     let s1 = mlw_expr_to_simple_expr e1 in
     let s2 = mlw_expr_to_simple_expr e2 in
     let s3 = mlw_expr_to_simple_expr e3 in
     mk_instr tag (SEif(s1,s2,s3))
  | Ewhile(cond,invs,vars,body) ->
     let looptag = record_loop tag e in
     let c = mlw_expr_to_simple_expr cond in
     let b = mlw_expr_to_simple_expr body in
(* we do not use

     mk_instr looptag (SEwhile(c,invs,vars,b))

  anymore, but the construct

     while true do (if c then body else break) done

  It has no impact on the generated invariants.
  It avoids the support for function calls in condition of while.
  (Yet, support for function calls in condition of if is required)
*)
       let b = mk_instr "" (SEif(c,b,mk_instr "" SEbreak)) in
       let se_true = mlw_expr_to_simple_expr e_true in
       mk_instr looptag (SEwhile(se_true,invs,vars,b))
  | Efor    _ (* pvsymbol * for_bounds * pvsymbol * invariant list * expr *) ->
     unsupported "mlw_expr_to_simple_expr: Efor"
  | Eassert(k,t) -> mk_instr tag (SEassert(k,t))
  (* ad-hoc support for "break" *)
  | Eraise(xs, _e1) when xs.Ity.xs_name.Ident.id_string = Ptree_helpers.break_id ->
     mk_instr tag SEbreak
  | Eexn(xs, e1) when xs.Ity.xs_name.Ident.id_string = Ptree_helpers.break_id ->
    let open Ity in
    begin
      match e1.e_node with
      | Ematch(e2,[],excs) ->
        begin
          match Mxs.bindings excs with
          | [xss,_] when xs_equal xss xs ->
            mlw_expr_to_simple_expr e2
          | _ ->
            unsupported "mlw_expr_to_simple_expr: Eexn (1)"
        end
      | _ ->
        unsupported "mlw_expr_to_simple_expr: Eexn (2)"
    end
  (* end of ad-hoc support for break *)
  | Eraise  _ (* xsymbol * expr *) ->
     unsupported "mlw_expr_to_simple_expr: Eraise"
  | Eexn    _ (* xsymbol * expr *) ->
     unsupported "mlw_expr_to_simple_expr: Eexn"
  | Ematch  _ (* expr * reg_branch list * exn_branch Mxs.t *) ->
     unsupported "mlw_expr_to_simple_expr: Ematch"
  | Eghost  _ (* expr *) ->
     unsupported "mlw_expr_to_simple_expr: Eghost"
  | Epure   _ (* term *) ->
     unsupported "mlw_expr_to_simple_expr: Epure"
  | Eabsurd ->
     unsupported "mlw_expr_to_simple_expr: Eabsurd"


let decl_global_vs vs d acc =
  if not d.is_global then acc else
    let name = d.why_var in
    let open Ty in
    let ty = vs.Term.vs_ty in
    let ty =
    match ty.ty_node with
    | Tyapp(id,[]) when ts_equal id Ty.ts_int ->  Tint
    | Tyapp(id,[]) when ts_equal id Ty.ts_bool -> Tbool
    | Tyapp(id,[ty]) when
           id.ts_name.Ident.id_string = "ref" && is_ty_int ty ->
       Tint
    | Tyapp(id,[ty]) when
           id.ts_name.Ident.id_string = "ref" && is_ty_bool ty ->
       Tbool
    | Tyapp(_id,_l) ->
       unsupported "decl_global_vs: type `%a`" Pretty.print_ty ty
    | Tyvar _ ->
       unsupported "decl_global_vs: type variable `%a`" Pretty.print_ty ty
  in VarMap.add name ty acc


let f_decl_rs ctx rs name acc : func FuncMap.t =
  (* Format.printf "f_decl : %a@." print_rs rs; *)
  let cty = rs.rs_cty in
  let ctx, args =
    match cty.Ity.cty_args with
    | [pv] when is_type_unit pv.Ity.pv_ity ->
       ctx,[]
    | args ->
       List.fold_right (fun pv (ctx, args) ->
           let ctx, n = declare_why_var_for_pv ctx ~is_global:false ~is_mutable:false pv in
           let (b,ty) =
             try type_of pv.Ity.pv_ity
             with Error(_msg,expl) ->
               unsupported
                 "@[<hov 2>f_decl_rs: rs=%a@ arg %a of type@ @[`%a`@] (%s)@]"
                 print_rs rs print_pv pv
                 Ity.print_ity pv.Ity.pv_ity expl

           in
           ctx, (b, ty, n)::args
         ) args (ctx, [])
  in
  (*
  Format.eprintf
    "@[ctx =@ @[{ %a }@]@."
    (Pp.print_list Pp.comma print_vs)
    (Term.Mvs.bindings ctx);
   *)
  (*
  Format.eprintf
    "@[eff_reads =@ @[{ %a }@]@."
    (Pp.print_list Pp.comma print_pvty)
    (Ity.Spv.elements cty.cty_effect.eff_reads);
  Format.eprintf
    "@[eff_writes =@ @[[ %a ]@]@]@."
    (Pp.print_list Pp.semi
       (fun fmt (reg,pvs) ->
         Format.fprintf fmt "@[%a -> { %a } @]"
           Ity.print_reg reg
           (Pp.print_list Pp.comma print_pv)
           (Ity.Spv.elements pvs)
       ))
    (Ity.Mreg.bindings cty.cty_effect.eff_writes);
  Format.eprintf
    "@[oldies =@ @[[ %a ]@]@]@."
    (Pp.print_list Pp.semi
       (fun fmt (pv1,pv2) ->
         Format.fprintf fmt "@[%a -> %a@]" print_pv pv1 print_pv pv2
       ))
    (Ity.Mpv.bindings cty.cty_oldies);
  *)
  let add_write pv writes =
    let open Ity in
    match pv.pv_ity.ity_node with
    | Ityreg r ->
       begin
         try
           let _ = Ity.Mreg.find r cty.cty_effect.eff_writes in
           let v =
             try
               let d = Term.Mvs.find pv.pv_vs ctx.env in
               d.why_var
             with Not_found ->
               translation_error "add_write: missing pv `%s` in ctx" pv.pv_vs.Term.vs_name.Ident.id_string
           in
           let (_,ty) = type_of pv.pv_ity in
           VarMap.add v ty writes
         with Not_found ->
           (* Format.eprintf "Mutable variable %a is not in eff_writes" print_pv pv; *)
           writes
       end
    | Ityapp _ | Ityvar _ ->
       (* Format.eprintf "Variable %a is not mutable" print_pv pv; *)
       writes
  in
  let writes =
    Ity.(Spv.fold add_write cty.cty_effect.eff_reads VarMap.empty)
  in
  let writes =
    List.fold_right add_write cty.Ity.cty_args writes
  in
  (*
  Format.eprintf
    "@[writes =@ @[[ %a ]@]@]@."
    (Pp.print_list Pp.semi Format.pp_print_string) writes;
  *)
  let ctx =
    Ity.Mpv.fold
      (fun pv1 pv2 ctx ->
        let is_old_for = pv2.Ity.pv_vs in
        let ctx,_v =
          declare_why_var_for_pv ctx ~is_global:false ~is_mutable:false ~is_old_for pv1 in
        ctx)
    cty.Ity.cty_oldies ctx
  in
  let ctx,result,post =
    List.fold_left
      (fun (ctx,result,acc) t ->
        let ctx, result, t' =
          match result, t.Term.t_node with
          | None, Term.Teps tb ->
             let v,t = Term.t_open_bound tb in
             (* Format.eprintf "result = %a@." print_vs v; *)
             let ctx,res = declare_why_var_for_vs ~is_global:false ~is_mutable:false ~is_result:true ctx v in
             let (ctx, t) = mlw_fmla_to_why1_cond ctx t in
             let res =
               try Some(type_of_ty v.Term.vs_ty,res) with
                 Invalid_argument _ -> result
             in
             (ctx, res, t)
          | _ ->
             let (ctx,t) = mlw_fmla_to_why1_cond ctx t in
             (ctx, result, t)
        in
        (ctx, result, and_cond acc t')
      )
      (ctx, None, true_cond) cty.Ity.cty_post
  in
  (* fix the result if it is not mentioned in the post-condition *)
  let result =
    let open Ity in
    if is_type_unit cty.cty_result then None else
      match result with
      | Some _ -> result
      | None ->
         let ty = Ity.ty_of_ity cty.cty_result in
         let id = Ident.id_fresh "result" in
         let vs = Term.create_vsymbol id ty in
         let _,res = declare_why_var_for_vs ~is_global:false ~is_mutable:false ~is_result:true ctx vs in
         let is_ref,ty = type_of cty.cty_result in
         assert (not is_ref);
         Some(ty,res)
  in
  let d = declare_function_val ~name ~params:args ~writes ~result ~post in
  FuncMap.add name d acc




(** {2 Translating back to Why3 } *)


(* TODO the following should be provided by Why3 API ! *)

let builtin_symbols = Wstdlib.Hstr.create 17

let add_int = Ident.op_infix "+"
let sub_int = Ident.op_infix "-"
let mul_int = Ident.op_infix "*"
(* let div_int = Ident.op_infix "/" *)
let minus_int = Ident.op_prefix "-"
let ge_int = Ident.op_infix ">="
let gt_int = Ident.op_infix ">"
let le_int = Ident.op_infix "<="
let lt_int = Ident.op_infix "<"
let bool_not = "notb"
let bool_or = "orb"
let bool_and = "andb"

let built_in_symbols =
  [
    ["bool"],"Bool", [],
    [ bool_not;
      bool_or;
      bool_and;
    ];
    ["int"],"Int", [],
    [ add_int;
      sub_int;
      mul_int;
      minus_int;
      lt_int;
      le_int;
      gt_int;
      ge_int;
    ] ;
    ["ref"],"Ref", [],
    [ (*logic_deref*) ]
  ]

let add_builtin_th env (l,n,t,d) =
  try
  let th = Env.read_theory env l n in
  List.iter
    (fun (id,r) ->
      let ts = Theory.ns_find_ts th.Theory.th_export [id] in
      r ts)
    t;
  List.iter
    (fun id ->
      let ls = Theory.ns_find_ls th.Theory.th_export [id] in
      Wstdlib.Hstr.add builtin_symbols id ls)
    d
  with e ->
    translation_error "add_builtin_th: %a"
      Exn_printer.exn_printer e

let get_builtins ctx =
  Wstdlib.Hstr.clear builtin_symbols;
  List.iter (add_builtin_th ctx) built_in_symbols

let term_app ls l : Term.term =
  try
    Term.t_app_infer ls l
  with e ->
    translation_error "term_app: ill-typed application of `%a` to `[%a]`: %a"
      Pretty.print_ls ls Pp.(print_list semi Pretty.print_term) l
      Exn_printer.exn_printer e

let rec binop_to_term rev_map op e1 e2 =
  let ls =
    try
      Wstdlib.Hstr.find builtin_symbols op
    with Not_found ->
      translation_error "binop_to_term"
  in
  let e1 = expression_to_term rev_map e1 in
  let e2 = expression_to_term rev_map e2 in
  term_app ls [e1;e2]

and unop_to_term rev_map op e =
  let ls =
    try
      Wstdlib.Hstr.find builtin_symbols op
    with Not_found ->
      translation_error "unop_to_term"
  in
  let e = expression_to_term rev_map e in
  term_app ls [e]

and expression_to_term rev_map e =
  let open Term in
  match e with
  | Evar(v,Here) ->
     let is_mut,x =
       try
         VarMap.find v rev_map
       with Not_found ->
         translation_error "expression_to_term: Evar not found"
     in
     if is_mut then
       term_app Pmodule.ls_ref_proj [t_var x]
     else
       t_var x
  | Evar(_v,Old) ->
     translation_error "expression_to_term: Evar Old"
  | Ecst n ->
     let c = Number.(int_literal ILitDec ~neg:false n) in
     t_const (Constant.ConstInt c) Ty.ty_int
  | Eadd(e1,e2) -> binop_to_term rev_map add_int e1 e2
  | Esub(e1,e2) -> binop_to_term rev_map sub_int e1 e2
  | Emul(e1,e2) -> binop_to_term rev_map mul_int e1 e2
  | Ediv(_e1,_e2) -> (* binop_to_term rev_map div_int e1 e2 *)
     translation_error "expression_to_term: Ediv"
  | Emod _ (* expression * expression *) ->
     translation_error "expression_to_term: Emod"
  | Ebwtrue -> t_bool_true
  | Ebwfalse -> t_bool_false
  | Ebwnot e -> unop_to_term rev_map bool_not e
  | Ebwand(e1,e2) -> binop_to_term rev_map bool_and e1 e2
  | Ebwor(e1,e2) -> binop_to_term rev_map bool_or e1 e2

and atomic_condition_to_term rev_map c =
  let open Term in
  match c with
  | Ceq(e1, e2) ->
      let e1' = expression_to_term rev_map e1 in
      let e2' = expression_to_term rev_map e2 in
      t_equ e1' e2'
  | Cne(e1, e2) ->
      let e1' = expression_to_term rev_map e1 in
      let e2' = expression_to_term rev_map e2 in
      t_neq e1' e2'
  | Clt(e1, e2) -> binop_to_term rev_map lt_int e1 e2
  | Cle(e1, e2) -> binop_to_term rev_map le_int e1 e2
  | Cgt(e1, e2) -> binop_to_term rev_map gt_int e1 e2
  | Cge(e1, e2) -> binop_to_term rev_map ge_int e1 e2
  | C_is_true (Ebwnot e) ->
     t_equ (expression_to_term rev_map e) t_bool_false
  | C_is_true e ->
     t_equ (expression_to_term rev_map e) t_bool_true


let rec condition_to_term rev_map c =
  let open Term in
  if !verbose_level >= 4 then
    Format.eprintf "condition_to_term, condition = %a@." print_condition c;
  match c with
  | BAtomic c -> atomic_condition_to_term rev_map c
  | BTrue -> t_true
  | BFalse  -> t_false
  | Bite(c,c1,c2) ->
    t_if
      (condition_to_term rev_map c)
      (condition_to_term rev_map c1)
      (condition_to_term rev_map c2)
  | BAnd(c1,c2) ->
     t_and (condition_to_term rev_map c1) (condition_to_term rev_map c2)
  | BOr(c1,c2)  ->
     t_or (condition_to_term rev_map c1) (condition_to_term rev_map c2)



let abstract_state_to_why3_term_and_dom ctx s =
  let cs = Interp_expression.abstract_state_to_conditions s in
  let dom = get_domains s in
  let rev_map =
    Term.Mvs.fold
      (fun vs d acc -> VarMap.add d.why_var (d.is_mutable,vs) acc)
      ctx VarMap.empty
  in
  let f =
    List.fold_left
      (fun acc c ->
        if !verbose_level >= 4 then Format.eprintf "Here1, condition = %a@." print_condition c;
        let f = Term.t_and_simp acc (condition_to_term rev_map c) in
        if !verbose_level >= 4 then Format.eprintf "Here2@.";
        f
      )
      Term.t_true
      cs
  in
  let dom =
    VarMap.fold
      (fun x d acc ->
        try
          let _,vs = VarMap.find x rev_map in
          Term.Mvs.add vs d acc
        with Not_found -> assert false)
      dom Term.Mvs.empty
  in
  f,dom


type domains = Abstract.domain Term.Mvs.t

type engine_report = {
    engine_error : (string * string) option;
    engine_running_time : float;
    engine_num_bool_vars : int;
    engine_invariants_and_domains : (Term.term * domains) Wstdlib.Mstr.t;
    engine_subreport : Infer.interp_report option;
  }

let empty_report = {
    engine_error = None;
    engine_running_time = 0.0;
    engine_num_bool_vars = 0;
    engine_invariants_and_domains = Wstdlib.Mstr.empty;
    engine_subreport = None;
  }

let infer_loop_invs_for_mlw_expr last_report _attrs env tkn mkn e cty =
  try
    begin
      if !verbose_level >= 3 then
        Format.printf "@[You have triggered BDD-infer loop inference on expression@ @[%a@]@]@."
          Expr.print_expr e;
      let instr = mlw_expr_to_simple_expr e in
      if !verbose_level >= 4 then
        Format.printf "@[Here is the simplified expression@ @[%a@]@]@."
          print_simple_expr instr;
      let ctx = {
        known = tkn;
        env = Term.Mvs.empty;
      }
      in
      ignore mkn;
      let ctx, _vars, p_ast = simple_expr_to_why1_stmt ctx Ity.Spv.empty instr in
(*
      if !verbose_level >= 3 then
        begin
          Format.printf "@[Here are the global variables :@ @[[%a]@]@]@."
            (Pp.print_list Pp.semi
               (fun fmt pv ->
                 Format.fprintf fmt "%a@ " print_pv pv))
            (Ity.Spv.elements vars);
        end;
*)
      let ctx, p_ast =
        List.fold_left
          (fun (ctx,a) pre ->
            let ctx,t = mlw_fmla_to_why1_cond ctx pre in
            let a = s_sequence "" (s_assume "" t) a in
            (ctx,a))
          (ctx,p_ast) cty.Ity.cty_pre
      in
      if !verbose_level >= 4 then
        begin
          Format.printf "@[Here are the variables in the vs_table:@ @[[%a]@]@]@."
            (Pp.print_list Pp.semi
               (fun fmt (vs,d) ->
                 Format.fprintf fmt "@[%a -> %b,%a@]@ " print_vs vs d.is_global print_var d.why_var))
            (Term.Mvs.bindings ctx.env);
        end;
      let decl = Term.Mvs.fold decl_global_vs ctx.env VarMap.empty in
      let f_decl = Expr.Mrs.fold (f_decl_rs ctx) !rs_table FuncMap.empty in
      let variables = decl in
      let functions = f_decl in
      let main = p_ast in
      let prog = Ast.mk_program ~name:"" ~variables ~functions ~main in
      if !verbose_level >= 3 then
        Format.printf "%a@." Ast.print_program prog;
      (* interpretation *)
      let ai_init_time = Unix.times () in
      let report =
        try
          Infer.interp_prog prog
        with
        | Apron.Manager.Error e ->
           engine_error "Apron exception: %a@." Apron.Manager.print_exclog e
        | Invalid_argument e when e = "Bdd.mk_var" ->
           engine_error "maximum number of BDD variables reached"
      in
      let ai_end_time = Unix.times () in
      let (n,_) = bdd_stats () in
      last_report :=
        { !last_report with
          engine_running_time = Unix.(ai_end_time.tms_utime -. ai_init_time.tms_utime);
          engine_num_bool_vars = n;
          engine_subreport = Some report;
        };
      get_builtins env;
      let invs_list, invs_and_doms =
        Wstdlib.(
          Mstr.fold
            (fun key s (invsl,invs) ->
              match Mstr.find key !loop_tags with
              | exception Not_found ->
                 (* translation_error "loop tag `%s` not found" key *)
                 (invsl,invs)
              | e ->
              if !verbose_level >= 4 then
                Format.printf "@[Converting state@ @[%a@]@]@." print s;
              let inv,dom = abstract_state_to_why3_term_and_dom ctx.env s in
              if !verbose_level >= 4 then
                Format.printf "@[State converted to@ @[%a@]@]@." Pretty.print_term inv;
              ((e,inv)::invsl,Mstr.add key (inv,dom) invs))
            report.Infer.invariants ([],Mstr.empty))
      in
      last_report :=
        { !last_report with
          engine_invariants_and_domains = invs_and_doms;
        };
      invs_list

    end
  with
  | Error(expl,msg) ->
    let msg =
      Format.asprintf "%s: %s@\n%s" expl msg
        (Printexc.get_backtrace ())
    in
    last_report :=
      { !last_report with
        engine_error = Some (expl,msg);
      };
    []
  | exn ->
    let msg =
      Format.asprintf "%a@\n%s" Exn_printer.exn_printer exn
        (Printexc.get_backtrace ())
    in
    last_report :=
      { !last_report with
        engine_error = Some ("other exception", msg) ;
      };
    []


let print_var_dom fmt (v,d) =
  Format.fprintf fmt "@[%a = %a@]"
    Pretty.print_vs v Abstract.print_domain d

let print_domains fmt m =
  Format.fprintf fmt "@[<hov 2>%a@]"
    Pp.(print_list semi print_var_dom) (Term.Mvs.bindings m)

let report ~verbosity report =
  match report.engine_error with
  | Some(reason,expl) ->
     Format.printf "BDD-infer failure: %s, %s@." reason expl
  | None ->
      if verbosity >= 1 then
        (* generated loop invariants *)
        Wstdlib.Mstr.iter
          (fun tag (inv,doms) ->
             Format.printf "@[<hov 2>[BDDinfer] inferred invariant for loop [%s] is@ @[%a@]@]@."
               tag Pretty.print_term inv;
             Format.printf "@[<hov 2>[BDDinfer] inferred domains for loop [%s] are@ @[%a@]@]@."
               tag print_domains doms)
          report.engine_invariants_and_domains;
      if verbosity >= 2 then
        match report.engine_subreport with
        | Some r ->
            Format.printf "[BDDinfer] internal info available (verbosity %d):@." verbosity;
            Infer.report ~verbosity r;
            Format.printf "[BDDinfer] end of internal info.@."
        | None ->
            Format.printf "[BDDinfer] no internal info available (verbosity %d).@." verbosity

let default_hook r =
  report ~verbosity:!verbose_level r

let hook_report = ref default_hook

let infer_loop_invs attrs env tkn mkn e cty =
  let do_infer =
    Ident.Sattr.fold
      (fun a acc ->
         try
           let suf = Strings.remove_prefix "bddinfer" a.Ident.attr_string in
           begin try
             let n = int_of_string (Strings.remove_prefix ":" suf) in
             verbose_level := n
             with _ -> ()
           end;
           true
         with Not_found -> acc)
      attrs false
  in
  if do_infer then
    begin
      let last_report = ref empty_report in
      loop_tags_counter := 0;
      loop_tags := Wstdlib.Mstr.empty;
      Ast.reset_ast_generation ();
      let l = infer_loop_invs_for_mlw_expr last_report attrs env tkn mkn e cty in
      !hook_report !last_report;
      l
    end
  else []

let register_hook f = hook_report := f

let () = Vc.set_infer_invs infer_loop_invs
