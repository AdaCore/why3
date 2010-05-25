
open Why
open Ident
open Theory
open Term
open Ty
open Pgm_typing

type effect = Pgm_effect.t

type pre = Term.fmla

type post_fmla = Term.vsymbol (* result *) * Term.fmla
type exn_post_fmla = Term.vsymbol (* result *) option * Term.fmla

type post = post_fmla * (Term.lsymbol * exn_post_fmla) list

type type_v = 
  | Tpure of Ty.ty
  | Tarrow of binder list * type_c

and type_c = 
  { c_result_type : type_v;
    c_effect      : effect;
    c_pre         : pre;
    c_post        : post; }

and binder = Term.vsymbol * type_v


type env = {
  uc      : theory_uc;
  globals : type_v Mls.t;
  locals  : type_v Mvs.t;
  ts_arrow: tysymbol;
  ts_label: tysymbol;
  ts_ref: tysymbol;
  ls_at : lsymbol;
  ls_bang : lsymbol;
  ls_old : lsymbol;
}

let empty_env uc = { 
  uc = uc; globals = Mls.empty; locals = Mvs.empty;
  (* types *)
  ts_arrow = ns_find_ts (get_namespace uc) ["arrow"];
  ts_label = ns_find_ts (get_namespace uc) ["label"];
  ts_ref   = ns_find_ts (get_namespace uc) ["ref"];
  (* functions *)
  ls_at = ns_find_ls (get_namespace uc) ["at"];
  ls_bang = ns_find_ls (get_namespace uc) ["prefix !"];
  ls_old = ns_find_ls (get_namespace uc) ["old"];
}

let add_local x v env = { env with locals = Mvs.add x v env.locals }

let add_global x v env = { env with globals = Mls.add x v env.globals }

let add_decl d env = { env with uc = add_decl env.uc d }

let ts_arrow uc = ns_find_ts (get_namespace uc) ["arrow"]

let currying uc tyl ty =
  let make_arrow_type ty1 ty2 = Ty.ty_app (ts_arrow uc) [ty1; ty2] in
  List.fold_right make_arrow_type tyl ty

let rec purify uc = function
  | Tpure ty -> 
      ty
  | Tarrow (bl, c) -> 
      currying uc (List.map (fun (v,_) -> v.vs_ty) bl) 
	(purify uc c.c_result_type)

let post_map f ((v, q), ql) = 
  (v, f q), List.map (fun (e,(v,q)) -> e, (v, f q)) ql

let v_result ty = create_vsymbol (id_fresh "result") ty

let type_c_of_type_v env = function
  | Tarrow ([], c) ->
      c
  | v ->
      let ty = purify env.uc v in
      { c_result_type = v;
	c_effect      = Pgm_effect.empty;
	c_pre         = f_true;
	c_post        = (v_result ty, f_true), []; }

let subst1 vs1 vs2 = Mvs.add vs1 (t_var vs2) Mvs.empty

let rec subst_type_c s c = 
  { c_result_type = subst_type_v s c.c_result_type;
    c_effect      = c.c_effect;
    c_pre         = f_subst s c.c_pre;
    c_post        = post_map (f_subst s) c.c_post; }

and subst_type_v s = function
  | Tpure _ as v -> v
  | Tarrow (bl, c) -> Tarrow (bl, subst_type_c s c)

let apply_type_v env v vs = match v with
  | Tarrow ((x, _) :: bl, c) ->
      let c = type_c_of_type_v env (Tarrow (bl, c)) in
      subst_type_c (subst1 x vs) c
  | Tarrow ([], _) | Tpure _ -> 
      assert false

(* pretty-printers *)

open Pp
open Format
open Pretty 

let print_post fmt ((_,q), el) =
  let print_exn_post fmt (l,(_,q)) = 
    fprintf fmt "| %a -> {%a}" print_ls l print_fmla q 
  in
  fprintf fmt "{%a} %a" print_fmla q (print_list space print_exn_post) el

let rec print_type_v fmt = function
  | Tpure ty -> 
      print_ty fmt ty
  | Tarrow (bl, c) ->
      fprintf fmt "@[<hov 2>%a ->@ %a@]" 
	(print_list arrow print_binder) bl print_type_c c

and print_type_c fmt c =
  fprintf fmt "@[{%a}@ %a%a@ %a@]" print_fmla c.c_pre
    print_type_v c.c_result_type Pgm_effect.print c.c_effect
    print_post c.c_post

and print_binder fmt (x, v) =
  fprintf fmt "(%a:%a)" print_vs x print_type_v v


