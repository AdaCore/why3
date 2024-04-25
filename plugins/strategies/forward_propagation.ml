(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2022 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3
open Strategy
open Term
open Decl
open Ty
open Theory
open Ident
open Task
open Format

type ufloat_symbols = {
  ufloat_type : tysymbol;
  to_real : lsymbol;
  uadd : lsymbol;
  usub : lsymbol;
  umul : lsymbol;
  udiv : lsymbol;
  uminus : lsymbol;
  uadd_infix : lsymbol;
  usub_infix : lsymbol;
  umul_infix : lsymbol;
  udiv_infix : lsymbol;
  uminus_prefix : lsymbol;
  eps : term;
  eta : term;
  real_fun : lsymbol;
}

type symbols = {
  add : lsymbol;
  sub : lsymbol;
  mul : lsymbol;
  _div : lsymbol;
  minus : lsymbol;
  add_infix : lsymbol;
  sub_infix : lsymbol;
  mul_infix : lsymbol;
  div_infix : lsymbol;
  minus_infix : lsymbol;
  lt : lsymbol;
  lt_infix : lsymbol;
  le : lsymbol;
  le_infix : lsymbol;
  abs : lsymbol;
  sum : lsymbol;
  exp : lsymbol;
  log : lsymbol;
  log2 : lsymbol;
  log10 : lsymbol;
  sin : lsymbol;
  cos : lsymbol;
  from_int : lsymbol;
  usingle_symbols : ufloat_symbols;
  udouble_symbols : ufloat_symbols;
  ident_printer : ident_printer;
  tv_printer : ident_printer;
}

let symbols = ref None
let ( !! ) s = Option.get !s

(* This type corresponds to the numeric info we have on a real/float term *)
type term_info = {
  (*
   * Forward error associated to a float term "t"
   * "Some (exact_t, rel_err, t', cst_err)" stands for
   * "|t - exact_t| <= rel_err * t' + cst_err", where |exact_t| <= t'
   *)
  error : (term * term * term * term) option;
  (*
   * "Some (op, [x; y])" means that the term "t" is the result of the FP operation
   * "op" on "x" and "y"
   *)
  ieee_op : (lsymbol * term list) option;
}

type info = {
  terms_info : term_info Mterm.t;
  (*
   * An entry '(i, j, exact_fn, rel_err, fn', cst_err)' for a ls 'fn' means that
   * `forall k. i <= k < j -> |fn k - exact_fn k| <= fn' k * rel_err + cst_err`
   * This is used for sum error propagation
   *)
  fns_info : (term option * term option * term * term * term * term) Mls.t;
  ls_defs : term Mls.t;
}

let default_strat () = Sdo_nothing

let zero =
  t_const
    (Constant.ConstReal
       (Number.real_literal ~radix:10 ~neg:false ~int:"0" ~frac:"0" ~exp:None))
    ty_real

let one =
  t_const
    (Constant.ConstReal
       (Number.real_literal ~radix:10 ~neg:false ~int:"1" ~frac:"0" ~exp:None))
    ty_real

let is_zero t = t_equal zero t
let is_one t = t_equal one t

let abs t =
  match t.t_node with
  (* Don't add an abs symbol on top of another *)
  | Tapp (ls, [ _ ]) when ls_equal !!symbols.abs ls -> t
  | _ -> fs_app !!symbols.abs [ t ] ty_real

let from_int t = fs_app !!symbols.from_int [ t ] ty_real

let is_ineq_ls ls =
  let symbols = !!symbols in
  ls_equal ls symbols.lt || ls_equal ls symbols.le
  || ls_equal ls symbols.lt_infix
  || ls_equal ls symbols.le_infix

let is_add_ls ls = ls_equal ls !!symbols.add || ls_equal ls !!symbols.add_infix
let is_sub_ls ls = ls_equal ls !!symbols.sub || ls_equal ls !!symbols.sub_infix
let is_mul_ls ls = ls_equal ls !!symbols.mul || ls_equal ls !!symbols.mul_infix

let is_minus_ls ls =
  ls_equal ls !!symbols.minus || ls_equal ls !!symbols.minus_infix

let is_abs_ls ls = ls_equal ls !!symbols.abs

let is_to_real_ls ls =
  ls_equal ls !!symbols.usingle_symbols.to_real
  || ls_equal ls !!symbols.udouble_symbols.to_real

let is_uadd_ls ls =
  ls_equal ls !!symbols.usingle_symbols.uadd
  || ls_equal ls !!symbols.usingle_symbols.uadd_infix
  || ls_equal ls !!symbols.udouble_symbols.uadd
  || ls_equal ls !!symbols.udouble_symbols.uadd_infix

let is_usub_ls ls =
  ls_equal ls !!symbols.usingle_symbols.usub
  || ls_equal ls !!symbols.usingle_symbols.usub_infix
  || ls_equal ls !!symbols.udouble_symbols.usub
  || ls_equal ls !!symbols.udouble_symbols.usub_infix

let is_umul_ls ls =
  ls_equal ls !!symbols.usingle_symbols.umul
  || ls_equal ls !!symbols.usingle_symbols.umul_infix
  || ls_equal ls !!symbols.udouble_symbols.umul
  || ls_equal ls !!symbols.udouble_symbols.umul_infix

let is_udiv_ls ls =
  ls_equal ls !!symbols.usingle_symbols.udiv
  || ls_equal ls !!symbols.usingle_symbols.udiv_infix
  || ls_equal ls !!symbols.udouble_symbols.udiv
  || ls_equal ls !!symbols.udouble_symbols.udiv_infix

let is_uminus_ls ls =
  ls_equal ls !!symbols.usingle_symbols.uminus
  || ls_equal ls !!symbols.usingle_symbols.uminus_prefix
  || ls_equal ls !!symbols.udouble_symbols.uminus
  || ls_equal ls !!symbols.udouble_symbols.uminus_prefix

let is_uop ls =
  is_uadd_ls ls || is_usub_ls ls || is_umul_ls ls || is_udiv_ls ls
  || is_uminus_ls ls

let minus t = fs_app !!symbols.minus_infix [ t ] ty_real

let minus_simp t =
  match t.t_node with
  | Tapp (ls, [ t' ]) when is_minus_ls ls -> t'
  | _ -> minus t

let add t1 t2 = fs_app !!symbols.add_infix [ t1; t2 ] ty_real

let add_simp t1 t2 =
  if is_zero t1 then
    t2
  else if is_zero t2 then
    t1
  else
    add t1 t2

let sub t1 t2 = fs_app !!symbols.sub_infix [ t1; t2 ] ty_real

let sub_simp t1 t2 =
  if is_zero t1 then
    minus_simp t2
  else if is_zero t2 then
    t1
  else
    sub t1 t2

let mul t1 t2 = fs_app !!symbols.mul_infix [ t1; t2 ] ty_real
let div t1 t2 = fs_app !!symbols.div_infix [ t1; t2 ] ty_real

let mul_simp t1 t2 =
  if is_zero t1 || is_zero t2 then
    zero
  else if is_one t1 then
    t2
  else if is_one t2 then
    t1
  else
    match (t1.t_node, t2.t_node) with
    | Tapp (ls1, [ t1 ]), Tapp (ls2, [ t2 ]) when is_abs_ls ls1 && is_abs_ls ls2
      ->
      abs (mul t1 t2)
    | _ -> mul t1 t2

let div_simp t1 t2 =
  if is_zero t1 then
    zero
  else if is_one t2 then
    t1
  else
    div t1 t2

let ( +. ) x y = add x y
let ( -. ) x y = sub x y
let ( *. ) x y = mul x y
let ( /. ) x y = div x y
let ( ++. ) x y = add_simp x y
let ( --. ) x y = sub_simp x y
let ( **. ) x y = mul_simp x y
let ( //. ) x y = div_simp x y
let ( <=. ) x y = ps_app !!symbols.le_infix [ x; y ]

let is_ty_float ty =
  match ty.ty_node with
  | Tyapp (v, []) ->
    if
      ts_equal v !!symbols.usingle_symbols.ufloat_type
      || ts_equal v !!symbols.udouble_symbols.ufloat_type
    then
      true
    else
      false
  | _ -> false

let eps ieee_type =
  if ts_equal ieee_type !!symbols.usingle_symbols.ufloat_type then
    !!symbols.usingle_symbols.eps
  else if ts_equal ieee_type !!symbols.udouble_symbols.ufloat_type then
    !!symbols.udouble_symbols.eps
  else
    failwith (asprintf "Unsupported type %a" Pretty.print_ts ieee_type)

let eta ieee_type =
  if ts_equal ieee_type !!symbols.usingle_symbols.ufloat_type then
    !!symbols.usingle_symbols.eta
  else if ts_equal ieee_type !!symbols.udouble_symbols.ufloat_type then
    !!symbols.udouble_symbols.eta
  else
    failwith (asprintf "Unsupported type %a" Pretty.print_ts ieee_type)

let to_real ieee_type t =
  let to_real =
    if ts_equal ieee_type !!symbols.usingle_symbols.ufloat_type then
      !!symbols.usingle_symbols.to_real
    else if ts_equal ieee_type !!symbols.udouble_symbols.ufloat_type then
      !!symbols.udouble_symbols.to_real
    else
      failwith (asprintf "Unsupported type %a" Pretty.print_ts ieee_type)
  in
  fs_app to_real [ t ] ty_real

let real_fun ieee_type =
  if ts_equal ieee_type !!symbols.usingle_symbols.ufloat_type then
    !!symbols.usingle_symbols.real_fun
  else if ts_equal ieee_type !!symbols.udouble_symbols.ufloat_type then
    !!symbols.udouble_symbols.real_fun
  else
    failwith (asprintf "Unsupported type %a" Pretty.print_ts ieee_type)

let get_info info t =
  try Mterm.find t info with
  | Not_found -> { error = None; ieee_op = None }

let add_fw_error info t error =
  let t =
    match t.t_node with
    | Tapp (ls, [ t ]) when is_to_real_ls ls -> t
    | _ -> t
  in
  let t_info = get_info info t in
  let t_info = { t_info with error = Some error } in
  Mterm.add t t_info info

let add_ieee_op info ls t args =
  let t_info = get_info info t in
  let t_info = { t_info with ieee_op = Some (ls, args) } in
  Mterm.add t t_info info

let get_ts t =
  match t.t_ty with
  | None -> assert false
  | Some ty -> (
    match ty.ty_node with
    | Tyvar _ -> assert false
    | Tyapp (ts, []) -> ts
    | _ -> assert false)

(* Return the float terms inside `t`. Note that if `t` is an application of type
   float we don't return the floats that it potentially contains *)
let rec get_floats t =
  match t.t_ty with
  | Some ty when is_ty_float ty -> [ t ]
  | _ -> (
    match t.t_node with
    | Tapp (_, tl) -> List.fold_left (fun l t -> l @ get_floats t) [] tl
    | _ -> [])

let string_of_ufloat_type ts =
  if ts_equal ts !!symbols.usingle_symbols.ufloat_type then
    "single"
  else if ts_equal ts !!symbols.udouble_symbols.ufloat_type then
    "double"
  else
    failwith (asprintf "Unsupported type %a" Pretty.print_ts ts)

let string_of_ufloat_type_and_op ts uop =
  let ty_str = string_of_ufloat_type ts in
  let uop_str =
    if is_uadd_ls uop then
      "uadd"
    else if is_usub_ls uop then
      "usub"
    else if is_umul_ls uop then
      "umul"
    else
      failwith (asprintf "Unsupported uop '%a'" Pretty.print_ls uop)
  in
  uop_str ^ "_" ^ ty_str

let term_to_str t =
  let module P =
    (val Pretty.create !!symbols.ident_printer !!symbols.tv_printer
           !!symbols.ident_printer
           (Ident.create_ident_printer []))
  in
  Format.asprintf "%a" P.print_term t

(* Error on an IEEE op when propagation is needed (eg. we have a forward error
   on t1 and/or on t2) *)
let combine_uop_errors info uop t1 exact_t1 t1_rel_err t1' t1_cst_err t2
    exact_t2 t2_rel_err t2' t2_cst_err r strat_for_t1 strat_for_t2 =
  let ts = get_ts r in
  let eps = eps ts in
  let eta = eta ts in
  let to_real = to_real ts in
  let rel_err, rel_err_simp =
    if is_uadd_ls uop || is_usub_ls uop then
      (* Relative error for addition and sustraction *)
      (t1_rel_err +. t2_rel_err +. eps, t1_rel_err ++. t2_rel_err ++. eps)
    else
      (* Relative error for multiplication *)
      ( eps
        +. (t1_rel_err +. t2_rel_err +. (t1_rel_err *. t2_rel_err))
           *. (one +. eps),
        eps
        ++. (t1_rel_err ++. t2_rel_err ++. (t1_rel_err **. t2_rel_err))
            **. (one ++. eps) )
  in
  let cst_err, cst_err_simp =
    if is_uadd_ls uop || is_usub_ls uop then
      (* Constant error for addition and sustraction *)
      ( ((one +. eps +. t2_rel_err) *. t1_cst_err)
        +. ((one +. eps +. t1_rel_err) *. t2_cst_err),
        ((one ++. eps ++. t2_rel_err) **. t1_cst_err)
        ++. ((one ++. eps ++. t1_rel_err) **. t2_cst_err) )
    else
      (* Constant error for multiplication *)
      ( (((t2_cst_err +. (t2_cst_err *. t1_rel_err)) *. t1')
        +. ((t1_cst_err +. (t1_cst_err *. t2_rel_err)) *. t2')
        +. (t1_cst_err *. t2_cst_err))
        *. (one +. eps)
        +. eta,
        ((one ++. eps) **. (t2_cst_err ++. (t2_cst_err **. t1_rel_err)))
        **. t1'
        ++. ((one ++. eps) **. (t1_cst_err ++. (t1_cst_err **. t2_rel_err)))
            **. t2'
        ++. ((one ++. eps) **. t1_cst_err **. t2_cst_err)
        ++. eta )
  in
  let total_err =
    if is_uadd_ls uop || is_usub_ls uop then
      (rel_err *. (t1' +. t2')) +. cst_err
    else
      (rel_err *. (t1' *. t2')) +. cst_err
  in
  let total_err_simp =
    if is_uadd_ls uop || is_usub_ls uop then
      (rel_err **. (t1' ++. t2')) ++. cst_err
    else
      (rel_err **. t1' **. t2') ++. cst_err
  in
  let exact, exact' =
    if is_uadd_ls uop then
      (exact_t1 +. exact_t2, t1' ++. t2')
    else if is_usub_ls uop then
      (exact_t1 -. exact_t2, t1' ++. t2')
    else
      (exact_t1 *. exact_t2, t1' **. t2')
  in
  let info = add_fw_error info r (exact, rel_err_simp, exact', cst_err_simp) in
  let str = string_of_ufloat_type_and_op ts uop in
  let strat =
    Sapply_trans
      ( "apply",
        [
          str ^ "_error_propagation";
          "with";
          sprintf "%s,%s" (term_to_str t1) (term_to_str t2);
        ],
        [
          strat_for_t1;
          strat_for_t2;
          default_strat ();
          default_strat ();
          default_strat ();
          default_strat ();
          default_strat ();
          default_strat ();
          default_strat ();
        ] )
  in
  (* We want to apply the propagation lemma on a term of the form `t1 uop t2`.
     It is possible for the term r to have a different form, for instance if we
     have in our context `t = t1 uop t2` then r will be `t`. In this case
     applying the lemma will fail because the transformation "apply" may not be
     able to resolve the equality. We prefer to not manage these cases and let
     the provers resolve these kind of trivial equalities, therefore we don't
     apply the lemma on r but on `t1 uop t2`. *)
  (* let r' = t_app_infer uop [ t1; t2 ] in *)
  (* let f = abs (to_real r' -. exact) <=. total_err in *)
  let f = abs (to_real r -. exact) <=. total_err in
  if t_equal total_err total_err_simp then
    (info, f, strat)
  else
    let f_simp = abs (to_real r -. exact) <=. total_err_simp in
    ( info,
      f_simp,
      Sapply_trans ("assert", [ term_to_str f ], [ strat; default_strat () ]) )

(* Error on a IEEE op when no propagation is needed (eg. we don't have a forward
   error on t1 nor t2) *)
let basic_uop_error info uop r t1 t2 =
  let ts = get_ts r in
  let eps = eps ts in
  let eta = eta ts in
  let to_real = to_real ts in
  let exact =
    if is_uadd_ls uop then
      to_real t1 +. to_real t2
    else if is_usub_ls uop then
      to_real t1 -. to_real t2
    else
      to_real t1 *. to_real t2
  in
  let cst_err =
    if is_umul_ls uop then
      eta
    else
      zero
  in
  let total_err = (eps *. abs exact) ++. cst_err in
  let info = add_fw_error info r (exact, eps, abs exact, cst_err) in
  let f = abs (to_real r -. exact) <=. total_err in
  (info, f, default_strat ())

(* Generates the formula and the strat for the forward error of `r = uop t1
   t2` *)
let use_ieee_thms info uop r t1 t2 strat_for_t1 strat_for_t2 =
  let t1_info = get_info info t1 in
  let t2_info = get_info info t2 in
  match (t1_info.error, t2_info.error) with
  (* No propagation needed, we use the basic lemma *)
  | None, None -> basic_uop_error info uop r t1 t2
  (* We have an error on at least one of t1 and t2, use the propagation lemma *)
  | _ ->
    let to_real = to_real (get_ts r) in
    let combine_errors = combine_uop_errors info uop in
    let combine_errors =
      match t1_info.error with
      | None -> combine_errors t1 (to_real t1) zero (abs (to_real t1)) zero
      | Some (exact_t1, rel_err, t1', cst_err) ->
        combine_errors t1 exact_t1 rel_err t1' cst_err
    in
    let combine_errors =
      match t2_info.error with
      | None -> combine_errors t2 (to_real t2) zero (abs (to_real t2)) zero
      | Some (exact_t2, rel_err, t2', cst_err) ->
        combine_errors t2 exact_t2 rel_err t2' cst_err
    in
    combine_errors r strat_for_t1 strat_for_t2

(* The lemmas for error propagation on known functions use the higher order
   symbol '@'. To apply these lemmas, we need to transform terms of the form `fn
   a b c ...` into terms of the form `(...(((fn @ a) @ b) @ c) @ ...)` *)
let rec apply_higher_order_sym ls_defs t =
  match t.t_node with
  | Tapp (ls, []) -> (
    try
      let t = Mls.find ls ls_defs in
      apply_higher_order_sym ls_defs t
    with
    | Not_found -> t)
  | Tapp (ls, l) ->
    let tys = List.map (fun t -> Option.get t.t_ty) l in
    let t1 = t_app_partial ls [] tys (Some (Option.get t.t_ty)) in
    List.fold_left (fun t' t -> t_app_infer fs_func_app [ t'; t ]) t1 l
  | _ -> t

(* Returns None if the function is unsupported by the strategy. Otherwise,
   returns its symbol as well as its arguments. *)
let get_known_fn_and_args t x =
  match x.t_node with
  | Tapp (ls, args)
    when ls_equal ls !!symbols.log || ls_equal ls !!symbols.exp
         || ls_equal ls !!symbols.log2
         || ls_equal ls !!symbols.log10
         || ls_equal ls !!symbols.sin || ls_equal ls !!symbols.cos ->
    let args =
      List.map
        (fun arg ->
          match arg.t_node with
          | Tapp (ls, [ t ]) when is_to_real_ls ls -> t
          | _ -> arg)
        args
    in
    Some (ls, args)
  | Tapp (sum_ls, [ fn; i; j ]) when ls_equal sum_ls !!symbols.sum -> (
    let real_fun = real_fun (get_ts t) in
    match fn.t_node with
    | Tapp (ls, [ fn ]) when ls_equal ls real_fun -> Some (sum_ls, [ fn; i; j ])
    | Tapp (ls, _) when ls_equal ls real_fun -> None
    | _ -> None)
  | _ -> None

(* Returns the forward error formula associated with the propagation lemma of
   the function `fn` *)
let get_fn_errs info fn app_approx arg_approx =
  let exact_arg, arg_rel_err, arg', arg_cst_err =
    Option.get (get_info info.terms_info arg_approx).error
  in
  let _, fn_rel_err, _, fn_cst_err =
    Option.get (get_info info.terms_info app_approx).error
  in
  if ls_equal fn !!symbols.exp then
    let cst_err = fn_cst_err in
    let cst_err_simp = fn_cst_err in
    let a = fs_app fn [ (arg_rel_err *. arg') +. arg_cst_err ] ty_real in
    let a_simp = fs_app fn [ (arg_rel_err **. arg') ++. arg_cst_err ] ty_real in
    let rel_err = fn_rel_err +. ((a -. one) *. (one +. fn_rel_err)) in
    let rel_err_simp =
      fn_rel_err ++. ((a_simp --. one) **. (one ++. fn_rel_err))
    in
    ( rel_err,
      rel_err_simp,
      cst_err,
      cst_err_simp,
      fs_app fn [ exact_arg ] ty_real,
      3 )
  else if
    ls_equal fn !!symbols.log || ls_equal fn !!symbols.log2
    || ls_equal fn !!symbols.log10
  then
    let a =
      fs_app fn
        [ one -. (((arg_rel_err *. arg') +. arg_cst_err) /. exact_arg) ]
        ty_real
    in
    let a_simp =
      if t_equal exact_arg arg' || t_equal (abs exact_arg) arg' then
        fs_app fn
          [ one --. (arg_rel_err ++. (arg_cst_err //. exact_arg)) ]
          ty_real
      else
        fs_app fn
          [ one --. (((arg_rel_err **. arg') ++. arg_cst_err) //. exact_arg) ]
          ty_real
    in
    let cst_err = (minus a *. (one +. fn_rel_err)) +. fn_cst_err in
    let cst_err_simp =
      (minus_simp a_simp **. (one ++. fn_rel_err)) ++. fn_cst_err
    in
    let rel_err = fn_rel_err in
    ( rel_err,
      rel_err,
      cst_err,
      cst_err_simp,
      abs (fs_app fn [ exact_arg ] ty_real),
      4 )
  else if ls_equal fn !!symbols.sin || ls_equal fn !!symbols.cos then
    let cst_err =
      (((arg_rel_err *. arg') +. arg_cst_err) *. (one +. fn_rel_err))
      +. fn_cst_err
    in
    let cst_err_simp =
      (((arg_rel_err **. arg') ++. arg_cst_err) **. (one ++. fn_rel_err))
      ++. fn_cst_err
    in
    let rel_err = fn_rel_err in
    ( rel_err,
      rel_err,
      cst_err,
      cst_err_simp,
      abs (fs_app fn [ exact_arg ] ty_real),
      3 )
  else
    assert false

(* Returns the forward error formula and the strat associated with the
   application of the propagation lemma for `fn`. The argument `strat`
   corresponds to the strat that is used to prove the error on `arg_approx` (the
   argument of the function) *)
let apply_fn_thm info fn app_approx arg_approx strat =
  let exact_arg, _, _, _ =
    Option.get (get_info info.terms_info arg_approx).error
  in
  let to_real = to_real (get_ts app_approx) in
  let exact_app = fs_app fn [ exact_arg ] ty_real in
  let fn_str = fn.ls_name.id_string in
  let ty_str = string_of_ufloat_type (get_ts app_approx) in
  let rel_err, rel_err_simp, cst_err, cst_err_simp, app', nb =
    get_fn_errs info fn app_approx arg_approx
  in
  let strat =
    Sapply_trans
      ( "apply",
        [ sprintf "%s_%s_error_propagation" fn_str ty_str ],
        [ strat ] @ List.init nb (fun _ -> Sdo_nothing) )
  in
  let total_err = (rel_err *. app') +. cst_err in
  let total_err_simp = (app' **. rel_err_simp) ++. cst_err_simp in
  let term_info =
    add_fw_error info.terms_info app_approx
      (exact_app, rel_err_simp, app', cst_err_simp)
  in
  let t_func_app = apply_higher_order_sym info.ls_defs app_approx in
  let left = abs (to_real t_func_app -. exact_app) in
  let s =
    Sapply_trans
      ( "assert",
        [ term_to_str (left <=. total_err) ],
        [ strat; default_strat () ] )
  in
  let left = abs (to_real app_approx -. exact_app) in
  if t_equal total_err total_err_simp then
    (term_info, Some (left <=. total_err), s)
  else
    ( term_info,
      Some (left <=. total_err_simp),
      Sapply_trans
        ("assert", [ term_to_str (left <=. total_err) ], [ s; default_strat () ])
    )

(* Returns the forward error formula and the strat associated with the
   application of the propagation lemma for the sum. *)
let apply_sum_thm info sum_approx _fn_approx (fn, i, j) =
  let _, sum_rel_err, sum'', sum_cst_err =
    Option.get (get_info info.terms_info sum_approx).error
  in
  let f'' =
    match sum''.t_node with
    | Tapp (_, [ f''; _; _ ]) -> f''
    | _ -> assert false
  in
  let _, _, exact_fn, fn_rel_err, fn', fn_cst_err = Mls.find fn info.fns_info in
  let to_real = to_real (get_ts sum_approx) in
  let exact_sum = fs_app !!symbols.sum [ exact_fn; i; j ] ty_real in
  let sum' = fs_app !!symbols.sum [ fn'; i; j ] ty_real in
  let ty_str = string_of_ufloat_type (get_ts sum_approx) in
  let rel_err = fn_rel_err +. (sum_rel_err *. (one +. fn_rel_err)) in
  let rel_err_simp = fn_rel_err ++. (sum_rel_err **. (one ++. fn_rel_err)) in
  let cst_err =
    (fn_cst_err *. from_int j *. (one +. sum_rel_err)) +. sum_cst_err
  in
  let cst_err_simp =
    (fn_cst_err **. from_int j **. (one ++. sum_rel_err)) ++. sum_cst_err
  in
  let strat =
    Sapply_trans
      ( "apply",
        [
          sprintf "sum_%s_error_propagation" ty_str;
          "with";
          sprintf "%s, %s" fn.ls_name.id_string (term_to_str f'');
        ],
        List.init 5 (fun _ -> Sdo_nothing) )
  in
  let total_err = (rel_err *. sum') +. cst_err in
  let total_err_simp = (sum' **. rel_err_simp) ++. cst_err_simp in
  let term_info =
    add_fw_error info.terms_info sum_approx
      (exact_sum, rel_err_simp, sum', cst_err_simp)
  in
  let t_func_app = apply_higher_order_sym info.ls_defs sum_approx in
  let left = abs (to_real t_func_app -. exact_sum) in
  let s =
    Sapply_trans
      ( "assert",
        [ term_to_str (left <=. total_err) ],
        [ strat; default_strat () ] )
  in
  let left = abs (to_real sum_approx -. exact_sum) in
  if t_equal total_err total_err_simp then
    (term_info, Some (left <=. total_err), s)
  else
    ( term_info,
      Some (left <=. total_err_simp),
      Sapply_trans
        ("assert", [ term_to_str (left <=. total_err) ], [ s; default_strat () ])
    )

let use_known_thm info app_approx fn args strats =
  if
    (* Nothing to do if none of the args have a forward error *)
    not
      (List.exists
         (fun arg ->
           match (get_info info.terms_info arg).error with
           | None -> false
           | Some _ -> true)
         args)
  then
    (info.terms_info, None, List.hd strats)
  else if
    ls_equal fn !!symbols.exp || ls_equal fn !!symbols.log
    || ls_equal fn !!symbols.log2
    || ls_equal fn !!symbols.log10
    || ls_equal fn !!symbols.sin || ls_equal fn !!symbols.cos
  then
    apply_fn_thm info fn app_approx (List.hd args) (List.hd strats)
  else
    failwith (asprintf "Unsupported fn symbol '%a'" Pretty.print_ls fn)

(* Recursively unfold the definition of `t` if it has one. Stops when we find an
   error that we can use *)
let update_term_info info t =
  let t_info = get_info info.terms_info t in
  let rec recurse t' =
    let t'_info = get_info info.terms_info t' in
    match t'_info.ieee_op with
    | None -> (
      match t'_info.error with
      | None -> (
        match t'.t_node with
        | Tapp (ls, []) ->
          if Mls.mem ls info.ls_defs then
            recurse (Mls.find ls info.ls_defs)
          else
            t_info
        | Tapp (ls, args) when is_uop ls ->
          { t_info with ieee_op = Some (ls, args) }
        | _ -> t_info)
      | Some _ as error -> { t_info with error })
    | Some _ as ieee_op -> { t_info with ieee_op }
  in
  recurse t

(*
 * Generate error formulas recursively for a term `t` using propagation lemmas.
 * This is recursive because if `t` is an approximation of a term `u` which
 * itself is an approximation of a term `v`, we first compute a formula for the
 * approximation of `v` by `u` and we combine it with the formula we already
 * have of the approximation of `u` by `t` to get a formula relating `t` to `v`.
 *)
let rec get_error_fmlas info t =
  let t_info = update_term_info info t in
  let get_strat f s =
    match f with
    | Some f ->
      Sapply_trans ("assert", [ term_to_str f ], [ s; default_strat () ])
    | None -> s
  in
  match t_info.ieee_op with
  (* `t` is the result of the IEEE minus operation *)
  | Some (ieee_op, [ x ]) when is_uminus_ls ieee_op -> (
    let terms_info, fmla, strat_for_x = get_error_fmlas info x in
    let strat = get_strat fmla strat_for_x in
    let ts = get_ts t in
    let to_real = to_real ts in
    let x_info = get_info terms_info x in
    match x_info.error with
    (* No propagation needed *)
    | None -> (terms_info, None, strat)
    (* The error doesn't change since the float minus operation is exact *)
    | Some (exact_x, rel_err, x', cst_err) ->
      let exact = minus exact_x in
      let f = abs (to_real t -. exact) <=. (rel_err **. x') ++. cst_err in
      let terms_info =
        add_fw_error terms_info t (exact, rel_err, x', cst_err)
      in
      (terms_info, Some f, strat))
  (* `t` is the result of an IEEE addition/sustraction/multiplication *)
  | Some (ieee_op, [ t1; t2 ]) ->
    (* Get error formulas on subterms `t1` and `t2` *)
    let terms_info, fmla1, strat_for_t1 = get_error_fmlas info t1 in
    let terms_info, fmla2, strat_for_t2 =
      get_error_fmlas { info with terms_info } t2
    in
    let strat_for_t1 = get_strat fmla1 strat_for_t1 in
    let strat_for_t2 = get_strat fmla2 strat_for_t2 in
    let terms_info, f, strats =
      use_ieee_thms terms_info ieee_op t t1 t2 strat_for_t1 strat_for_t2
    in
    (terms_info, Some f, strats)
  (* `t` is the result of an other IEEE operation *)
  | Some _ -> (info.terms_info, None, default_strat ())
  | None -> (
    match t_info.error with
    (* `t` has a forward error, we look if it is the result of the approximation
       of a known function, in which case we use the function's propagation
       lemma to compute an error bound *)
    | Some (x, _, _, _) -> (
      match get_known_fn_and_args t x with
      | Some (ls, [ fn; i; j ]) when ls_equal ls !!symbols.sum -> (
        match fn.t_node with
        | Tapp (fn, []) ->
          if Mls.mem fn info.fns_info then
            apply_sum_thm info t ls (fn, i, j)
          else
            (info.terms_info, None, default_strat ())
        | _ -> (info.terms_info, None, default_strat ()))
      | Some (fn, args) ->
        (* First we compute the potential forward errors of the function args *)
        let info, strats =
          List.fold_left
            (fun (info, l) t ->
              let terms_info, f, s = get_error_fmlas info t in
              let s =
                match f with
                | None -> s
                | Some f ->
                  Sapply_trans
                    ("assert", [ term_to_str f ], [ s; default_strat () ])
              in
              ({ info with terms_info }, s :: l))
            (info, []) args
        in
        use_known_thm info t fn args (List.rev strats)
      | None -> (info.terms_info, None, default_strat ()))
    | None -> (info.terms_info, None, default_strat ()))

let parse_error is_match exact t =
  (* If it we don't find a "relative" error, then we have an absolute error of
     `t` *)
  let abs_err = (exact, zero, zero, t) in
  let rec parse t =
    if is_match t then
      ((exact, one, t, zero), true)
    else
      match t.t_node with
      | Tapp (_ls, [ t1; t2 ]) when is_add_ls _ls ->
        let (a, factor, a', cst), _ = parse t1 in
        if is_zero factor then
          let (a, factor, a', cst), _ = parse t2 in
          if is_zero factor then
            (abs_err, false)
          else
            (* FIXME: we should combine the factor of t1 and factor of t2 *)
            ((a, factor, a', cst ++. t1), false)
        else
          ((a, factor, a', cst ++. t2), false)
      | Tapp (_ls, [ t1; t2 ]) when is_sub_ls _ls ->
        let (a, factor, a', cst), _ = parse t1 in
        if is_zero factor then
          (abs_err, false)
        else
          ((a, factor, a', cst --. t2), false)
      | Tapp (_ls, [ t1; t2 ]) when is_mul_ls _ls ->
        let (a, factor, a', cst), is_factor = parse t1 in
        if is_zero factor then
          let (a, factor, a', cst), is_factor = parse t2 in
          if is_zero factor then
            (abs_err, false)
          else if is_factor then
            ((a, factor **. t1, a', cst), true)
          else
            ((a, factor, a', cst **. t2), false)
        else if is_factor then
          ((a, factor **. t2, a', cst), true)
        else
          ((a, factor, a', cst **. t2), false)
      | _ -> (abs_err, false)
  in
  fst (parse t)

(* Parse `|f i - exact_f i| <= C`.
 * We try to decompose `C` to see if it has the form `A (f' i) + B` where
 * |f i| <= f' i for i in a given range
 *)
let parse_fn_error i exact_fn c =
  let rec is_match t =
    let extract_fn_and_args fn l =
      if ls_equal fn fs_func_app then
        match (List.hd l).t_node with
        | Tapp (fn, []) -> (fn, List.tl l)
        | _ -> (fn, [])
      else
        (fn, l)
    in
    match t.t_node with
    | Tapp (ls, [ t' ]) when is_abs_ls ls && is_match t' -> true
    | Tapp (fn', l) -> (
      let _, args = extract_fn_and_args fn' l in
      match args with
      | [ i' ] when t_equal i i' -> true
      | _ -> false)
    | _ -> false
  in
  parse_error is_match exact_fn c

(* Parse `|x_approx - x| <= C`.
 * We try to decompose `C` to see if it has the form `Ax' + B` where |x| <= x' *)
let parse_error x c =
  let is_sum, _f, i, j =
    match x.t_node with
    | Tapp (ls, [ f; i; j ]) when ls_equal ls !!symbols.sum ->
      (true, Some f, Some i, Some j)
    | _ -> (false, None, None, None)
  in
  let is_match t =
    t_equal t x
    ||
    match t.t_node with
    | Tapp (ls, [ t' ]) when is_abs_ls ls -> (
      if t_equal t' x then
        true
      else
        match t'.t_node with
        | Tapp (ls, [ _f'; i'; j' ])
          when ls_equal ls !!symbols.sum && is_sum
               && t_equal i' (Option.get i)
               && t_equal j' (Option.get j) ->
          true
        | _ -> false)
    | Tapp (ls, [ _f'; i'; j' ])
      when ls_equal ls !!symbols.sum && is_sum
           && t_equal i' (Option.get i)
           && t_equal j' (Option.get j) ->
      true
    | _ -> false
  in
  parse_error is_match x c

let is_var_equal t vs =
  match t.t_node with
  | Tvar vs' when vs_equal vs vs' -> true
  | _ -> false

(* Looks for |to_real x - exact_x| <= C. *)
let parse_ineq t =
  match t.t_node with
  | Tapp (ls, [ t; c ]) when is_ineq_ls ls -> (
    match t.t_node with
    | Tapp (ls, [ t ]) when is_abs_ls ls -> (
      match t.t_node with
      | Tapp (ls, [ x; exact_x ]) when is_sub_ls ls -> (
        match x.t_node with
        | Tapp (ls, [ x ]) when is_to_real_ls ls -> Some (x, exact_x, c)
        | _ -> None)
      | _ -> None)
    | _ -> None)
  | _ -> None

(* Looks for `forall i. P -> |to_real (fn i) - exact_fn i| <= A(fn' i) + B` (or
   the same formula without the hypothesis), with `i` an integer. We also match
   on a potential hypothesis P because usually there is a hypothesis on the
   bounds of i. A forward error on a function of type (int -> real) is can be
   used for sum error propagation *)
let collect_in_quant info q =
  let vs, _, t = t_open_quant q in
  match vs with
  | [ i ] when ty_equal i.vs_ty ty_int -> (
    let t =
      match t.t_node with
      | Tbinop (Timplies, _, t) -> t
      | _ -> t
    in
    match parse_ineq t with
    | Some (x, exact_x, c) -> (
      match (x.t_node, exact_x.t_node) with
      | Tapp (fn, l), Tapp (exact_fn, l') -> (
        let extract_fn_and_args fn l =
          if ls_equal fn fs_func_app then
            match (List.hd l).t_node with
            | Tapp (fn, []) -> (fn, List.tl l)
            | _ -> (fn, [])
          else
            (fn, l)
        in
        let fn, args = extract_fn_and_args fn l in
        let exact_fn, args' = extract_fn_and_args exact_fn l' in
        match (args, args') with
        | [ i' ], [ i'' ] when is_var_equal i' i && is_var_equal i'' i -> (
          let _, rel_err, fn_app', cst_err = parse_fn_error i' exact_fn c in
          match fn_app'.t_node with
          | Tapp (fn'', args) ->
            let fn' = fst (extract_fn_and_args fn'' args) in
            let fns_info =
              Mls.add fn
                ( None,
                  None,
                  t_app_infer exact_fn [],
                  rel_err,
                  t_app_infer fn' [],
                  cst_err )
                info.fns_info
            in
            { info with fns_info }
          | _ -> info)
        | _ -> info)
      | _ -> info)
    | _ -> info)
  | _ -> info

let rec collect info f =
  match f.t_node with
  | Tbinop (Tand, f1, f2) ->
    let info = collect info f1 in
    collect info f2
  | Tapp (ls, [ _; _ ]) when is_ineq_ls ls ->
      (* term of the form x op y where op is an inequality "<" or "<=" over reals
         FIXME: we should handle ">" and ">=" as well
      *)
      (
    match parse_ineq f with
    | Some (x, exact_x, c) ->
      let error_fmla = parse_error exact_x c in
      let terms_info = add_fw_error info.terms_info x error_fmla in
      { info with terms_info }
    | _ -> info)
  (* `r = uop args` or `uop args = r` *)
  | Tapp (ls, [ t1; t2 ]) when ls_equal ls ps_equ -> (
    match t1.t_node with
    | Tapp (ls, args) when is_uop ls ->
      let terms_info = add_ieee_op info.terms_info ls t2 args in
      { info with terms_info }
    | _ -> (
      match t2.t_node with
      | Tapp (ls, args) when is_uop ls ->
        let terms_info = add_ieee_op info.terms_info ls t1 args in
        { info with terms_info }
      | _ -> info))
  | Tquant (Tforall, tq) ->
    (* Collect potential error on function (for sum propagation lemma) *)
    collect_in_quant info tq
  | _ -> info

(*
 * We look for relevant axioms in the task, and we add corresponding
 * inequalities to `info`.
 * The formulas we look for have one of the following structures :
 * - `|to_real x - exact_x| <= A` : fw error on `x`
 * - `r = t1 uop t2` : `r` is the result of an IEEE operation on `t1` and `t2`
 * - `forall (i:int). P -> |to_real (f i) - exact_f i| <= A` : fw error on `f`
 * - `forall (i:int). |to_real (f i) - exact_f i| <= A` : fw error on `f`
 *
 * We also look for definitions of the form `r = t1 uop t2`
 *)
let collect_info info d =
  match d.d_node with
  | Dprop (kind, _pr, f) when kind = Paxiom || kind = Plemma -> collect info f
  | Dlogic defs ->
    let ls_defs =
      List.fold_left
        (fun info (ls, ls_def) ->
          match ls.ls_value with
          | Some ty when is_ty_float ty ->
            let _vsl, t = open_ls_defn ls_def in
            Mls.add ls t info
          | _ -> info)
        info.ls_defs defs
    in
    { info with ls_defs }
  | _ -> info

let init_symbols env printer =
  let real = Env.read_theory env [ "real" ] "Real" in
  let lt = ns_find_ls real.th_export [ Ident.op_infix "<" ] in
  let le = ns_find_ls real.th_export [ Ident.op_infix "<=" ] in
  let real_infix = Env.read_theory env [ "real" ] "RealInfix" in
  let lt_infix = ns_find_ls real_infix.th_export [ Ident.op_infix "<." ] in
  let le_infix = ns_find_ls real_infix.th_export [ Ident.op_infix "<=." ] in
  let add = ns_find_ls real.th_export [ Ident.op_infix "+" ] in
  let sub = ns_find_ls real.th_export [ Ident.op_infix "-" ] in
  let mul = ns_find_ls real.th_export [ Ident.op_infix "*" ] in
  let _div = ns_find_ls real.th_export [ Ident.op_infix "/" ] in
  let minus = ns_find_ls real.th_export [ Ident.op_prefix "-" ] in
  let add_infix = ns_find_ls real_infix.th_export [ Ident.op_infix "+." ] in
  let sub_infix = ns_find_ls real_infix.th_export [ Ident.op_infix "-." ] in
  let mul_infix = ns_find_ls real_infix.th_export [ Ident.op_infix "*." ] in
  let div_infix = ns_find_ls real_infix.th_export [ Ident.op_infix "/." ] in
  let minus_infix = ns_find_ls real_infix.th_export [ Ident.op_prefix "-." ] in
  let real_abs = Env.read_theory env [ "real" ] "Abs" in
  let abs = ns_find_ls real_abs.th_export [ "abs" ] in
  let real_from_int = Env.read_theory env [ "real" ] "FromInt" in
  let from_int = ns_find_ls real_from_int.th_export [ "from_int" ] in
  let sum_th = Env.read_theory env [ "real" ] "Sum" in
  let sum = ns_find_ls sum_th.th_export [ "sum" ] in
  let exp_log_th = Env.read_theory env [ "real" ] "ExpLog" in
  let exp = ns_find_ls exp_log_th.th_export [ "exp" ] in
  let log = ns_find_ls exp_log_th.th_export [ "log" ] in
  let log2 = ns_find_ls exp_log_th.th_export [ "log2" ] in
  let log10 = ns_find_ls exp_log_th.th_export [ "log10" ] in
  let trigo_th = Env.read_theory env [ "real" ] "Trigonometry" in
  let sin = ns_find_ls trigo_th.th_export [ "sin" ] in
  let cos = ns_find_ls trigo_th.th_export [ "cos" ] in
  let usingle = Env.read_theory env [ "ufloat" ] "USingle" in
  let udouble = Env.read_theory env [ "ufloat" ] "UDouble" in
  let usingle_lemmas = Env.read_theory env [ "ufloat" ] "USingleLemmas" in
  let udouble_lemmas = Env.read_theory env [ "ufloat" ] "UDoubleLemmas" in
  let mk_ufloat_symbols th th_lemmas ty =
    let f th s =
      try ns_find_ls th.th_export [ s ] with
      | Not_found -> failwith (Format.sprintf "Symbol %s not found" s)
    in
    {
      ufloat_type = ns_find_ts th.th_export [ ty ];
      to_real = f th "to_real";
      uadd = f th "uadd";
      usub = f th "usub";
      umul = f th "umul";
      udiv = f th "udiv";
      uminus = f th "uminus";
      uadd_infix = f th (Ident.op_infix "++.");
      usub_infix = f th (Ident.op_infix "--.");
      umul_infix = f th (Ident.op_infix "**.");
      udiv_infix = f th (Ident.op_infix "//.");
      uminus_prefix = f th (Ident.op_prefix "--.");
      eps = fs_app (f th "eps") [] ty_real;
      eta = fs_app (f th "eta") [] ty_real;
      real_fun = f th_lemmas "real_fun";
    }
  in
  let usingle_symbols = mk_ufloat_symbols usingle usingle_lemmas "usingle" in
  let udouble_symbols = mk_ufloat_symbols udouble udouble_lemmas "udouble" in
  symbols :=
    Some
      {
        add;
        sub;
        mul;
        _div;
        minus;
        sum;
        add_infix;
        sub_infix;
        mul_infix;
        div_infix;
        minus_infix;
        lt;
        lt_infix;
        le;
        le_infix;
        abs;
        exp;
        log;
        log2;
        log10;
        sin;
        cos;
        from_int;
        usingle_symbols;
        udouble_symbols;
        ident_printer = printer.Trans.printer;
        tv_printer = printer.Trans.aprinter;
      }

let numeric env task =
  let naming_table = Args_wrapper.build_naming_tables task in
  init_symbols env naming_table;
  let printer = Args_wrapper.build_naming_tables task in
  (* Update the printer at each call, but not the symbols *)
  symbols :=
    Some
      {
        !!symbols with
        ident_printer = printer.Trans.printer;
        tv_printer = printer.Trans.aprinter;
      };
  (* We start by collecting infos from the hypotheses of the task *)
  let info =
    List.fold_left collect_info
      { terms_info = Mterm.empty; fns_info = Mls.empty; ls_defs = Mls.empty }
      (task_decls task)
  in
  (* For each float `x` of the goal, we try to compute a formula of the form `|x
     - exact_x| <= A x' + B` where `exact_x` is the real value which is
     approximated by the float `x` and `|exact_x| <= x'`. For this, forward
     error propagation is performed using propagation lemmas of the ufloat
     stdlib with the data contained in `info`. For each new formula created, a
     proof tree is generated with the necessary steps to prove it. *)
  let goal = task_goal_fmla task in
  let floats = get_floats goal in
  let f, strats =
    List.fold_left
      (fun (f, l) t ->
        match get_error_fmlas info t with
        | _, None, _ -> (f, l)
        | _, Some f', s -> (t_and_simp f f', s :: l))
      (t_true, []) floats
  in
  if List.length strats = 0 then
    default_strat ()
  else if List.length strats = 1 then
    (* We only have an assertion on one float so no need to use split *)
    Sapply_trans ("assert", [ term_to_str f ], strats @ [ default_strat () ])
  else
    (* We assert a conjunction of formulas, one for each float in the goal for
       which we can use propagation lemmas. We have one strat for each of this
       goal so we split our assertions and prove each subgoal with the
       corresponding strat *)
    let s = Sapply_trans ("split_vc", [], List.rev strats) in
    Sapply_trans ("assert", [ term_to_str f ], [ s; default_strat () ])

let () =
  register_strat "forward_propagation" numeric
    ~desc:"Compute@ forward@ error@ of@ float@ computations."
