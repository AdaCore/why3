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

(* This type is used in order to keep a real formula with and without
   simplifications *)
type real_fmla = {
  full : term;
  simplified : term;
}

let rf t = { full = t; simplified = t }

(* A term 't' having a forward error 'e' means "|t - e.exact| <= e.rel *
   e.factor + e.cst", where |exact_t| <= t' *)
type forward_error = {
  exact : real_fmla;
  factor : real_fmla;
  rel : real_fmla;
  cst : real_fmla;
}

(* This type corresponds to the numeric info we have on a real/float term *)
type term_info = {
  error : forward_error option;
  (*
   * "Some (op, [x; y])" means that the term "t" is the result of the FP operation
   * "op" on "x" and "y"
   *)
  ieee_op : (lsymbol * term list) option;
}

type info = {
  terms_info : term_info Mterm.t;
  (* fns_info is used for the sum propagation lemma *)
  fns_info : forward_error Mls.t;
  (* ls_defs is used to store logic definitions *)
  ls_defs : term Mls.t;
}

let default_strat () = Sdo_nothing

let zero_term =
  t_const
    (Constant.ConstReal
       (Number.real_literal ~radix:10 ~neg:false ~int:"0" ~frac:"0" ~exp:None))
    ty_real

let one_term =
  t_const
    (Constant.ConstReal
       (Number.real_literal ~radix:10 ~neg:false ~int:"1" ~frac:"0" ~exp:None))
    ty_real

let is_zero t = t_equal zero_term t
let is_one t = t_equal one_term t

let abs_term t =
  match t.t_node with
  (* Don't add an abs symbol on top of another *)
  | Tapp (ls, [ _ ]) when ls_equal !!symbols.abs ls -> t
  | _ -> fs_app !!symbols.abs [ t ] ty_real

let abs t = { full = abs_term t.full; simplified = abs_term t.simplified }
let from_int_term t = fs_app !!symbols.from_int [ t ] ty_real

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
    zero_term
  else if is_one t1 then
    t2
  else if is_one t2 then
    t1
  else
    match (t1.t_node, t2.t_node) with
    | Tapp (ls1, [ t1 ]), Tapp (ls2, [ t2 ]) when is_abs_ls ls1 && is_abs_ls ls2
      ->
      abs_term (mul t1 t2)
    | _ -> mul t1 t2

let div_simp t1 t2 =
  if is_zero t1 then
    zero_term
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

let compose_fmla op op_simp x y =
  { full = op x.full y.full; simplified = op_simp x.simplified y.simplified }

let add_fmla x y = compose_fmla add add_simp x y
let sub_fmla x y = compose_fmla sub sub_simp x y
let mul_fmla x y = compose_fmla mul mul_simp x y
let div_fmla x y = compose_fmla div div_simp x y
let ( ++ ) x y = add_fmla x y
let ( -- ) x y = sub_fmla x y
let ( ** ) x y = mul_fmla x y
let ( // ) x y = div_fmla x y
let minus x = { full = minus x.full; simplified = minus_simp x.simplified }

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

let eps_term ieee_type =
  if ts_equal ieee_type !!symbols.usingle_symbols.ufloat_type then
    !!symbols.usingle_symbols.eps
  else if ts_equal ieee_type !!symbols.udouble_symbols.ufloat_type then
    !!symbols.udouble_symbols.eps
  else
    failwith (asprintf "Unsupported type %a" Pretty.print_ts ieee_type)

let eta_term ieee_type =
  if ts_equal ieee_type !!symbols.usingle_symbols.ufloat_type then
    !!symbols.usingle_symbols.eta
  else if ts_equal ieee_type !!symbols.udouble_symbols.ufloat_type then
    !!symbols.udouble_symbols.eta
  else
    failwith (asprintf "Unsupported type %a" Pretty.print_ts ieee_type)

let zero = rf zero_term
let one = rf one_term
let eps ieee_type = rf (eps_term ieee_type)
let eta ieee_type = rf (eta_term ieee_type)

let fs_app_fmla fs t ty =
  {
    full = fs_app fs (List.map (fun x -> x.full) t) ty;
    simplified = fs_app fs (List.map (fun x -> x.simplified) t) ty;
  }

let to_real_term ieee_type t =
  let to_real =
    if ts_equal ieee_type !!symbols.usingle_symbols.ufloat_type then
      !!symbols.usingle_symbols.to_real
    else if ts_equal ieee_type !!symbols.udouble_symbols.ufloat_type then
      !!symbols.udouble_symbols.to_real
    else
      failwith (asprintf "Unsupported type %a" Pretty.print_ts ieee_type)
  in
  fs_app to_real [ t ] ty_real

let to_real ieee_type t =
  {
    full = to_real_term ieee_type t.full;
    simplified = to_real_term ieee_type t.simplified;
  }

let from_int t =
  { full = from_int_term t.full; simplified = from_int_term t.simplified }

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

let generate_final info e r strat to_real =
  let total_err = (e.rel.full *. e.factor.full) +. e.cst.full in
  let total_err_simp =
    (e.rel.simplified **. e.factor.simplified) ++. e.cst.simplified
  in
  let f = abs_term (to_real r -. e.exact.full) <=. total_err in
  if t_equal total_err total_err_simp then
    (info, f, strat)
  else
    let f_simp = abs_term (to_real r -. e.exact.full) <=. total_err_simp in
    ( info,
      f_simp,
      Sapply_trans ("assert", [ term_to_str f ], [ strat; default_strat () ]) )

let generate_add e1 e2 eps =
  let rel = e1.rel ++ e2.rel ++ eps in
  let cst =
    ((one ++ eps ++ e2.rel) ** e1.cst) ++ ((one ++ eps ++ e1.rel) ** e2.cst)
  in
  { exact = e1.exact ++ e2.exact; factor = e1.factor ++ e2.factor; rel; cst }

let generate_mul e1 e2 eps eta =
  let rel = eps ++ ((e1.rel ++ e2.rel ++ (e1.rel ** e2.rel)) ** (one ++ eps)) in
  let cst =
    (((e2.cst ++ (e2.cst ** e1.rel)) ** e1.factor)
    ++ ((e1.cst ++ (e1.cst ** e2.rel)) ** e2.factor)
    ++ (e1.cst ** e2.cst))
    ** (one ++ eps)
    ++ eta
  in
  { exact = e1.exact ** e2.exact; factor = e1.factor ** e2.factor; rel; cst }

(* Error on an IEEE op when propagation is needed (eg. we have a forward error
   on t1 and/or on t2) *)
let generate_uop info uop t1 e1 t2 e2 r strat_for_t1 strat_for_t2 =
  let ts = get_ts r in
  let eps = eps ts in
  let eta = eta ts in
  let to_real = to_real_term ts in
  let e =
    if is_uadd_ls uop then
      generate_add e1 e2 eps
    else if is_usub_ls uop then
      let e = generate_add e1 e2 eps in
      { e with exact = e1.exact -- e2.exact }
    else if is_umul_ls uop then
      generate_mul e1 e2 eps eta
    else
      assert false
  in
  let info = add_fw_error info r e in
  let str = string_of_ufloat_type_and_op ts uop in
  let strat =
    Sapply_trans
      ( "apply",
        [
          str ^ "_error_propagation";
          "with";
          sprintf "%s,%s" (term_to_str t1) (term_to_str t2);
        ],
        [ strat_for_t1; strat_for_t2 ] @ List.init 7 (fun _ -> default_strat ())
      )
  in
  generate_final info e r strat to_real

(* Error on a IEEE op when no propagation is needed (eg. we don't have a forward
   error on t1 nor t2) *)
let basic_uop_error info uop r t1 t2 =
  let ts = get_ts r in
  let eps = eps ts in
  let eta = eta ts in
  let to_real = to_real ts in
  let t1 = rf t1 in
  let t2 = rf t2 in
  let exact =
    if is_uadd_ls uop then
      to_real t1 ++ to_real t2
    else if is_usub_ls uop then
      to_real t1 -- to_real t2
    else
      to_real t1 ** to_real t2
  in
  let cst =
    if is_umul_ls uop then
      eta
    else
      zero
  in
  let total_err = (eps ** abs exact) ++ cst in
  let info =
    add_fw_error info r { exact; rel = eps; factor = abs exact; cst }
  in
  let f =
    abs_term (to_real_term ts r -. exact.simplified) <=. total_err.simplified
  in
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
    let get_err_or_default t t_info =
      match t_info.error with
      | None ->
        {
          exact = to_real (rf t);
          rel = zero;
          factor = abs (to_real (rf t));
          cst = zero;
        }
      | Some e -> e
    in
    let e1 = get_err_or_default t1 t1_info in
    let e2 = get_err_or_default t2 t2_info in
    generate_uop info uop t1 e1 t2 e2 r strat_for_t1 strat_for_t2

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

let generate_sin_cos exact_fn exact e_arg e_app =
  let cst =
    (((e_arg.rel ** e_arg.factor) ++ e_arg.cst) ** (one ++ e_app.rel))
    ++ e_app.cst
  in
  let factor = abs (fs_app_fmla exact_fn [ e_arg.exact ] ty_real) in
  ({ exact; rel = e_app.rel; cst; factor }, 3)

let generate_exp exact_fn exact e_arg e_app =
  let a =
    fs_app_fmla exact_fn [ (e_arg.rel ** e_arg.factor) ++ e_arg.cst ] ty_real
  in
  let rel = e_app.rel ++ ((a -- one) ** (one ++ e_app.rel)) in
  let factor = fs_app_fmla exact_fn [ e_arg.exact ] ty_real in
  ({ exact; rel; cst = e_app.cst; factor }, 3)

let generate_log exact_fn exact e_arg e_app =
  let a =
    fs_app_fmla exact_fn
      [ one -- (((e_arg.rel ** e_arg.factor) ++ e_arg.cst) // e_arg.exact) ]
      ty_real
  in
  let a =
    if
      t_equal e_arg.exact.simplified e_arg.factor.simplified
      || t_equal (abs_term e_arg.exact.simplified) e_arg.factor.simplified
    then
      {
        a with
        simplified =
          fs_app exact_fn
            [
              one_term
              --. (e_arg.rel.simplified
                  ++. (e_arg.cst.simplified //. e_arg.exact.simplified));
            ]
            ty_real;
      }
    else
      a
  in
  let cst = (minus a ** (one ++ e_app.rel)) ++ e_app.cst in
  let factor = abs (fs_app_fmla exact_fn [ e_arg.exact ] ty_real) in
  ({ exact; rel = e_app.rel; cst; factor }, 4)

(* Returns the forward error formula associated with the propagation lemma of
   the function `exact_fn`. `app_approx` *)
let get_fn_errs info exact_fn exact e_arg e_app =
  if ls_equal exact_fn !!symbols.sin || ls_equal exact_fn !!symbols.cos then
    generate_sin_cos exact_fn exact e_arg e_app
  else if ls_equal exact_fn !!symbols.exp then
    generate_exp exact_fn exact e_arg e_app
  else if
    ls_equal exact_fn !!symbols.log
    || ls_equal exact_fn !!symbols.log2
    || ls_equal exact_fn !!symbols.log10
  then
    generate_log exact_fn exact e_arg e_app
  else
    assert false

(* Returns the forward error formula and the strat associated with the
   application of the propagation lemma for `fn`. The argument `strat`
   corresponds to the strat that is used to prove the error on `arg_approx` (the
   argument of the function) *)
let apply_fn_thm info fn app_approx arg_approx strat =
  let e_arg = Option.get (get_info info.terms_info arg_approx).error in
  let to_real = to_real_term (get_ts app_approx) in
  let exact = fs_app_fmla fn [ e_arg.exact ] ty_real in
  let fn_str = fn.ls_name.id_string in
  let ty_str = string_of_ufloat_type (get_ts app_approx) in
  let e_app = Option.get (get_info info.terms_info app_approx).error in
  let e, nb = get_fn_errs info fn exact e_arg e_app in
  let strat =
    Sapply_trans
      ( "apply",
        [ sprintf "%s_%s_error_propagation" fn_str ty_str ],
        [ strat ] @ List.init nb (fun _ -> Sdo_nothing) )
  in
  let term_info = add_fw_error info.terms_info app_approx e in
  let t_func_app = apply_higher_order_sym info.ls_defs app_approx in
  let left = abs_term (to_real t_func_app -. exact.simplified) in
  let total_err = (e.rel.full *. e.factor.full) +. e.cst.full in
  let total_err_simp =
    (e.rel.simplified *. e.factor.simplified) +. e.cst.simplified
  in
  let s =
    Sapply_trans
      ( "assert",
        [ term_to_str (left <=. total_err) ],
        [ strat; default_strat () ] )
  in
  let left = abs_term (to_real app_approx -. exact.simplified) in
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
  let e_sum = Option.get (get_info info.terms_info sum_approx).error in
  let f' =
    match e_sum.factor.full.t_node with
    | Tapp (_, [ f'; _; _ ]) -> f'
    | _ -> assert false
  in
  let e_fn = Mls.find fn info.fns_info in
  let to_real = to_real_term (get_ts sum_approx) in
  let exact = fs_app_fmla !!symbols.sum [ e_fn.exact; i; j ] ty_real in
  let factor = fs_app_fmla !!symbols.sum [ e_fn.factor; i; j ] ty_real in
  let ty_str = string_of_ufloat_type (get_ts sum_approx) in
  let rel = e_fn.rel ++ (e_sum.rel ** (one ++ e_fn.rel)) in
  let cst = (e_fn.cst ** from_int j ** (one ++ e_sum.rel)) ++ e_sum.cst in
  let strat =
    Sapply_trans
      ( "apply",
        [
          sprintf "sum_%s_error_propagation" ty_str;
          "with";
          sprintf "%s, %s" fn.ls_name.id_string (term_to_str f');
        ],
        List.init 5 (fun _ -> Sdo_nothing) )
  in
  let term_info =
    add_fw_error info.terms_info sum_approx { exact; rel; factor; cst }
  in
  let t_func_app = apply_higher_order_sym info.ls_defs sum_approx in
  let left = abs_term (to_real t_func_app -. exact.full) in
  let total_err = (rel.full *. factor.full) +. cst.full in
  let s =
    Sapply_trans
      ( "assert",
        [ term_to_str (left <=. total_err) ],
        [ strat; default_strat () ] )
  in
  let total_err_simp = (factor ** rel) ++ cst in
  let left = abs_term (to_real sum_approx -. exact.full) in
  if t_equal total_err total_err_simp.simplified then
    (term_info, Some (left <=. total_err), s)
  else
    ( term_info,
      Some (left <=. total_err_simp.simplified),
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
    let to_real = to_real_term ts in
    let x_info = get_info terms_info x in
    match x_info.error with
    (* No propagation needed *)
    | None ->
      (terms_info, None, strat)
      (* The error doesn't change since the float minus operation is exact *)
    | Some { exact; rel; factor; cst } ->
      let exact = minus exact in
      let f =
        abs_term (to_real t -. exact.full)
        <=. ((rel ** factor) ++ cst).simplified
      in
      let terms_info = add_fw_error terms_info t { exact; rel; factor; cst } in
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
    | Some e -> (
      match get_known_fn_and_args t e.exact.full with
      | Some (ls, [ fn; i; j ]) when ls_equal ls !!symbols.sum -> (
        match fn.t_node with
        | Tapp (fn, []) ->
          if Mls.mem fn info.fns_info then
            apply_sum_thm info t ls (fn, rf i, rf j)
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
  (* If it we don't find a "relative" error we have an absolute error of `t` *)
  let exact = rf exact in
  let e_default = { exact; rel = zero; factor = zero; cst = rf t } in
  let rec parse t =
    if is_match t then
      ({ exact; rel = one; factor = rf t; cst = zero }, true)
    else
      match t.t_node with
      | Tapp (ls, [ t1; t2 ]) when is_add_ls ls ->
        let e1, _ = parse t1 in
        if is_zero e1.rel.simplified then
          let e2, _ = parse t2 in
          if is_zero e2.rel.simplified then
            (e_default, false)
          else
            (* FIXME: we should combine the factor of t1 and factor of t2 *)
            ({ e2 with cst = e2.cst ++ rf t1 }, false)
        else
          ({ e1 with cst = e1.cst ++ rf t2 }, false)
      | Tapp (ls, [ t1; t2 ]) when is_sub_ls ls ->
        (* FIXME : should be the same as for addition *)
        let e1, _ = parse t1 in
        if is_zero e1.rel.simplified then
          (e_default, false)
        else
          ({ e1 with cst = e1.cst -- rf t2 }, false)
      | Tapp (ls, [ t1; t2 ]) when is_mul_ls ls ->
        let e1, is_factor = parse t1 in
        if is_zero e1.rel.simplified then
          let e2, is_factor = parse t2 in
          if is_zero e2.rel.simplified then
            (e_default, false)
          else if is_factor then
            ({ e2 with rel = e2.rel ** rf t1 }, true)
          else
            ({ e2 with cst = e2.cst ** rf t1 }, false)
        else if is_factor then
          ({ e1 with rel = e1.rel ** rf t2 }, true)
        else
          ({ e1 with cst = e1.cst ** rf t2 }, false)
      | _ -> (e_default, false)
  in
  fst (parse t)

(* Parse `|f i - exact_f i| <= C`.
 * We try to decompose `C` to see if it has the form `A (f' i) + B` where
 * |f i| <= f' i for i in a given range
 *)
let parse_fn_error i exact c =
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
  parse_error is_match exact c

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
          let e = parse_fn_error i' (t_app_infer exact_fn []) c in
          match e.factor.simplified.t_node with
          | Tapp (fn'', args) ->
            let fn' = fst (extract_fn_and_args fn'' args) in
            let fns_info =
              Mls.add fn
                { e with factor = rf (t_app_infer fn' []) }
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
  | Tapp (ls, [ _; _ ]) when is_ineq_ls ls -> (
    (* term of the form x op y where op is an inequality "<" or "<=" over reals
       FIXME: we should handle ">" and ">=" as well *)
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

let fw_propagation env task =
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
  register_strat "forward_propagation" fw_propagation
    ~desc:"Compute@ forward@ error@ of@ float@ computations."
