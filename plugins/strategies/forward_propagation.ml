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
  udiv_exact : lsymbol;
  uadd_infix : lsymbol;
  usub_infix : lsymbol;
  umul_infix : lsymbol;
  udiv_infix : lsymbol;
  uminus_prefix : lsymbol;
  udiv_exact_infix : lsymbol;
  eps : term;
  eta : term;
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
  exp : lsymbol;
  log : lsymbol;
  log2 : lsymbol;
  log10 : lsymbol;
  sin : lsymbol;
  cos : lsymbol;
  usingle_symbols : ufloat_symbols;
  udouble_symbols : ufloat_symbols;
  ident_printer : ident_printer;
  tv_printer : ident_printer;
}

let symbols = ref None
let ( !! ) s = Option.get !s

(* A term 't' having a forward error 'e' means "|t - e.exact| <= e.rel *
   e.factor + e.cst", where |exact_t| <= t' *)
type forward_error = {
  exact : term;
  factor : term;
  rel : term;
  cst : term;
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

let is_uexact_div_ls ls =
  ls_equal ls !!symbols.usingle_symbols.udiv_exact
  || ls_equal ls !!symbols.usingle_symbols.udiv_exact_infix
  || ls_equal ls !!symbols.udouble_symbols.udiv_exact
  || ls_equal ls !!symbols.udouble_symbols.udiv_exact_infix

let is_uop ls =
  is_uadd_ls ls || is_usub_ls ls || is_umul_ls ls || is_udiv_ls ls
  || is_uminus_ls ls || is_uexact_div_ls ls

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
(* TODO: Don't put duplicates in list !!! *)
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
    else if is_uexact_div_ls uop then
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
let combine_uop_errors info uop t1 e1 t2 e2 r strat_for_t1 strat_for_t2 =
  let ts = get_ts r in
  let eps = eps ts in
  let eta = eta ts in
  let to_real = to_real ts in
  let rel_err, rel_err_simp =
    if is_uadd_ls uop || is_usub_ls uop then
      (* Relative error for addition and sustraction *)
      (e1.rel +. e2.rel +. eps, e1.rel ++. e2.rel ++. eps)
    else
      (* Relative error for multiplication *)
      ( eps +. ((e1.rel +. e2.rel +. (e1.rel *. e2.rel)) *. (one +. eps)),
        eps ++. ((e1.rel ++. e2.rel ++. (e1.rel **. e2.rel)) **. (one ++. eps))
      )
  in
  let cst_err, cst_err_simp =
    if is_uadd_ls uop || is_usub_ls uop then
      (* Constant error for addition and sustraction *)
      ( ((one +. eps +. e2.rel) *. e1.cst) +. ((one +. eps +. e1.rel) *. e2.cst),
        ((one ++. eps ++. e2.rel) **. e1.cst)
        ++. ((one ++. eps ++. e1.rel) **. e2.cst) )
    else
      (* Constant error for multiplication *)
      ( (((e2.cst +. (e2.cst *. e1.rel)) *. e1.factor)
        +. ((e1.cst +. (e1.cst *. e2.rel)) *. e2.factor)
        +. (e1.cst *. e2.cst))
        *. (one +. eps)
        +. eta,
        (((one ++. eps) **. (e2.cst ++. (e2.cst **. e1.rel))) **. e1.factor)
        ++. (((one ++. eps) **. (e1.cst ++. (e1.cst **. e2.rel))) **. e2.factor)
        ++. ((one ++. eps) **. e1.cst **. e2.cst)
        ++. eta )
  in
  let total_err =
    if is_uadd_ls uop || is_usub_ls uop then
      (rel_err *. (e1.factor +. e2.factor)) +. cst_err
    else
      (rel_err *. (e1.factor *. e2.factor)) +. cst_err
  in
  let total_err_simp =
    if is_uadd_ls uop || is_usub_ls uop then
      (rel_err **. (e1.factor ++. e2.factor)) ++. cst_err
    else
      (rel_err **. e1.factor **. e2.factor) ++. cst_err
  in
  let exact, exact' =
    if is_uadd_ls uop then
      (e1.exact +. e2.exact, e1.factor ++. e2.factor)
    else if is_usub_ls uop then
      (e1.exact -. e2.exact, e1.factor ++. e2.factor)
    else
      (e1.exact *. e2.exact, e1.factor **. e2.factor)
  in
  let info =
    add_fw_error info r
      { exact; rel = rel_err_simp; factor = exact'; cst = cst_err_simp }
  in
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
  let info =
    add_fw_error info r { exact; rel = eps; factor = abs exact; cst = cst_err }
  in
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
    let get_err_or_default t t_info =
      match t_info.error with
      | None ->
        { exact = to_real t; rel = zero; factor = abs (to_real t); cst = zero }
      | Some e -> e
    in
    let e1 = get_err_or_default t1 t1_info in
    let e2 = get_err_or_default t2 t2_info in
    combine_uop_errors info uop t1 e1 t2 e2 r strat_for_t1 strat_for_t2

(* Returns None if the function is unsupported by the strategy. Otherwise,
   returns its symbol as well as its arguments. *)
let get_known_fn_and_args _t x =
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
  | _ -> None

(* Returns the forward error formula associated with the propagation lemma of
   the function `exact_fn`. `app_approx` *)
let get_fn_errs info exact_fn app_approx arg_approx =
  let e_arg = Option.get (get_info info.terms_info arg_approx).error in
  let e_app = Option.get (get_info info.terms_info app_approx).error in
  if ls_equal exact_fn !!symbols.exp then
    let cst_err = e_app.cst in
    let a =
      fs_app exact_fn [ (e_arg.rel *. e_arg.factor) +. e_arg.cst ] ty_real
    in
    let a_simp =
      fs_app exact_fn [ (e_arg.rel **. e_arg.factor) ++. e_arg.cst ] ty_real
    in
    let rel_err = e_app.rel +. ((a -. one) *. (one +. e_app.rel)) in
    let rel_err_simp =
      e_app.rel ++. ((a_simp --. one) **. (one ++. e_app.rel))
    in
    ( rel_err,
      rel_err_simp,
      cst_err,
      cst_err,
      fs_app exact_fn [ e_arg.exact ] ty_real,
      3 )
  else if
    ls_equal exact_fn !!symbols.log
    || ls_equal exact_fn !!symbols.log2
    || ls_equal exact_fn !!symbols.log10
  then
    let a =
      fs_app exact_fn
        [ one -. (((e_arg.rel *. e_arg.factor) +. e_arg.cst) /. e_arg.exact) ]
        ty_real
    in
    let a_simp =
      if
        t_equal e_arg.exact e_arg.factor
        || t_equal (abs e_arg.exact) e_arg.factor
      then
        fs_app exact_fn
          [ one --. (e_arg.rel ++. (e_arg.cst //. e_arg.exact)) ]
          ty_real
      else
        fs_app exact_fn
          [
            one
            --. (((e_arg.rel **. e_arg.factor) ++. e_arg.cst) //. e_arg.exact);
          ]
          ty_real
    in
    let cst_err = (minus a *. (one +. e_app.rel)) +. e_app.cst in
    let cst_err_simp =
      (minus_simp a_simp **. (one ++. e_app.rel)) ++. e_app.cst
    in
    let rel_err = e_app.rel in
    ( rel_err,
      rel_err,
      cst_err,
      cst_err_simp,
      abs (fs_app exact_fn [ e_arg.exact ] ty_real),
      4 )
  else if ls_equal exact_fn !!symbols.sin || ls_equal exact_fn !!symbols.cos
  then
    let cst_err =
      (((e_arg.rel *. e_arg.factor) +. e_arg.cst) *. (one +. e_app.rel))
      +. e_app.cst
    in
    let cst_err_simp =
      (((e_arg.rel **. e_arg.factor) ++. e_arg.cst) **. (one ++. e_app.rel))
      ++. e_app.cst
    in
    let rel_err = e_app.rel in
    ( rel_err,
      rel_err,
      cst_err,
      cst_err_simp,
      abs (fs_app exact_fn [ e_arg.exact ] ty_real),
      3 )
  else
    assert false

(* Returns the forward error formula and the strat associated with the
   application of the propagation lemma for `fn`. The argument `strat`
   corresponds to the strat that is used to prove the error on `arg_approx` (the
   argument of the function) *)
let apply_fn_thm info fn app_approx arg_approx strat =
  let e_arg = Option.get (get_info info.terms_info arg_approx).error in
  let to_real = to_real (get_ts app_approx) in
  let exact = fs_app fn [ e_arg.exact ] ty_real in
  let fn_str = fn.ls_name.id_string in
  let ty_str = string_of_ufloat_type (get_ts app_approx) in
  let rel_err, rel_err_simp, cst_err, cst_err_simp, app', nb =
    get_fn_errs info fn app_approx arg_approx
  in
  let strat =
    Sapply_trans
      ( "apply",
        [
          sprintf "%s_%s_error_propagation" fn_str ty_str;
          "with";
          sprintf "%s" (term_to_str arg_approx);
        ],
        [ strat ] @ List.init nb (fun _ -> Sdo_nothing) )
  in
  let total_err = (rel_err *. app') +. cst_err in
  let total_err_simp = (app' **. rel_err_simp) ++. cst_err_simp in
  let term_info =
    add_fw_error info.terms_info app_approx
      { exact; rel = rel_err_simp; factor = app'; cst = cst_err_simp }
  in
  let left = abs (to_real app_approx -. exact) in
  if t_equal total_err total_err_simp then
    (term_info, Some (left <=. total_err), strat)
  else
    ( term_info,
      Some (left <=. total_err_simp),
      Sapply_trans
        ( "assert",
          [ term_to_str (left <=. total_err) ],
          [ strat; default_strat () ] ) )

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
    | None ->
      (terms_info, None, strat)
      (* The error doesn't change since the float minus operation is exact *)
    | Some { exact; rel; factor; cst } ->
      let exact = minus exact in
      let f = abs (to_real t -. exact) <=. (rel **. factor) ++. cst in
      let terms_info = add_fw_error terms_info t { exact; rel; factor; cst } in
      (terms_info, Some f, strat))
  (* `t` is the result of an IEEE addition/sustraction/multiplication *)
  | Some (ieee_op, [ t1; t2 ])
    when is_uadd_ls ieee_op || is_usub_ls ieee_op || is_umul_ls ieee_op ->
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
  | Some (ieee_op, [ t1; t2 ]) when is_uexact_div_ls ieee_op ->
    let ts = get_ts t2 in
    let eta = eta ts in
    let to_real = to_real ts in
    let terms_info, fmla1, strat_for_t1 = get_error_fmlas info t1 in
    let strat_for_t1 = get_strat fmla1 strat_for_t1 in
    let t1_info = get_info terms_info t1 in
    let e1 = Option.get t1_info.error in
    let fe =
      {
        exact = e1.exact //. to_real t2;
        rel = e1.rel;
        factor = e1.factor //. abs (to_real t2);
        cst = (e1.cst //. abs (to_real t2)) ++. eta;
      }
    in
    let err =
      (e1.rel *. (e1.factor /. abs (to_real t2)))
      +. ((e1.cst /. abs (to_real t2)) +. eta)
    in
    let err_simp =
      (e1.rel **. (e1.factor //. abs (to_real t2)))
      ++. ((e1.cst //. abs (to_real t2)) ++. eta)
    in
    let left = abs (to_real t -. (e1.exact //. to_real t2)) in
    let s = string_of_ufloat_type ts in
    let strat =
      Sapply_trans
        ( "apply",
          [
            "udiv_exact_" ^ s ^ "_error_propagation";
            "with";
            sprintf "%s" (term_to_str t1);
          ],
          [
            strat_for_t1;
            default_strat ();
            default_strat ();
            default_strat ();
            default_strat ();
            default_strat ();
            default_strat ();
          ] )
    in
    let s =
      Sapply_trans
        ("assert", [ term_to_str (left <=. err) ], [ strat; default_strat () ])
    in
    let term_info = add_fw_error terms_info t fe in
    if t_equal err err_simp then
      (term_info, Some (left <=. err), s)
    else
      ( term_info,
        Some (left <=. err_simp),
        Sapply_trans
          ("assert", [ term_to_str (left <=. err) ], [ s; default_strat () ]) )
  | Some _ -> (info.terms_info, None, default_strat ())
  | None -> (
    match t_info.error with
    (* `t` has a forward error, we look if it is the result of the approximation
       of a known function, in which case we use the function's propagation
       lemma to compute an error bound *)
    | Some e -> (
      match get_known_fn_and_args t e.exact with
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
  let e_default = { exact; rel = zero; factor = zero; cst = t } in
  let rec parse t =
    if is_match t then
      ({ exact; rel = one; factor = t; cst = zero }, true)
    else
      match t.t_node with
      | Tapp (ls, [ t1; t2 ]) when is_add_ls ls ->
        let e1, _ = parse t1 in
        if is_zero e1.rel then
          let e2, _ = parse t2 in
          if is_zero e2.rel then
            (e_default, false)
          else
            (* FIXME: we should combine the factor of t1 and factor of t2 *)
            ({ e2 with cst = e2.cst ++. t1 }, false)
        else
          ({ e1 with cst = e1.cst ++. t2 }, false)
      | Tapp (ls, [ t1; t2 ]) when is_sub_ls ls ->
        (* FIXME : should be the same as for addition *)
        let e1, _ = parse t1 in
        if is_zero e1.rel then
          (e_default, false)
        else
          ({ e1 with cst = e1.cst --. t2 }, false)
      | Tapp (ls, [ t1; t2 ]) when is_mul_ls ls ->
        let e1, is_factor = parse t1 in
        if is_zero e1.rel then
          let e2, is_factor = parse t2 in
          if is_zero e2.rel then
            (e_default, false)
          else if is_factor then
            ({ e2 with rel = e2.rel **. t1 }, true)
          else
            ({ e2 with cst = e2.cst **. t1 }, false)
        else if is_factor then
          ({ e1 with rel = e1.rel **. t2 }, true)
        else
          ({ e1 with cst = e1.cst **. t2 }, false)
      | _ -> (e_default, false)
  in
  fst (parse t)

(* Parse `|f i - exact_f i| <= C`.
 * We try to decompose `C` to see if it has the form `A (f' i) + B` where
 * |f i| <= f' i for i in a given range.
 * Used for sum error propagation.
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
  let _is_sum, _f, _i, _j =
    match x.t_node with
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
        | _ -> false)
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
          match e.factor.t_node with
          | Tapp (fn'', args) ->
            let fn' = fst (extract_fn_and_args fn'' args) in
            let fns_info =
              Mls.add fn { e with factor = t_app_infer fn' [] } info.fns_info
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
  let mk_ufloat_symbols th _th_lemmas ty =
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
      udiv_exact = f th "udiv_exact";
      uadd_infix = f th (Ident.op_infix "++.");
      usub_infix = f th (Ident.op_infix "--.");
      umul_infix = f th (Ident.op_infix "**.");
      udiv_infix = f th (Ident.op_infix "//.");
      uminus_prefix = f th (Ident.op_prefix "--.");
      udiv_exact_infix = f th (Ident.op_infix "///.");
      eps = fs_app (f th "eps") [] ty_real;
      eta = fs_app (f th "eta") [] ty_real;
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
        usingle_symbols;
        udouble_symbols;
        ident_printer = printer.Trans.printer;
        tv_printer = printer.Trans.aprinter;
      }

(*** letify **)

let letify f =
  let rec compute_subterms (acc : int Mterm.t) f : int Mterm.t =
    match f.t_node with
    | Ttrue
    | Tfalse
    | Tconst _
    | Tvar _
    | Tapp (_, []) ->
      acc
    | _ -> (
      match f.t_ty with
      | None -> t_fold compute_subterms acc f
      | Some _ -> (
        try
          let n = Mterm.find f acc in
          Mterm.add f (n + 1) acc
        with
        | Not_found ->
          let acc = t_fold compute_subterms acc f in
          Mterm.add f 1 acc))
  in
  let m = compute_subterms Mterm.empty f in
  let m =
    Mterm.fold
      (fun t n acc ->
        if n <= 1 then
          acc
        else
          let id = Ident.id_fresh ?loc:t.t_loc "t" in
          let vs = create_vsymbol id (Option.get t.t_ty) in
          Mterm.add t vs acc)
      m Mterm.empty
  in
  let rec letify_rec f =
    try
      let vs = Mterm.find f m in
      t_var vs
    with
    | Not_found -> t_map letify_rec f
  in
  let letified_f = letify_rec f in
  let l = Mterm.bindings m in
  let l =
    List.sort (fun (t1, _) (t2, _) -> compare (term_size t2) (term_size t1)) l
  in
  List.fold_left
    (fun acc (t, vs) ->
      let t = t_map letify_rec t in
      t_let_close vs t acc)
    letified_f l

(*** complete strategy *)

let fw_propagation args env naming_table lang task =
  (* let naming_table = Args_wrapper.build_naming_tables task in *)
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
  let floats =
    match args with
    (* If no argument is given, then we perform forward error propagation for
       every ufloat term of the goal. *)
    | [] ->
      let goal = task_goal_fmla task in get_floats goal
    | [floats] ->
        Args_wrapper.parse_and_type_list ~lang ~as_fmla:false floats naming_table
    | _ -> raise (Args_wrapper.Arg_error
                    "this strategy expects an optional comma-separated list of terms as argument")
  in
  (* For each float `x`, we try to compute a formula of the form `|x - exact_x|
     <= A x' + B` where `exact_x` is the real value which is approximated by the
     float `x` and `|exact_x| <= x'`. For this, forward error propagation is
     performed using propagation lemmas of the ufloat stdlib with the data
     contained in `info`. For each new formula created, a proof tree is
     generated with the necessary steps to prove it. *)
  let f, strats =
    List.fold_left
      (fun (f, l) t ->
        match get_error_fmlas info t with
        | _, None, _ -> (f, l)
        | _, Some f', s -> (t_and_simp f f', s :: l))
      (t_true, []) floats
  in
  let f' = letify f in
  if List.length strats = 0 then
    (* Nothing to do *)
    default_strat ()
  else if List.length strats = 1 then
    (* We only have an assertion on one float so no need to use split *)
    let f_strat =
      Sapply_trans ("assert", [ term_to_str f ], strats @ [ default_strat () ])
    in
    Sapply_trans ("assert", [ term_to_str f' ], [ f_strat ])
  else
    (* We assert a conjunction of formulas, one for each float in the goal for
       which we can use propagation lemmas. We have one strat for each of this
       goal so we split our assertions and prove each subgoal with the
       corresponding strat *)
    let s = Sapply_trans ("split_vc", [], List.rev strats) in
    let f_strat =
      Sapply_trans ("assert", [ term_to_str f ], [ s; default_strat () ])
    in
    Sapply_trans ("assert", [ term_to_str f' ], [ f_strat ])

let () =
  register_strat_with_args "forward_propagation" fw_propagation
    ~desc:"Compute@ forward@ error@ of@ float@ computations."
