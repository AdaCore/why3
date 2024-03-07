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

(* TODO: Support uminus *)
type ufloat_symbols = {
  ufloat_type : tysymbol;
  to_real : lsymbol;
  uadd : lsymbol;
  usub : lsymbol;
  umul : lsymbol;
  udiv : lsymbol;
  uadd_infix : lsymbol;
  usub_infix : lsymbol;
  umul_infix : lsymbol;
  udiv_infix : lsymbol;
  eps : term;
  eta : term;
}

type symbols = {
  add : lsymbol;
  sub : lsymbol;
  mul : lsymbol;
  minus : lsymbol;
  add_infix : lsymbol;
  sub_infix : lsymbol;
  mul_infix : lsymbol;
  minus_infix : lsymbol;
  lt : lsymbol;
  lt_infix : lsymbol;
  le : lsymbol;
  le_infix : lsymbol;
  abs : lsymbol;
  sum : lsymbol;
  usingle_symbols : ufloat_symbols;
  udouble_symbols : ufloat_symbols;
  printer : ident_printer;
}

let symbols = ref None
let ( !! ) s = Option.get !s

(* This type corresponds to the numeric info we have on a real/float term *)
type term_info = {
  (*
   * Forward error associated to a real term "exact_t"
   * "Some (exact_t, rel_err, t', cst_err)" stands for
   * "|t - exact_t| <= rel_err * t' + cst_err", where |exact_t| <= t'
   *)
  error : (term * term * term * term) option;
  (*
   * "Some (op, x, y)" means that the term is the result of the FP operation
   * "op" on "x" and "y"
   *)
  ieee_op : (lsymbol * term * term) option;
}

type info = {
  terms_info : term_info Mterm.t;
  ls_defs : term Mls.t;
}

(* TODO: Call provers ? *)
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

let is_uop ls = is_uadd_ls ls || is_usub_ls ls || is_umul_ls ls || is_udiv_ls ls
let minus t = fs_app !!symbols.minus [ t ] ty_real

let minus_simp t =
  match t.t_node with
  | Tapp (ls, [ t' ]) when is_minus_ls ls -> t'
  | _ -> minus t

let add t1 t2 = fs_app !!symbols.add [ t1; t2 ] ty_real

let add_simp t1 t2 =
  if is_zero t1 then
    t2
  else if is_zero t2 then
    t1
  else
    add t1 t2

let sub t1 t2 = fs_app !!symbols.sub [ t1; t2 ] ty_real

let sub_simp t1 t2 =
  if is_zero t1 then
    minus_simp t2
  else if is_zero t2 then
    t1
  else
    sub t1 t2

let mul t1 t2 = fs_app !!symbols.mul [ t1; t2 ] ty_real

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

let ( +. ) x y = add x y
let ( -. ) x y = sub x y
let ( *. ) x y = mul x y
let ( ++. ) x y = add_simp x y
let ( --. ) x y = sub_simp x y
let ( **. ) x y = mul_simp x y
let ( <=. ) x y = ps_app !!symbols.le [ x; y ]

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

let add_ieee_op info ls t t1 t2 =
  let t_info = get_info info t in
  let t_info = { t_info with ieee_op = Some (ls, t1, t2) } in
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

let string_of_ufloat_type_and_op ts uop =
  let ty_str =
    if ts_equal ts !!symbols.usingle_symbols.ufloat_type then
      "single"
    else
      "double"
  in
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

let rec print_term fmt t =
  let id_unique = id_unique !!symbols.printer in
  match t.t_node with
  | Tvar v -> fprintf fmt "%s" (id_unique v.vs_name)
  | Tapp (ls, []) -> fprintf fmt "%s" (id_unique ls.ls_name)
  | Tapp (ls, tl) -> (
    let s = id_unique ls.ls_name in
    match (Ident.sn_decode s, tl) with
    | Ident.SNinfix s, [ t1; t2 ] ->
      fprintf fmt "(%a %s %a)" print_term t1 s print_term t2
    | Ident.SNprefix s, [ t ] -> fprintf fmt "(%s %a)" s print_term t
    | Ident.SNword s, tl ->
      fprintf fmt "(%s@ %a)" s (Pp.print_list Pp.space print_term) tl
    (* TODO: Other applications *)
    | _ ->
      fprintf fmt "(%s %a)" (id_unique ls.ls_name)
        (pp_print_list ~pp_sep:Pp.space print_term)
        tl)
  | Tbinop (Tand, t1, t2) ->
    fprintf fmt "(%a /\\ %a)" print_term t1 print_term t2
  | _ -> Pretty.print_term fmt t

let combine_errors info uop exact_t1 t1_rel_err t1' t1_cst_err exact_t2
    t2_rel_err t2' t2_cst_err r strat_for_t1 strat_for_t2 =
  let ts = get_ts r in
  let eps = eps ts in
  let eta = eta ts in
  let to_real = to_real ts in
  let rel_err, rel_err_simp =
    if is_uadd_ls uop || is_usub_ls uop then
      (* Relative error for addition and susbstraction *)
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
      (* Constant error for addition and susbstraction *)
      ( ((one +. eps +. t2_rel_err) *. t1_cst_err)
        +. ((one +. eps +. t1_rel_err) *. t2_cst_err),
        ((one ++. eps ++. t2_rel_err) **. t1_cst_err)
        ++. ((one ++. eps ++. t1_rel_err) **. t2_cst_err) )
    else
      (* Constant error for multiplication *)
      (* TODO: Here we choose to put things in the constant error that could
         instead be in the relative error. Sometimes it is good, sometimes not
         (for instance when x and y are lower than 1 ?). Investigate. *)
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
        [ str ^ "_error_propagation" ],
        [
          strat_for_t1;
          strat_for_t2;
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
      Sapply_trans
        ("assert", [ asprintf "%a" print_term f ], [ strat; default_strat () ])
    )

let basic_error info uop r t1 t2 =
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

(* Generates the formula for the forward error of `r = uop t1 t2` *)
let use_ieee_thms info uop r t1 t2 strat_for_t1 strat_for_t2 =
  let t1_info = get_info info t1 in
  let t2_info = get_info info t2 in
  match (t1_info.error, t2_info.error) with
  (* No propagation needed, we use the basic lemma *)
  | None, None -> basic_error info uop r t1 t2
  (* We have an error on at least one of t1 and t2, use the propagation lemma *)
  | _ ->
    let to_real = to_real (get_ts r) in
    let combine_errors = combine_errors info uop in
    let combine_errors =
      match t1_info.error with
      | None -> combine_errors (to_real t1) zero (abs (to_real t1)) zero
      | Some (exact_t1, rel_err, t1', cst_err) ->
        combine_errors exact_t1 rel_err t1' cst_err
    in
    let combine_errors =
      match t2_info.error with
      | None -> combine_errors (to_real t2) zero (abs (to_real t2)) zero
      | Some (exact_t2, rel_err, t2', cst_err) ->
        combine_errors exact_t2 rel_err t2' cst_err
    in
    combine_errors r strat_for_t1 strat_for_t2

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
        | Tapp (ls, [ t1; t2 ]) when is_uop ls ->
          { t_info with ieee_op = Some (ls, t1, t2) }
        | _ -> t_info)
      | Some _ as error -> { t_info with error })
    | Some _ as ieee_op -> { t_info with ieee_op }
  in
  recurse t

(*
 * Generate error formulas recursively for a term `t` using basic floating point
 * theorems as well as triangle inequality. This is recursive because if `t` is
 * an approximation of a term `u` which itself is an approximation of a term
 * `v`, we first compute a formula for the approximation of `v` by `u` and we
 *  combine it with the formula we already have of the approximation of `u` by
 * `t` to get a formula relating `t` to `v`.
 *)
let rec get_error_fmlas info t =
  let t_info = update_term_info info t in
  match t_info.ieee_op with
  (* `r` is the result of an ieee basic operation, we can use the corresponding
     theorem to compute an error for it *)
  | Some (ieee_op, t1, t2) ->
    (* Get error formulas on subterms `t1` and `t2` *)
    let terms_info, f1, strat_for_t1 = get_error_fmlas info t1 in
    let terms_info, f2, strat_for_t2 =
      get_error_fmlas { info with terms_info } t2
    in
    let get_strat f s =
      match f with
      | Some f ->
        Sapply_trans
          ("assert", [ asprintf "%a" print_term f ], [ s; default_strat () ])
      | None -> s
    in
    let strat_for_t1 = get_strat f1 strat_for_t1 in
    let strat_for_t2 = get_strat f2 strat_for_t2 in
    let info, f, strats =
      use_ieee_thms terms_info ieee_op t t1 t2 strat_for_t1 strat_for_t2
    in
    (info, Some f, strats)
  | None -> (info.terms_info, None, default_strat ())

(* Parse `|x_approx - x| <= C`.
 * We try to decompose `C` to see if it has the form `Ax' + B` where |x| <= x' *)
let parse_and_add_error_fmla info x_approx x c =
  let is_sum, _f, i, j =
    match x.t_node with
    | Tapp (ls, [ f; i; j ]) when ls_equal ls !!symbols.sum ->
      (true, Some f, Some i, Some j)
    | _ -> (false, None, None, None)
  in
  (* If it we don't find a "relative" error, then we have an absolute error of
     `c` *)
  let abs_err = (x, zero, zero, c) in
  let rec parse t =
    if t_equal t x then
      (abs_err, true)
    else
      match t.t_node with
      | Tapp (_ls, [ t' ]) when is_abs_ls _ls -> (
        if t_equal t' x then
          ((x, one, t, zero), true)
        else
          (* TODO: Special case of the sum, it could be handled better. Here we
             compare check that the indices are equal but we don't compare the
             functions. An idea would be to check if `|t1| <= t'` with a prover
             then consider it a forward error only if it is proved *)
          match t'.t_node with
          | Tapp (ls, [ _f'; i'; j' ])
            when ls_equal ls !!symbols.sum && is_sum
                 && t_equal i' (Option.get i)
                 && t_equal j' (Option.get j) ->
            ((x, one, t, zero), true)
          | _ -> (abs_err, false))
      | Tapp (ls, [ _f'; i'; j' ])
        when ls_equal ls !!symbols.sum && is_sum
             && t_equal i' (Option.get i)
             && t_equal j' (Option.get j) ->
        ((x, one, t, zero), true)
      | Tapp (_ls, [ t1; t2 ]) when is_add_ls _ls ->
        let (a, factor, a', cst), _ = parse t1 in
        if is_zero factor then
          let (a, factor, a', cst), _ = parse t2 in
          if is_zero factor then
            (abs_err, false)
          else
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
  let error_fmla, _ = parse c in
  add_fw_error info x_approx error_fmla

let rec collect info f =
  match f.t_node with
  | Tbinop (Tand, f1, f2) ->
    let info = collect info f1 in
    collect info f2
  | Tapp (ls, [ t; c ]) when is_ineq_ls ls -> (
    match t.t_node with
    | Tapp (ls, [ t ]) when is_abs_ls ls -> (
      match t.t_node with
      (* `|x_approx - x| <= C` *)
      | Tapp (ls, [ x_approx; x ]) when is_sub_ls ls ->
        parse_and_add_error_fmla info x_approx x c
      | _ -> info)
    | _ -> info)
  (* `r = t1 uop t2` or `t1 uop t2 = r` *)
  | Tapp (ls, [ t1; t2 ]) when ls_equal ls ps_equ -> (
    match t1.t_node with
    | Tapp (ls, [ t1'; t2' ]) when is_uop ls -> add_ieee_op info ls t2 t1' t2'
    | _ -> (
      match t2.t_node with
      | Tapp (ls, [ t1'; t2' ]) when is_uop ls -> add_ieee_op info ls t1 t1' t2'
      | _ -> info))
  | _ -> info

(*
 * We look for relevant axioms in the task, and we add corresponding
 * inequalities to `info`.
 * The formulas we look for have one of the following structures :
 * - `|x_approx - x| <= A` : forward error on `x_approx`
 * - `r = t1 uop t2` : `r` is the result of a FP operation on `t1` and `t2`
 *
 * We also look for definitions of the form `r = t1 uop t2`
 *)
(* TODO: Put that in a transformation for memoization *)
let collect_info info d =
  match d.d_node with
  | Dprop (kind, _, f) when kind = Paxiom || kind = Plemma ->
    { info with terms_info = collect info.terms_info f }
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
  let minus = ns_find_ls real.th_export [ Ident.op_prefix "-" ] in
  let add_infix = ns_find_ls real_infix.th_export [ Ident.op_infix "+." ] in
  let sub_infix = ns_find_ls real_infix.th_export [ Ident.op_infix "-." ] in
  let mul_infix = ns_find_ls real_infix.th_export [ Ident.op_infix "*." ] in
  let minus_infix = ns_find_ls real_infix.th_export [ Ident.op_prefix "-." ] in
  let real_abs = Env.read_theory env [ "real" ] "Abs" in
  let sum_th = Env.read_theory env [ "creal" ] "SumReal" in
  let sum = ns_find_ls sum_th.th_export [ "sum" ] in
  let abs = ns_find_ls real_abs.th_export [ "abs" ] in
  let usingle = Env.read_theory env [ "ufloat" ] "USingle" in
  let udouble = Env.read_theory env [ "ufloat" ] "UDouble" in
  let mk_ufloat_symbols th ty =
    let f s = ns_find_ls th.th_export [ s ] in
    {
      ufloat_type = ns_find_ts th.th_export [ ty ];
      to_real = f "to_real";
      uadd = f "uadd";
      usub = f "usub";
      umul = f "umul";
      udiv = f "udiv";
      uadd_infix = f (Ident.op_infix "++.");
      usub_infix = f (Ident.op_infix "--.");
      umul_infix = f (Ident.op_infix "**.");
      udiv_infix = f (Ident.op_infix "//.");
      eps = fs_app (f "eps") [] ty_real;
      eta = fs_app (f "eta") [] ty_real;
    }
  in
  let usingle_symbols = mk_ufloat_symbols usingle "usingle" in
  let udouble_symbols = mk_ufloat_symbols udouble "udouble" in
  symbols :=
    Some
      {
        add;
        sub;
        mul;
        minus;
        sum;
        add_infix;
        sub_infix;
        mul_infix;
        minus_infix;
        lt;
        lt_infix;
        le;
        le_infix;
        abs;
        usingle_symbols;
        udouble_symbols;
        printer;
      }

let numeric _ task =
  let printer = (Args_wrapper.build_naming_tables task).Trans.printer in
  (* Update the printer at each call, but not the symbols *)
  symbols := Some { !!symbols with printer };
  let goal = task_goal_fmla task in
  let floats = get_floats goal in
  let info =
    List.fold_left collect_info
      { terms_info = Mterm.empty; ls_defs = Mls.empty }
      (task_decls task)
  in
  (* For each float `f_approx` of the goal, we try to compute a formula of the
     form `|f_approx - f| <= A f' + B` where `f` is the real value which is
     approximated by the float `f_approx` and `|f| <= f'`. For this, forward
     error propagation is performed using theorems on the basic float operations
     as well as the triangle inequality with the data contained in `info`. For
     each new formula created, a proof tree is generated with the necessary
     steps to prove it. *)
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
    Sapply_trans
      ("assert", [ asprintf "%a" print_term f ], strats @ [ default_strat () ])
  else
    (* We assert a conjunction of formulas, one for each float in the goal for
       which we can use propagation lemmas. We have one strat for each of this
       goal so we split our assertions and prove each subgoal with the
       corresponding strat *)
    let s = Sapply_trans ("split_vc", [], List.rev strats) in
    Sapply_trans
      ("assert", [ asprintf "%a" print_term f ], [ s; default_strat () ])

let numeric_init env task =
  let naming_table = Args_wrapper.build_naming_tables task in
  init_symbols env naming_table.Trans.printer;
  (* `inline_trivial` simplifies the process of finding relevant information in
     the task *)
  Scont ("inline_trivial", [], numeric)

(* TODO: Add an optionnal argument to the strategy specifying a prover as a
   string, then use Whyconf.parse_filter_prover on it to generate a
   filter_prover. Problem : How do we get the config ? *)
(* TODO: Support log/exp/sin/cos *)
let () =
  register_strat "forward_propagation" numeric_init
    ~desc:"Compute@ forward@ error@ of@ float@ computations."
