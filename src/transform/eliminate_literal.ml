(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ident
open Ty
open Term
open Decl
open Theory

let meta_keep_lit = register_meta "literal:keep" [MTtysymbol]
  ~desc:"Preserve@ literals@ of@ a@ given@ type."

let add_literal (known_lit, decl as acc) t c ls_proj fin =
  try acc, Mterm.find t known_lit with Not_found ->
    (* TODO: pretty-print the constant to have a readable name *)
    let litname =
      match fin with None -> "rliteral" | _ -> "fliteral" in
    let ls = create_lsymbol (id_fresh litname) [] t.t_ty in
    let ls_decl = create_param_decl ls in
    let pr = create_prsymbol (id_fresh (litname^"_axiom")) in
    let ls_t = t_app ls [] t.t_ty in
    let f = t_app ls_proj [ls_t] ls_proj.ls_value in
    let f = t_equ f (t_const c (Opt.get f.t_ty)) in
    let f = match fin with
      | None -> f
      | Some isF -> t_and (t_app isF [ls_t] None) f in
    let ax_decl = create_prop_decl Paxiom pr f in
    let decl = ax_decl::ls_decl::decl in
    (Mterm.add t ls_t known_lit, decl), ls_t

(* TODO: remove int and real literals if not supported.
   NOTE: in this case, [add_literal] above is incorrect. *)
let rec abstract_terms kn range_metas float_metas type_kept acc t =
  match t.t_node, t.t_ty with
  | Tconst (Number.ConstInt _ as c), Some {ty_node = Tyapp (ts,[])}
    when not (ts_equal ts ts_int || Sts.mem ts type_kept) ->
      let to_int = Mts.find ts range_metas in
      add_literal acc t c to_int None
  | Tconst (Number.ConstReal _ as c), Some {ty_node = Tyapp (ts,[])}
    when not (ts_equal ts ts_real || Sts.mem ts type_kept) ->
      let to_real,isF = Mts.find ts float_metas in
      add_literal acc t c to_real (Some isF)
  | _ ->
      t_map_fold (abstract_terms kn range_metas float_metas type_kept) acc t

let elim le_int le_real neg_real type_kept kn
    range_metas float_metas d (known_lit,task) =
  match d.d_node with
  | Dtype ts when Mts.exists (fun ts' _ -> ts_equal ts ts') range_metas
               && not (Sts.mem ts type_kept) ->
      let to_int = Mts.find ts range_metas in
      let ir = match ts.ts_def with Range ir -> ir | _ -> assert false in
      let lo = ir.Number.ir_lower in
      let hi = ir.Number.ir_upper in
      let ty_decl = create_ty_decl ts in
      let ls_decl = create_param_decl to_int in
      let pr = create_prsymbol (id_fresh (ts.ts_name.id_string ^ "'axiom")) in
      let v = create_vsymbol (id_fresh "i") (ty_app ts []) in
      let v_term = t_app to_int [t_var v] (Some ty_int) in
      let a_term = t_bigint_const lo in
      let b_term = t_bigint_const hi in
      let f = t_and (t_app le_int [a_term; v_term] None)
          (t_app le_int [v_term; b_term] None)
      in
      let f = t_forall_close [v] [] f in
      let ax_decl = create_prop_decl Paxiom pr f in
      let add_decl t d = try Task.add_decl t d
                         with UnknownIdent _ -> t in (*FIXME*)
      (known_lit, List.fold_left add_decl task [ty_decl; ls_decl; ax_decl])
  | Dtype ts when Mts.exists (fun ts' _ -> ts_equal ts ts') float_metas
               && not (Sts.mem ts type_kept) ->
      let to_real,is_finite = Mts.find ts float_metas in
      let fp = match ts.ts_def with Float fp -> fp | _ -> assert false in
      let eb = BigInt.of_int fp.Number.fp_exponent_digits in
      let sb = BigInt.of_int fp.Number.fp_significand_digits in
      (* declare abstract type [t] *)
      let ty_decl = create_ty_decl ts in
      (* declare projection to_real *)
      let proj_decl = create_param_decl to_real in
      (* declare predicate is_finite *)
      let isFinite_decl = create_param_decl is_finite in
      (* create defining axiom *)
      (* [forall v:t. is_finite v -> | to_real v | <= max] *)
      let pr = create_prsymbol (id_fresh (ts.ts_name.id_string ^ "'axiom")) in
      let v = create_vsymbol (id_fresh "x") (ty_app ts []) in
      let v_term = t_app to_real [t_var v] (Some ty_real) in
      (* compute max *)
      let emax = BigInt.pow_int_pos_bigint 2 (BigInt.pred eb) in
      let m = BigInt.pred (BigInt.pow_int_pos_bigint 2 sb) in
      let e = BigInt.sub emax sb in
      let m_string = Format.asprintf "%a" (Number.print_in_base 16 None) m in
      let e_string = Format.asprintf "%a" (Number.print_in_base 10 None) e in
      let e_val = Number.real_const_hex m_string "" (Some e_string) in
      let max_term = t_const
          Number.(ConstReal { rc_negative = false ; rc_abs = e_val })
          ty_real
      in
      (* compose axiom *)
      let f = t_and (t_app le_real [t_app neg_real [max_term] (Some ty_real); v_term] None)
          (t_app le_real [v_term; max_term] None) in
        (* t_app le_real [t_app abs_real [v_term] (Some ty_real); term] None in *)
      let f = t_implies (t_app is_finite [t_var v] None) f in
      let f = t_forall_close [v] [] f in
      let ax_decl = create_prop_decl Paxiom pr f in
      (known_lit, List.fold_left Task.add_decl task
         [ty_decl; proj_decl; isFinite_decl; ax_decl])
  | _ ->
      let (known_lit, local_decl), d =
        decl_map_fold
          (abstract_terms kn range_metas float_metas type_kept)
          (known_lit,[]) d in
      let t = List.fold_left Task.add_decl task (List.rev local_decl) in
      (known_lit, Task.add_decl t d)

let eliminate le_int le_real neg_real type_kept
    range_metas float_metas t (known_lit, acc) =
  match t.Task.task_decl.td_node with
  | Decl d ->
      elim le_int le_real neg_real type_kept
        t.Task.task_known range_metas float_metas d (known_lit, acc)
  | Meta (m, [MAts ts]) when meta_equal m meta_keep_lit ->
      let td = create_meta Libencoding.meta_kept [MAty (ty_app ts [])] in
      let acc = Task.add_tdecl acc t.Task.task_decl in
      known_lit, Task.add_tdecl acc td
  | Use _ | Clone _ | Meta _ ->
      known_lit, Task.add_tdecl acc t.Task.task_decl

let eliminate_literal env =
  (* FIXME: int.Int.le_sym should be imported in the task *)
  let th = Env.read_theory env ["int"] "Int" in
  let le_int = ns_find_ls th.th_export [op_infix "<="] in
  let th = Env.read_theory env ["real"] "Real" in
  let le_real = ns_find_ls th.th_export [op_infix "<="] in
  let neg_real = ns_find_ls th.th_export [op_prefix "-"] in
  Trans.on_meta meta_range (fun range_metas ->
      Trans.on_meta meta_float (fun float_metas ->
          let range_metas = List.fold_left (fun acc meta_arg ->
              match meta_arg with
              | [MAts ts; MAls to_int] -> Mts.add ts to_int acc
              | _ -> assert false) Mts.empty range_metas in
          let float_metas = List.fold_left (fun acc meta_arg ->
              match meta_arg with
              | [MAts ts; MAls to_real; MAls is_finite] ->
                  Mts.add ts (to_real,is_finite) acc
              | _ -> assert false) Mts.empty float_metas in
          Trans.on_tagged_ts meta_keep_lit
            (fun type_kept ->
               Trans.fold_map
                 (eliminate le_int le_real neg_real type_kept
                    range_metas float_metas)
                 Mterm.empty None)))

let () =
  Trans.register_env_transform "eliminate_literal" eliminate_literal
    ~desc:"Eliminate@ unsupported@ literals."



(* simple transformation that just replace negative constants by application
   of 'prefix -' to positive constant *)

open Number

let rec replace_negative_constants neg_int neg_real t =
  match t.t_ty, t.t_node with
  | (Some ty), (Tconst (ConstInt c)) ->
     if c.ic_negative && ty_equal ty ty_int then
       t_app neg_int
             [t_const (ConstInt { c with ic_negative = false }) ty_int]
             (Some ty_int)
     else t
  | (Some ty), (Tconst (ConstReal c)) ->
     if c.rc_negative && ty_equal ty ty_real then
       t_app neg_real
             [t_const (ConstReal { c with rc_negative = false }) ty_real]
             (Some ty_real)
     else t
  | _ -> t_map (replace_negative_constants neg_int neg_real) t

let eliminate_negative_constants env =
  (* FIXME: int.Int should be imported in the task *)
  let th = Env.read_theory env ["int"] "Int" in
  let neg_int = ns_find_ls th.th_export [op_prefix "-"] in
  let th = Env.read_theory env ["real"] "Real" in
  let neg_real = ns_find_ls th.th_export [op_prefix "-"] in
  Trans.rewrite (replace_negative_constants neg_int neg_real) None

let () =
  Trans.register_env_transform "eliminate_negative_constants"
                               eliminate_negative_constants
                               ~desc:"Eliminate@ negative@ constants"
