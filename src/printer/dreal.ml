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

(** Dreal printer *)

open Format
open Printer
open Ident
open Term
open Decl
open Theory

let syntactic_transform transf =
  Trans.on_meta meta_syntax_logic (fun metas ->
      let symbols =
        List.fold_left
          (fun acc meta_arg ->
            match meta_arg with
            | [ MAls ls; MAstr _; MAint _ ] -> Sls.add ls acc
            | _ -> assert false)
          Sls.empty metas
      in
      transf (fun ls -> Sls.mem ls symbols))

let syntactic_transform_env transf env =
  Trans.on_meta meta_syntax_logic (fun metas ->
      let symbols =
        List.fold_left
          (fun acc meta_arg ->
            match meta_arg with
            | [ MAls ls; MAstr _; MAint _ ] -> Sls.add ls acc
            | _ -> assert false)
          Sls.empty metas
      in
      transf (fun ls -> Sls.mem ls symbols) env)

type info = { info_syn : syntax_map }

let info = ref { info_syn = Mid.empty }

let find_th env file th =
  let theory = Env.read_theory env [ file ] th in
  fun id -> Theory.ns_find_ls theory.Theory.th_export [ id ]

let get_info env task = { info_syn = get_syntax_map task }

let number_format =
  {
    Number.long_int_support = `Default;
    Number.negative_int_support = `Custom (fun fmt f -> fprintf fmt "-%t" f);
    Number.dec_int_support = `Default;
    Number.hex_int_support = `Default;
    Number.oct_int_support = `Unsupported;
    Number.bin_int_support = `Unsupported;
    Number.negative_real_support = `Custom (fun fmt f -> fprintf fmt "-%t" f);
    Number.dec_real_support = `Default;
    Number.hex_real_support = `Default;
    Number.frac_real_support = `Unsupported (fun _ _ -> assert false);
  }

let ident_printer =
  let bls =
    [
      "sqrt";
      "pow";
      "log";
      "exp";
      "tan";
      "atan";
      "atan2";
      "sin";
      "asin";
      "acos";
      "sinh";
      "cosh";
      "tanh";
      "min";
      "max";
    ]
  in
  let san = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer bls ~sanitizer:san

let print_ident fmt id = pp_print_string fmt (id_unique ident_printer id)

let print_decl fmt ls =
  if Ty.ty_equal (Option.get ls.ls_value) Ty.ty_int then
    fprintf fmt "@[(declare-fun %a () Int)@]\n" print_ident ls.ls_name
  else
    fprintf fmt "@[(declare-fun %a () Real)@]\n" print_ident ls.ls_name

let rec print_term fmt t =
  match t.t_node with
  | Tapp ({ ls_name = id; ls_value = Some ty }, [])
    when Ty.ty_equal ty Ty.ty_int || Ty.ty_equal ty Ty.ty_real ->
    fprintf fmt "%a" print_ident id
  | Tapp ({ ls_name = id }, []) -> fprintf fmt "%a" print_ident id
  | Tapp (ls, tl) -> (
    match query_syntax !info.info_syn ls.ls_name with
    | Some s -> syntax_arguments s print_term fmt tl
    | None ->
      unsupportedTerm t
        ("dreal: function '" ^ ls.ls_name.id_string ^ "' is not supported"))
  | Tquant (_q, _fq) -> raise (FmlaExpected t)
  | Tbinop (Tand, f1, f2) ->
    fprintf fmt "@[(and@ %a@ %a)@]" print_term f1 print_term f2
  | Tbinop (Tor, f1, f2) ->
    fprintf fmt "@[(or@ %a@ %a)@]" print_term f1 print_term f2
  | Tbinop (Timplies, f1, f2) ->
    fprintf fmt "@[(=>@ %a@ %a)@]" print_term f1 print_term f2
  | Tbinop (Tiff, f1, f2) ->
    fprintf fmt "@[(=@ %a@ %a)@]" print_term f1 print_term f2
  | Tnot f -> fprintf fmt "@[<hv2>(not@ %a)@]" print_term f
  | Ttrue -> pp_print_string fmt "true"
  | Tfalse -> pp_print_string fmt "false"
  | Tif (f1, f2, f3) ->
    fprintf fmt "@[<hv2>(ite %a@ %a@ %a)@]" print_term f1 print_term f2
      print_term f3
  | Tlet (t1, tb) ->
    let v, f2 = t_open_bound tb in
    fprintf fmt "@[<hv2>(let ((%a %a))@ %a)@]" print_ident v.vs_name print_term
      t1 print_term f2
  | Tcase _ -> unsupportedTerm t "dreal: you must eliminate match"
  | Tvar _ -> raise (FmlaExpected t)
  | Tconst c ->
    fprintf fmt "%a" Constant.(print number_format unsupported_escape) c
  | Teps _ -> raise (FmlaExpected t)

let rec print_assertion fmt assertion =
  fprintf fmt "@[(assert %a)@]\n" print_term assertion

type fmla =
  | Unsupported
  | Tautology
  | Contradiction
  | Formula of term

(* Filter all the formulas that are not inequalities or equalities *)
(* Also performs some simplifications *)
let rec get_fmla f =
  match f.t_node with
  | Tbinop (Tand, f1, f2) -> (
    match get_fmla f1 with
    | Unsupported
    | Tautology ->
      get_fmla f2
    | Contradiction -> Contradiction
    | Formula f1 -> (
      match get_fmla f2 with
      | Unsupported
      | Tautology ->
        Formula f1
      | Contradiction -> Contradiction
      | Formula f2 -> Formula (t_and f1 f2)))
  | Tbinop (Tor, f1, f2) -> (
    match get_fmla f1 with
    | Unsupported -> Unsupported
    | Tautology -> Tautology
    | Contradiction -> get_fmla f2
    | Formula f1 -> (
      match get_fmla f2 with
      | Unsupported -> Unsupported
      | Tautology -> Tautology
      | Contradiction -> Formula f1
      | Formula f2 -> Formula (t_or f1 f2)))
  | Tbinop (Timplies, f1, f2) -> (
    match get_fmla f1 with
    | Unsupported
    | Contradiction ->
      Unsupported
    | Tautology -> get_fmla f2
    | Formula f1 -> (
      match get_fmla f2 with
      | Unsupported -> Unsupported
      | Tautology -> Tautology
      | Contradiction -> Formula (t_implies f1 t_false)
      | Formula f2 -> Formula (t_implies f1 f2)))
  | Ttrue -> Tautology
  | Tfalse -> Contradiction
  | Tnot f1 -> (
    match get_fmla f1 with
    | Unsupported -> Unsupported
    | Tautology -> Contradiction
    | Contradiction -> Tautology
    | Formula f -> Formula (t_not f))
  | Tapp (ls, [ t1; t2 ]) -> (
    if ls_equal ls ps_equ then
      match t1.t_ty with
      | Some ty ->
        if not (Ty.ty_equal ty Ty.ty_int || Ty.ty_equal ty Ty.ty_real) then
          Unsupported
        else
          Formula f
      | None -> Formula f
    else
      match query_syntax !info.info_syn ls.ls_name with
      | Some s -> Formula f
      | None -> Unsupported)
  | _ -> Unsupported

let get_decls_and_assertions (decls, assertions) d =
  match d.d_node with
  | Dtype _ -> (decls, assertions)
  | Ddata dl -> (decls, assertions)
  | Dparam ({ ls_args = []; ls_value = Some ty } as ls)
    when Ty.ty_equal ty Ty.ty_int || Ty.ty_equal ty Ty.ty_real ->
    (ls :: decls, assertions)
  | Dparam _
  | Dlogic _ ->
    (decls, assertions)
  | Dind _ ->
    unsupportedDecl d
      "please remove inductive definitions before calling dreal printer"
  | Dprop (Paxiom, _, f) -> (
    match get_fmla f with
    | Contradiction -> (decls, t_false :: assertions)
    | Formula f -> (decls, f :: assertions)
    | _ -> (decls, assertions))
  | Dprop (Pgoal, _, f) -> (
    match get_fmla f with
    | Unsupported -> unsupportedDecl d "dreal: This types of goals are not supported"
    | Contradiction -> (decls, t_true :: assertions)
    | Tautology -> (decls, t_false :: assertions)
    | Formula f -> (decls, t_not f :: assertions))
  | Dprop (Plemma, _, _) -> unsupportedDecl d "dreal: lemmas are not supported"

let print_task args ?old:_ fmt task =
  forget_all ident_printer;
  print_prelude fmt args.prelude;
  print_th_prelude task fmt args.th_prelude;
  info := get_info args.env task;
  let decls, assertions =
    List.fold_left get_decls_and_assertions ([], []) (Task.task_decls task)
  in
  List.iter (print_decl fmt) (List.rev decls);
  List.iter (print_assertion fmt) (List.rev assertions);
  fprintf fmt "(check-sat)"

let () =
  register_printer "dreal" print_task
    ~desc:
      "Printer@ for@ the@ dReal@ theorem@ prover@ specialized@ in@ real@ \
       numbers@ reasoning."
