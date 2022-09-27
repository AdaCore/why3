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
open Pp
open Printer
open Ident
open Term
open Decl
open Theory
open Task

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

type info = {
  info_env : Env.env;
  info_syn : syntax_map;
}

let find_th env file th =
  let theory = Env.read_theory env [ file ] th in
  fun id -> Theory.ns_find_ls theory.Theory.th_export [ id ]

let get_info env task =
  (* sets of known symbols *)
  let syn = get_syntax_map task in
  { info_env = env; info_syn = syn }

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

let rec print_fmla info fmt f =
  let print_fmla = print_fmla info in
  match f.t_node with
  | Tapp ({ ls_name = id }, []) -> fprintf fmt "%a" print_ident id
  | Tapp (ls, tl) -> (
    match query_syntax info.info_syn ls.ls_name with
    | Some s -> syntax_arguments s print_fmla fmt tl
    | None ->
      unsupportedTerm f
        ("dreal: function '" ^ ls.ls_name.id_string ^ "' is not supported"))
  | Tquant (_q, _fq) -> ()
  | Tbinop (Tand, f1, f2) ->
    fprintf fmt "@[(and@ %a@ %a)@]" print_fmla f1 print_fmla f2
  | Tbinop (Tor, f1, f2) ->
    fprintf fmt "@[(or@ %a@ %a)@]" print_fmla f1 print_fmla f2
  | Tbinop (Timplies, f1, f2) ->
    fprintf fmt "@[(=>@ %a@ %a)@]" print_fmla f1 print_fmla f2
  | Tbinop (Tiff, f1, f2) ->
    fprintf fmt "@[(=@ %a@ %a)@]" print_fmla f1 print_fmla f2
  | Tnot f -> fprintf fmt "@[<hv2>(not@ %a)@]" print_fmla f
  | Ttrue -> pp_print_string fmt "true"
  | Tfalse -> pp_print_string fmt "false"
  | Tif (f1, f2, f3) ->
    fprintf fmt "@[<hv2>(ite %a@ %a@ %a)@]" print_fmla f1 print_fmla f2
      print_fmla f3
  | Tlet (t1, tb) ->
    let v, f2 = t_open_bound tb in
    fprintf fmt "@[<hv2>(let ((%a %a))@ %a)@]" print_ident v.vs_name print_fmla
      t1 print_fmla f2
  | Tcase _ -> unsupportedTerm f "dreal: you must eliminate match"
  | Tvar _ -> raise (FmlaExpected f)
  | Tconst c ->
    fprintf fmt "%a" Constant.(print number_format unsupported_escape) c
  | Teps _ -> raise (FmlaExpected f)

exception Contradiction

let split_fmla info fmt f =
  let rec split pos f =
    match f.t_node with
    | Tbinop (Tand, f1, f2) when pos ->
      split true f1;
      split true f2
    | Tbinop (Tor, f1, f2) when not pos ->
      split false f1;
      split false f2
    | Tbinop (Timplies, f1, f2) when not pos ->
      split true f1;
      split false f2
    | Tapp (ls, []) -> ()
    | Tapp (ls, [ { t_node = Tapp (t1, []) }; t2 ])
      when ls_equal ls ps_equ && t_equal t2 t_bool_true ->
      ()
    | Ttrue ->
      if pos then
        ()
      else
        raise Contradiction
    | Tfalse ->
      if pos then
        raise Contradiction
      else
        ()
    | Tnot f -> split (not pos) f
    | Tapp (ls, [ t1; t2 ]) when pos && ls_equal ls ps_equ ->
      fprintf fmt "@[(assert  %a)@]\n" (print_fmla info) f
    | _ ->
      if pos then
        fprintf fmt "@[(assert %a)@]\n" (print_fmla info) f
      else
        fprintf fmt "@[(assert %a)@]\n" (print_fmla info) (t_not f)
  in
  split true f

(* let rec print_ddecl fmt (ty, e) = *)
(*   match e with *)
(*   | (f, h) :: b -> fprintf fmt "%a" print_ident f.ls_name *)
(*   | [] -> () *)

let print_decl info fmt d =
  match d.d_node with
  | Dtype _ -> ()
  | Ddata dl -> () (* List.iter (print_ddecl fmt) dl *)
  | Dparam ({ ls_args = []; ls_value = Some ty } as ls)
    when Ty.ty_equal ty Ty.ty_int || Ty.ty_equal ty Ty.ty_real ->
    if Ty.ty_equal ty Ty.ty_int then
      fprintf fmt "@[(declare-fun %a () Int)@]\n" print_ident ls.ls_name
    else
      fprintf fmt "@[(declare-fun %a () Real)@]\n" print_ident ls.ls_name
  | Dparam _
  | Dlogic _ ->
    ()
  | Dind _ ->
    unsupportedDecl d
      "please remove inductive definitions before calling dreal printer"
  | Dprop (Paxiom, pr, f) -> split_fmla info fmt f
  | Dprop (Pgoal, pr, f) -> split_fmla info fmt (t_not f)
  | Dprop (Plemma, _, _) -> unsupportedDecl d "dreal: lemmas are not supported"

let print_task args ?old:_ fmt task =
  forget_all ident_printer;
  print_prelude fmt args.prelude;
  print_th_prelude task fmt args.th_prelude;
  let info = get_info args.env task in
  List.iter (print_decl info fmt) (Task.task_decls task);
  fprintf fmt "(check-sat)"

let () =
  register_printer "dreal" print_task
    ~desc:
      "Printer@ for@ the@ dReal@ theorem@ prover@ specialized@ in@ real@ \
       numbers@ reasoning."
