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

(** Simplify printer *)

open Format
open Pp
open Ident
open Term
open Decl
open Printer

let ident_printer =
  let bls = ["select";"store"] in
  let san = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer bls ~sanitizer:san

let print_ident fmt id =
  fprintf fmt "%s" (id_unique ident_printer id)

let forget_var v = forget_id ident_printer v.vs_name

let print_var fmt {vs_name = id} = print_ident fmt id

type info = {
  info_syn : syntax_map;
}

let rec print_term info fmt t = match t.t_node with
  | Tconst c ->
      let number_format = {
          Number.long_int_support = false;
          Number.extra_leading_zeros_support = true;
          Number.negative_int_support = Number.Number_default;
          Number.dec_int_support = Number.Number_default;
          Number.hex_int_support = Number.Number_unsupported;
          Number.oct_int_support = Number.Number_unsupported;
          Number.bin_int_support = Number.Number_unsupported;
          Number.def_int_support = Number.Number_custom "constant_too_large_%s";
          Number.negative_real_support = Number.Number_default;
          Number.dec_real_support = Number.Number_unsupported;
          Number.hex_real_support = Number.Number_unsupported;
          Number.frac_real_support = Number.Number_unsupported;
          Number.def_real_support = Number.Number_custom "real_constant_%s";
        } in
      Number.print number_format fmt c
  | Tvar v ->
      print_var fmt v
  | Tapp (ls, tl) -> begin match query_syntax info.info_syn ls.ls_name with
      | Some s ->
          syntax_arguments s (print_term info) fmt tl
      | None -> begin match tl with (* for cvc3 wich doesn't accept (toto ) *)
          | [] -> fprintf fmt "@[%a@]" print_ident ls.ls_name
          | _ -> fprintf fmt "@[(%a@ %a)@]"
              print_ident ls.ls_name (print_list space (print_term info)) tl
        end end
  | Tlet _ ->
      unsupportedTerm t "simplify: you must eliminate let"
  | Tif _ ->
      unsupportedTerm t "simplify: you must eliminate if"
  | Tcase _ ->
      unsupportedTerm t "simplify: you must eliminate match"
  | Teps _ ->
      unsupportedTerm t  "simplify: you must eliminate epsilon"
  | Tquant _ | Tbinop _ | Tnot _ | Ttrue | Tfalse -> raise (TermExpected t)

and print_fmla info fmt f = match f.t_node with
  | Tapp ({ ls_name = id }, []) ->
      print_ident fmt id
  | Tapp (ls, tl) -> begin match query_syntax info.info_syn ls.ls_name with
      | Some s ->
          syntax_arguments s (print_term info) fmt tl
      | None ->
          fprintf fmt "(EQ (%a@ %a) |@@true|)"
            print_ident ls.ls_name (print_list space (print_term info)) tl
    end
  | Tquant (q, fq) ->
      let q = match q with Tforall -> "FORALL" | Texists -> "EXISTS" in
      let vl, tl, f = t_open_quant fq in
      fprintf fmt "@[(%s (%a)%a@ %a)@]" q (print_list space print_var) vl
        (print_triggers info) tl (print_fmla info) f;
      List.iter forget_var vl
  | Tbinop (Tand, f1, f2) ->
      fprintf fmt "@[(AND@ %a@ %a)@]" (print_fmla info) f1 (print_fmla info) f2
  | Tbinop (Tor, f1, f2) ->
      fprintf fmt "@[(OR@ %a@ %a)@]" (print_fmla info) f1 (print_fmla info) f2
  | Tbinop (Timplies, f1, f2) ->
      fprintf fmt "@[(IMPLIES@ %a@ %a)@]"
        (print_fmla info) f1 (print_fmla info) f2
  | Tbinop (Tiff, f1, f2) ->
      fprintf fmt "@[(IFF@ %a@ %a)@]" (print_fmla info) f1 (print_fmla info) f2
  | Tnot f ->
      fprintf fmt "@[(NOT@ %a)@]" (print_fmla info) f
  | Ttrue ->
      fprintf fmt "TRUE"
  | Tfalse ->
      fprintf fmt "FALSE"
  | Tif _ ->
      unsupportedTerm f "simplify: you must eliminate if"
  | Tlet _ ->
      unsupportedTerm f "simplify: you must eliminate let"
  | Tcase _ ->
      unsupportedTerm f "simplify: you must eliminate match"
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)

and print_expr info fmt =
  TermTF.t_select (print_term info fmt) (print_fmla info fmt)

and print_trigger info fmt = function
  | [] -> ()
  | [{t_node=Tvar _} as t] -> fprintf fmt "(MPAT %a)" (print_term info) t
  | [t] -> print_expr info fmt t
  | tl -> fprintf fmt "(MPAT %a)" (print_list space (print_expr info)) tl

and print_triggers info fmt = function
  | [] -> ()
  | tl -> fprintf fmt "@ (PATS %a)" (print_list space (print_trigger info)) tl

let print_decl info fmt d = match d.d_node with
  | Dtype _ | Dparam _ -> ()
  | Ddata _ ->
      unsupportedDecl d "Algebraic datatypes are not supported"
  | Dlogic _ ->
      unsupportedDecl d "Predicate and function definition aren't supported"
  | Dind _ ->
      unsupportedDecl d "simplify: inductive definition are not supported"
  | Dprop (Paxiom, pr, _) when Mid.mem pr.pr_name info.info_syn -> ()
  | Dprop (Paxiom, pr, f) ->
      fprintf fmt "@[(BG_PUSH@\n ;; axiom %s@\n @[<hov 2>%a@])@]@\n@\n"
        pr.pr_name.id_string (print_fmla info) f
  | Dprop (Pgoal, pr, f) ->
      fprintf fmt "@[;; %a@]@\n" print_ident pr.pr_name;
      (match pr.pr_name.id_loc with
        | Some loc -> fprintf fmt " @[;; %a@]@\n" Loc.gen_report_position loc
        | None -> ());
      fprintf fmt "@[<hov 2>%a@]@\n" (print_fmla info) f
  | Dprop (Plemma, _, _) ->
      assert false

let print_decls =
  let print_decl sm fmt d =
    try print_decl {info_syn = sm} fmt d; sm, []
    with Unsupported s -> raise (UnsupportedDecl (d,s)) in
  let print_decl = Printer.sprint_decl print_decl in
  let print_decl task acc = print_decl task.Task.task_decl acc in
  Discriminate.on_syntax_map (fun sm -> Trans.fold print_decl (sm,[]))

let print_task args ?old:_ fmt task =
  (* In trans-based p-printing [forget_all] is a no-no *)
  (* forget_all ident_printer; *)
  print_prelude fmt args.prelude;
  print_th_prelude task fmt args.th_prelude;
  let rec print = function
    | x :: r -> print r; Pp.string fmt x
    | [] -> () in
  print (snd (Trans.apply print_decls task));
  pp_print_flush fmt ()

let () = register_printer "simplify" print_task
  ~desc:"Printer@ for@ the@ Simplify@ theorem@ prover."
