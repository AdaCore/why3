(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Format

open Why3
open Pp
open Ident
open Ty
open Term
open Decl
open Task
open Printer

let ident_printer =
  let san = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer [] ~sanitizer:san

let pr_printer =
  let san = sanitizer char_to_lalpha char_to_alnumus in
  create_ident_printer [] ~sanitizer:san

let print_symbol fmt id =
  let san = String.uncapitalize in
  fprintf fmt "%s" (id_unique ~sanitizer:san ident_printer id)

let print_tvar fmt {tv_name = id} =
  let san = String.capitalize in
  fprintf fmt "%s" (id_unique ~sanitizer:san ident_printer id)

let print_var fmt {vs_name = id} =
  let san = String.capitalize in
  fprintf fmt "%s" (id_unique ~sanitizer:san ident_printer id)

let print_pr fmt pr =
  fprintf fmt "%s" (id_unique pr_printer pr.pr_name)

let forget_var v = forget_id ident_printer v.vs_name
let forget_tvar v = forget_id ident_printer v.tv_name

type info = {
  info_syn : syntax_map;
  info_fof : bool;
}

let rec print_type info fmt ty = match ty.ty_node with
  | Tyvar tv -> print_tvar fmt tv
  | Tyapp (ts, tl) -> begin match query_syntax info.info_syn ts.ts_name with
      | Some s -> syntax_arguments s (print_type info) fmt tl
      | None -> begin match tl with
          | [] -> print_symbol fmt ts.ts_name
          | _ -> fprintf fmt "@[%a(%a)@]" print_symbol ts.ts_name
              (print_list comma (print_type info)) tl
          end
      end

let rec print_app info fmt ls tl oty =
  match query_syntax info.info_syn ls.ls_name with
  | Some s -> syntax_arguments s (print_term info) fmt tl
  | None ->
      let sbs = ls_app_inst ls tl oty in
      if Mtv.is_empty sbs && tl = [] then
        print_symbol fmt ls.ls_name
      else begin
        let cm = if Mtv.is_empty sbs || tl = [] then "" else ", " in
        fprintf fmt "%a(%a%s%a)"
          print_symbol ls.ls_name
          (print_iter2 Mtv.iter comma nothing nothing (print_type info)) sbs
          cm
          (print_list comma (print_term info)) tl
      end

and print_term info fmt t = match t.t_node with
  | Tvar v ->
      print_var fmt v
  | Tapp (ls, tl) ->
      print_app info fmt ls tl t.t_ty
  | Tconst c ->
      let number_format = {
        Print_number.long_int_support = true;
        Print_number.dec_int_support = Print_number.Number_default;
        Print_number.hex_int_support = Print_number.Number_unsupported;
        Print_number.oct_int_support = Print_number.Number_unsupported;
        Print_number.bin_int_support = Print_number.Number_unsupported;
        Print_number.def_int_support = Print_number.Number_unsupported;
        Print_number.dec_real_support = Print_number.Number_default;
        Print_number.hex_real_support = Print_number.Number_unsupported;
        Print_number.frac_real_support = Print_number.Number_unsupported;
        Print_number.def_real_support = Print_number.Number_unsupported;
      } in
      Print_number.print number_format fmt c
  | Tlet (t1,tb) ->
      let v,t2 = t_open_bound tb in
      fprintf fmt "$let_tt(%a@ =@ %a,@ %a)"
        print_symbol v.vs_name (print_term info) t1 (print_term info) t2;
      forget_var v
  | Tif (f1,t1,t2) ->
      fprintf fmt "$ite_t(%a,@ %a,@ %a)"
        (print_fmla info) f1 (print_term info) t1 (print_term info) t2
  | Tcase _ -> unsupportedTerm t
      "TPTP does not support pattern matching, use eliminate_algebraic"
  | Teps _ -> unsupportedTerm t
      "TPTP does not support epsilon-terms"
  | Tquant _ | Tbinop _ | Tnot _ | Ttrue | Tfalse -> raise (TermExpected t)

and print_fmla info fmt f = match f.t_node with
  | Tapp (ls, tl) ->
      print_app info fmt ls tl f.t_ty
  | Tbinop (op, f1, f2) ->
      let s = match op with
        | Tand -> "&" | Tor -> "|" | Timplies -> "=>" | Tiff -> "<=>" in
      fprintf fmt "(%a@ %s %a)" (print_fmla info) f1 s (print_fmla info) f2
  | Tnot f ->
      fprintf fmt "~@ (%a)" (print_fmla info) f
  | Ttrue ->
      fprintf fmt "$true"
  | Tfalse ->
      fprintf fmt "$false"
  | Tquant (q, fq) ->
      let q = match q with Tforall -> "!" | Texists -> "?" in
      let vl, _tl, f = t_open_quant fq in
      let print_vsty fmt vs =
        if info.info_fof then fprintf fmt "%a" print_var vs
        else fprintf fmt "%a:@,%a" print_var vs (print_type info) vs.vs_ty in
      fprintf fmt "%s[%a]:@ %a" q
        (print_list comma print_vsty) vl (print_fmla info) f;
      List.iter forget_var vl
  | Tlet (t1,tb) ->
      let v,t2 = t_open_bound tb in
      fprintf fmt "$let_tf(%a@ =@ %a,@ %a)"
        print_symbol v.vs_name (print_term info) t1 (print_fmla info) t2;
      forget_var v
  | Tif (f1,t1,t2) ->
      fprintf fmt "$ite_f(%a,@ %a,@ %a)"
        (print_fmla info) f1 (print_fmla info) t1 (print_fmla info) t2
  | Tcase _ -> unsupportedTerm f
      "TPTP does not support pattern matching, use eliminate_algebraic"
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)

let print_tvarg fmt tv = fprintf fmt "%a : $tType" print_tvar tv
let print_tvargs fmt tvs = print_iter1 Stv.iter comma print_tvarg fmt tvs

let star fmt _ = fprintf fmt " *@ "

let print_fmla info fmt f =
  let tvs = t_ty_freevars Stv.empty f in
  if Stv.is_empty tvs then print_fmla info fmt f else
  fprintf fmt "![%a]:@ %a" print_tvargs tvs (print_fmla info) f;
  Stv.iter forget_tvar tvs

let print_decl info fmt d = match d.d_node with
  | Dtype _ when info.info_fof -> ()
  | Dtype { ts_def = Some _ } -> ()
  | Dtype ts when query_syntax info.info_syn ts.ts_name <> None -> ()
  | Dtype ts ->
      let print_arg fmt _ = fprintf fmt "$tType" in
      let print_sig fmt ts = match ts.ts_args with
        | [] -> fprintf fmt "$tType"
        | [_] -> fprintf fmt "$tType >@ $tType"
        | tl -> fprintf fmt "(%a) >@ $tType" (print_list star print_arg) tl
      in
      fprintf fmt "@[<hov 2>tff(%s, type,@ %a:@ %a).@]@\n@\n"
        (id_unique pr_printer ts.ts_name)
        print_symbol ts.ts_name print_sig ts
  | Dparam _ when info.info_fof -> ()
  | Dparam ls when query_syntax info.info_syn ls.ls_name <> None -> ()
  | Dparam ls ->
      let print_type = print_type info in
      let print_val fmt = function
        | Some ty -> print_type fmt ty
        | None -> fprintf fmt "$o" in
      let print_sig fmt ls = match ls.ls_args with
        | [] -> print_val fmt ls.ls_value
        | [ty] -> fprintf fmt "%a >@ %a"
            print_type ty print_val ls.ls_value
        | tl -> fprintf fmt "(%a) >@ %a"
            (print_list star print_type) tl print_val ls.ls_value in
      let print_sig fmt ls =
        let tvs = List.fold_left ty_freevars Stv.empty ls.ls_args in
        let tvs = oty_freevars tvs ls.ls_value in
        if Stv.is_empty tvs then
          print_sig fmt ls
        else if ls.ls_args = [] then
          fprintf fmt "!>[%a]:@ %a" print_tvargs tvs print_sig ls
        else
          fprintf fmt "!>[%a]:@ (%a)" print_tvargs tvs print_sig ls;
        Stv.iter forget_tvar tvs
      in
      fprintf fmt "@[<hov 2>tff(%s, type,@ %a:@ %a).@]@\n@\n"
        (id_unique pr_printer ls.ls_name)
        print_symbol ls.ls_name print_sig ls
  | Ddata _ -> unsupportedDecl d
      "TPTP does not support algebraic datatypes, use eliminate_algebraic"
  | Dlogic _ -> unsupportedDecl d
      "Definitions are not supported, use eliminate_definition"
  | Dind _ -> unsupportedDecl d
      "TPTP does not support inductive predicates, use eliminate_inductive"
  | Dprop (Paxiom, pr, _) when Mid.mem pr.pr_name info.info_syn -> ()
  | Dprop (Paxiom, pr, f) ->
      let head = if info.info_fof then "fof" else "tff" in
      fprintf fmt "@[<hov 2>%s(%a, axiom,@ %a).@]@\n@\n"
        head print_pr pr (print_fmla info) f
  | Dprop (Pgoal, pr, f) ->
      let head = if info.info_fof then "fof" else "tff" in
      fprintf fmt "@[<hov 2>%s(%a, conjecture,@ %a).@]@\n"
        head print_pr pr (print_fmla info) f
  | Dprop ((Plemma|Pskip), _, _) -> assert false

let print_decl info fmt = catch_unsupportedDecl (print_decl info fmt)

let print_task fof _env pr thpr _blacklist ?old:_ fmt task =
  forget_all ident_printer;
  forget_all pr_printer;
  print_prelude fmt pr;
  print_th_prelude task fmt thpr;
  let info = { info_syn = get_syntax_map task; info_fof = fof } in
  fprintf fmt "@[%a@]@."
    (print_list nothing (print_decl info)) (Task.task_decls task)

let () = register_printer "tptp-tff" (print_task false) ~desc:"TPTP TFF format"
let () = register_printer "tptp-fof" (print_task true) ~desc:"TPTP FOF format"
