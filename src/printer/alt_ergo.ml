(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
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

(** Alt-ergo printer *)

open Format
open Pp
open Ident
open Ty
open Term
open Decl
open Task
open Printer

let meta_ac = Theory.register_meta "AC" [Theory.MTlsymbol]

let ident_printer =
  let bls = [
    "ac"; "and"; "array"; "as"; "axiom"; "bool"; "else"; "exists";
    "false"; "forall"; "function"; "goal"; "if"; "int"; "bitv";
    "logic"; "not"; "or"; "parameter"; "predicate";
    "prop"; "real"; "then"; "true"; "type"; "unit"; "void";
    "select"; "store";
  ]
  in
  let san = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer bls ~sanitizer:san

let print_ident fmt id =
  fprintf fmt "%s" (id_unique ident_printer id)

let print_tvsymbols fmt tv =
  let sanitize n = "'" ^ n in
  let n = id_unique ident_printer ~sanitizer:sanitize tv.tv_name in
  fprintf fmt "%s" n

let forget_var v = forget_id ident_printer v.vs_name

type info = {
  info_syn : string Mid.t;
  info_rem : Sid.t;
  info_ac  : Sls.t;
}

let rec print_type info fmt ty = match ty.ty_node with
  | Tyvar id ->
      print_tvsymbols fmt id
  | Tyapp (ts, tl) -> begin match query_syntax info.info_syn ts.ts_name with
      | Some s -> syntax_arguments s (print_type info) fmt tl
      | None -> fprintf fmt "%a%a" (print_tyapp info) tl print_ident ts.ts_name
    end

and print_tyapp info fmt = function
  | [] -> ()
  | [ty] -> fprintf fmt "%a " (print_type info) ty
  | tl -> fprintf fmt "(%a) " (print_list comma (print_type info)) tl

let rec print_term info fmt t = match t.t_node with
  | Tbvar _ ->
      assert false
  | Tconst c ->
      Pretty.print_const fmt c
  | Tvar { vs_name = id } ->
      print_ident fmt id
  | Tapp (ls, tl) -> begin match query_syntax info.info_syn ls.ls_name with
      | Some s -> syntax_arguments s (print_term info) fmt tl
      | None -> fprintf fmt "%a%a" print_ident ls.ls_name (print_tapp info) tl
    end
  | Tlet _ -> unsupportedTerm t
      "alt-ergo : you must eliminate let in term"
  | Tif _ -> unsupportedTerm t
      "alt-ergo : you must eliminate if_then_else"
  | Tcase _ -> unsupportedTerm t
      "alt-ergo : you must eliminate match"
  | Teps _ -> unsupportedTerm t
      "alt-ergo : you must eliminate epsilon"

and print_tapp info fmt = function
  | [] -> ()
  | tl -> fprintf fmt "(%a)" (print_list comma (print_term info)) tl

let rec print_fmla info fmt f = match f.f_node with
  | Fapp ({ ls_name = id }, []) ->
      print_ident fmt id
  | Fapp (ls, tl) -> begin match query_syntax info.info_syn ls.ls_name with
      | Some s -> syntax_arguments s (print_term info) fmt tl
      | None -> fprintf fmt "%a(%a)" print_ident ls.ls_name
                    (print_list comma (print_term info)) tl
    end
  | Fquant (q, fq) ->
      let q = match q with Fforall -> "forall" | Fexists -> "exists" in
      let vl, tl, f = f_open_quant fq in
      let forall fmt v =
	fprintf fmt "%s %a:%a" q print_ident v.vs_name (print_type info) v.vs_ty
      in
      fprintf fmt "@[(%a%a.@ %a)@]" (print_list dot forall) vl
        (print_triggers info) tl (print_fmla info) f;
      List.iter forget_var vl
  | Fbinop (Fand, f1, f2) ->
      fprintf fmt "(%a and@ %a)" (print_fmla info) f1 (print_fmla info) f2
  | Fbinop (For, f1, f2) ->
      fprintf fmt "(%a or@ %a)" (print_fmla info) f1 (print_fmla info) f2
  | Fbinop (Fimplies, f1, f2) ->
      fprintf fmt "(%a ->@ %a)" (print_fmla info) f1 (print_fmla info) f2
  | Fbinop (Fiff, f1, f2) ->
      fprintf fmt "(%a <->@ %a)" (print_fmla info) f1 (print_fmla info) f2
  | Fnot f ->
      fprintf fmt "(not %a)" (print_fmla info) f
  | Ftrue ->
      fprintf fmt "true"
  | Ffalse ->
      fprintf fmt "false"
  | Fif (f1, f2, f3) ->
      fprintf fmt "((%a and %a) or (not %a and %a))"
	(print_fmla info) f1 (print_fmla info) f2 (print_fmla info)
        f1 (print_fmla info) f3
  | Flet _ -> unsupportedFmla f
      "alt-ergo : you must eliminate let in formula"
  | Fcase _ -> unsupportedFmla f
      "alt-ergo : you must eliminate match"


and print_expr info fmt = e_apply (print_term info fmt) (print_fmla info fmt)

and print_triggers info fmt tl =
  let filter = function
    | Term _ -> true
    | Fmla {f_node = Fapp (ps,_)} -> not (ls_equal ps ps_equ)
    | _ -> false in
  let tl = List.map (List.filter filter)
    tl in
  let tl = List.filter (function [] -> false | _::_ -> true) tl in
  if tl = [] then () else fprintf fmt "@ [%a]"
    (print_list alt (print_list comma (print_expr info))) tl

let print_logic_binder info fmt v =
  fprintf fmt "%a: %a" print_ident v.vs_name (print_type info) v.vs_ty

let print_type_decl fmt ts = match ts.ts_args with
  | [] -> fprintf fmt "type %a" print_ident ts.ts_name
  | [tv] -> fprintf fmt "type %a %a" print_tvsymbols tv print_ident ts.ts_name
  | tl -> fprintf fmt "type (%a) %a"
      (print_list comma print_tvsymbols) tl print_ident ts.ts_name

let print_type_decl info fmt = function
  | ts, Tabstract when Sid.mem ts.ts_name info.info_rem -> false
  | ts, Tabstract -> print_type_decl fmt ts; true
  | _, Talgebraic _ -> unsupported
      "alt-ergo : algebraic datatype are not supported"

let ac_th = ["algebra";"AC"]

let print_logic_decl info fmt (ls,ld) =
  match ld with
    | None ->
        let sac = if Sls.mem ls info.info_ac then "ac " else "" in
        fprintf fmt "@[<hov 2>logic %s%a : %a%s%a@]@\n"
          sac print_ident ls.ls_name
          (print_list comma (print_type info)) ls.ls_args
          (if ls.ls_args = [] then "" else " -> ")
          (print_option_or_default "prop" (print_type info)) ls.ls_value
    | Some ld ->
        let vl,e = open_ls_defn ld in
        begin match e with
          | Term t ->
              (* TODO AC? *)
              fprintf fmt "@[<hov 2>function %a(%a) : %a =@ %a@]@\n"
                print_ident ls.ls_name
                (print_list comma (print_logic_binder info)) vl
                (print_type info) (Util.of_option ls.ls_value)
                (print_term info) t
          | Fmla f ->
              fprintf fmt "@[<hov 2>predicate %a(%a) =@ %a@]"
                print_ident ls.ls_name
                (print_list comma (print_logic_binder info)) vl
                (print_fmla info) f
        end;
        List.iter forget_var vl

let print_logic_decl info fmt d =
  if Sid.mem (fst d).ls_name info.info_rem then
    false else (print_logic_decl info fmt d; true)

let print_decl info fmt d = match d.d_node with
  | Dtype dl ->
      print_list_opt newline (print_type_decl info) fmt dl
  | Dlogic dl ->
      print_list_opt newline (print_logic_decl info) fmt dl
  | Dind _ -> unsupportedDecl d
      "alt-ergo : inductive definition are not supported"
  | Dprop (Paxiom, pr, _) when Sid.mem pr.pr_name info.info_rem -> false
  | Dprop (Paxiom, pr, f) ->
      fprintf fmt "@[<hov 2>axiom %a :@ %a@]@\n"
        print_ident pr.pr_name (print_fmla info) f; true
  | Dprop (Pgoal, pr, f) ->
      fprintf fmt "@[<hov 2>goal %a :@ %a@]@\n"
        print_ident pr.pr_name (print_fmla info) f; true
  | Dprop ((Plemma|Pskip), _, _) ->
      assert false

let print_decl info fmt = catch_unsupportedDecl (print_decl info fmt)

let print_task pr thpr fmt task =
  print_prelude fmt pr;
  print_th_prelude task fmt thpr;
  let info = {
    info_syn = get_syntax_map task;
    info_rem = get_remove_set task;
    info_ac  = Task.on_tagged_ls meta_ac task }
  in
  let decls = Task.task_decls task in
  ignore (print_list_opt (add_flush newline2) (print_decl info) fmt decls)

let () = register_printer "alt-ergo"
  (fun _env pr thpr ?old:_ fmt task ->
     forget_all ident_printer;
     print_task pr thpr fmt task)

(*
let print_goal info fmt (id, f, task) =
  print_task info fmt task;
  fprintf fmt "@\n@[<hov 2>goal %a : %a@]@\n" print_ident id (print_fmla info) f
*)

