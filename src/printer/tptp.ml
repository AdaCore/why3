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

open Format
open Pp
open Ident
open Ty
open Term
open Decl
open Task
open Printer

let ident_printer =
  (* let bls = ["and";" benchmark";" distinct";"exists";"false";"flet";"forall";
     "if then else";"iff";"implies";"ite";"let";"logic";"not";"or";
     "sat";"theory";"true";"unknown";"unsat";"xor";
     "assumption";"axioms";"defintion";"extensions";"formula";
     "funs";"extrafuns";"extrasorts";"extrapreds";"language";
     "notes";"preds";"sorts";"status";"theory";"Int";"Real";"Bool";
     "Array";"U";"select";"store"] in *)
  let bls = ["fof"; "axiom"; "conjecture"; "&"; "="; "!="; "!"; "|"; "=>";
      "~"; "?"; "itef"] in
  let san = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer bls ~sanitizer:san

let print_symbol fmt id =
  let san = String.uncapitalize in
  fprintf fmt "%s" (id_unique ~sanitizer:san ident_printer id)

let print_var fmt {vs_name = id} =
  let san = String.capitalize in
  fprintf fmt "%s" (id_unique ~sanitizer:san ident_printer id)

let forget_var v = forget_id ident_printer v.vs_name

type info = {
  info_syn : string Mid.t;
  info_rem : Sid.t;
}

let rec print_term info fmt t = match t.t_node with
  | Tbvar _ -> assert false
  | Tconst c -> fprintf fmt "'%a'"
      Pretty.print_const c
  | Tvar v -> print_var fmt v
  | Tapp (ls, tl) -> begin match query_syntax info.info_syn ls.ls_name with
      | Some s -> syntax_arguments s (print_term info) fmt tl
      | None -> begin match tl with (* toto() is not accepted *)
          | [] -> fprintf fmt "@[%a@]" print_symbol ls.ls_name
          | _ -> fprintf fmt "@[%a(%a)@]"  print_symbol ls.ls_name
                (print_list comma (print_term info)) tl
          end
      end
  | Tlet (_,_) -> unsupportedTerm t
      "tptp : you must eliminate let"
  | Tif (f1,t1,t2) ->
      fprintf fmt "@[itef(%a,@ %a,@ %a)@]"
        (print_fmla info) f1 (print_term info) t1 (print_term info) t2
  | Tcase _ -> unsupportedTerm t
      "tptp : you must eliminate match"
  | Teps _ -> unsupportedTerm t
      "tptp : you must eliminate epsilon"

and print_fmla info fmt f = match f.f_node with
  | Fapp ({ ls_name = id }, []) ->
      print_symbol fmt id
  | Fapp (ls, tl) -> begin match query_syntax info.info_syn ls.ls_name with
      | Some s -> syntax_arguments s (print_term info) fmt tl
      | None -> fprintf fmt "@[%a(%a)@]"
	      print_symbol ls.ls_name (print_list comma (print_term info)) tl
      end
  | Fquant (q, fq) ->
      let q = match q with Fforall -> "!" | Fexists -> "?" in
      let vl, _tl, f = f_open_quant fq in
      (* TODO trigger *)
      fprintf fmt "%s [%a] :@ %a" q (print_list comma print_var) vl (print_fmla info) f;
      List.iter forget_var vl
  | Fbinop (Fand, f1, f2) ->
      fprintf fmt "@[(%a@ & %a)@]" (print_fmla info) f1 (print_fmla info) f2
  | Fbinop (For, f1, f2) ->
      fprintf fmt "@[(%a@ | %a)@]" (print_fmla info) f1 (print_fmla info) f2
  | Fbinop (Fimplies, f1, f2) ->
      fprintf fmt "@[(%a@ => %a)@]"
        (print_fmla info) f1 (print_fmla info) f2
  | Fbinop (Fiff, f1, f2) ->
      fprintf fmt "@[(%a@ <=> %a)@]" (print_fmla info) f1 (print_fmla info) f2
  | Fnot f ->
      fprintf fmt "@[~@ (%a)@]" (print_fmla info) f
  | Ftrue ->
      fprintf fmt "$true"
  | Ffalse ->
      fprintf fmt "$false"
  | Fif (_,_,_) -> unsupportedFmla f "Fif not supported"
      (* fprintf fmt "@[(if_then_else %a@ %a@ %a)@]"
	(print_fmla info) f1 (print_fmla info) f2 (print_fmla info) f3 *)
  | Flet (_, _) -> unsupportedFmla f "Flet not supported"
      (* let v, f2 = f_open_bound tb in
      fprintf fmt "@[(let (%a %a)@ %a)@]" print_var v
        (print_term info) t1 (print_fmla info) f2;
      forget_var v *)
  | Fcase _ -> unsupportedFmla f
      "tptp : you must eliminate match"

and print_expr info fmt = e_apply (print_term info fmt) (print_fmla info fmt)

and print_triggers info fmt tl = print_list comma (print_expr info) fmt tl


let print_logic_decl _ _ (_,ld) = match ld with
  | None -> ()
  | Some _ -> unsupported "Predicate and function definition aren't supported"

let print_logic_decl info fmt d =
  if Sid.mem (fst d).ls_name info.info_rem then
    false else (print_logic_decl info fmt d; true)

let print_decl info fmt d = match d.d_node with
  | Dtype _ -> false
      (* print_list_opt newline (print_type_decl info) fmt dl *)
  | Dlogic dl ->
      print_list_opt newline (print_logic_decl info) fmt dl
  | Dind _ -> unsupportedDecl d
      "tptp : inductive definition are not supported"
  | Dprop (Paxiom, pr, _) when Sid.mem pr.pr_name info.info_rem -> false
  | Dprop (Paxiom, pr, f) ->
      fprintf fmt "@[<hov 2>fof(%s, axiom,@ %a).@]@\n"
        (id_unique ~sanitizer:String.uncapitalize ident_printer pr.pr_name)
        (print_fmla info) f; true
  | Dprop (Pgoal, pr, f) -> (* TODO : what is pr ? *)
      fprintf fmt "@[<hov 2>fof(%s, conjecture,@ %a ).@]@\n"
        (id_unique ~sanitizer:String.uncapitalize ident_printer pr.pr_name)
        (print_fmla info) f; true
      (* fprintf fmt "@[;; %a@]@\n" print_ident pr.pr_name; *)
  | Dprop ((Plemma|Pskip), _, _) -> assert false

let print_decl info fmt = catch_unsupportedDecl (print_decl info fmt)

let print_task pr thpr fmt task =
  print_prelude fmt pr;
  print_th_prelude task fmt thpr;
  let info = {
    info_syn = get_syntax_map task;
    info_rem = get_remove_set task }
  in
  let decls = Task.task_decls task in
  ignore (print_list_opt (add_flush newline2) (print_decl info) fmt decls)

let () = register_printer "tptp"
  (fun _env pr thpr ?old:_ fmt task ->
     forget_all ident_printer;
     print_task pr thpr fmt task)

