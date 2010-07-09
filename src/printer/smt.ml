(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
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
  let bls = ["and";" benchmark";" distinct";"exists";"false";"flet";"forall";
     "if then else";"iff";"implies";"ite";"let";"logic";"not";"or";
     "sat";"theory";"true";"unknown";"unsat";"xor";
     "assumption";"axioms";"defintion";"extensions";"formula";
     "funs";"extrafuns";"extrasorts";"extrapreds";"language";
     "notes";"preds";"sorts";"status";"theory";"Int";"Real";"Bool";
     "Array";"U";"select";"store"] in
  let san = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer bls ~sanitizer:san

let print_ident fmt id =
  fprintf fmt "%s" (id_unique ident_printer id)

let forget_var v = forget_id ident_printer v.vs_name

let print_var fmt {vs_name = id} =
  let sanitize n = "?" ^ n in
  let n = id_unique ident_printer ~sanitizer:sanitize id in
  fprintf fmt "%s" n

type info = {
  info_syn : syntax_map;
  info_rem : Sid.t;
}

let rec print_type info fmt ty = match ty.ty_node with
  | Tyvar _ -> unsupported "smt : you must encode the polymorphism"
  | Tyapp (ts, tl) -> begin match query_syntax info.info_syn ts.ts_name with 
      | Some s -> syntax_arguments s (print_type info) fmt tl
      | None -> fprintf fmt "%a%a" (print_tyapp info) tl print_ident ts.ts_name
    end

and print_tyapp info fmt = function
  | [] -> ()
  | [ty] -> fprintf fmt "%a " (print_type info) ty
  | tl -> fprintf fmt "(%a) " (print_list comma (print_type info)) tl

let print_type info fmt = catch_unsupportedType (print_type info fmt)

let rec print_term info fmt t = match t.t_node with
  | Tbvar _ -> assert false
  | Tconst (ConstInt n) -> fprintf fmt "%s" n
  | Tconst (ConstReal c) ->
      Print_real.print_with_integers 
	"%s.0" "(* %s.0 %s.0)" "(/ %s.0 %s.0)" fmt c
  | Tvar v -> print_var fmt v
  | Tapp (ls, tl) -> begin match query_syntax info.info_syn ls.ls_name with
      | Some s -> syntax_arguments s (print_term info) fmt tl
      | None -> begin match tl with (* for cvc3 wich doesn't accept (toto ) *)
          | [] -> fprintf fmt "@[%a@]" print_ident ls.ls_name
          | _ -> fprintf fmt "@[(%a@ %a)@]" 
	      print_ident ls.ls_name (print_list space (print_term info)) tl
        end end
  | Tlet (t1, tb) ->
      let v, t2 = t_open_bound tb in
      fprintf fmt "@[(let (%a %a)@ %a)@]" print_var v
        (print_term info) t1 (print_term info) t2;
      forget_var v
  | Tif (f1,t1,t2) -> 
      fprintf fmt "@[(ite %a@ %a@ %a)@]"
        (print_fmla info) f1 (print_term info) t1 (print_term info) t2
  | Tcase _ -> unsupportedTerm t 
      "smtv1 : you must eliminate match"
  | Teps _ -> unsupportedTerm t 
      "smtv1 : you must eliminate epsilon"

and print_fmla info fmt f = match f.f_node with
  | Fapp ({ ls_name = id }, []) ->
      print_ident fmt id
  | Fapp (ls, tl) -> begin match query_syntax info.info_syn ls.ls_name with
      | Some s -> syntax_arguments s (print_term info) fmt tl
      | None -> begin match tl with (* for cvc3 wich doesn't accept (toto ) *)
          | [] -> fprintf fmt "%a" print_ident ls.ls_name
          | _ -> fprintf fmt "(%a@ %a)" 
	      print_ident ls.ls_name (print_list space (print_term info)) tl 
        end end
  | Fquant (q, fq) ->
      let q = match q with Fforall -> "forall" | Fexists -> "exists" in
      let vl, _tl, f = f_open_quant fq in
      (* TODO trigger dépend des capacités du prover : 2 printers?
      smtwithtriggers/smtstrict *)
      let rec forall fmt = function
        | [] -> print_fmla info fmt f
        | v::l -> 
	    fprintf fmt "@[(%s (%a %a)@ %a)@]" q print_var v 
              (print_type info) v.vs_ty forall l
      in
      forall fmt vl;
      List.iter forget_var vl
  | Fbinop (Fand, f1, f2) ->
      fprintf fmt "@[(and@ %a@ %a)@]" (print_fmla info) f1 (print_fmla info) f2
  | Fbinop (For, f1, f2) ->
      fprintf fmt "@[(or@ %a@ %a)@]" (print_fmla info) f1 (print_fmla info) f2
  | Fbinop (Fimplies, f1, f2) ->
      fprintf fmt "@[(implies@ %a@ %a)@]" 
        (print_fmla info) f1 (print_fmla info) f2
  | Fbinop (Fiff, f1, f2) ->
      fprintf fmt "@[(iff@ %a@ %a)@]" (print_fmla info) f1 (print_fmla info) f2
  | Fnot f ->
      fprintf fmt "@[(not@ %a)@]" (print_fmla info) f
  | Ftrue ->
      fprintf fmt "true"
  | Ffalse ->
      fprintf fmt "false"
  | Fif (f1, f2, f3) ->
      fprintf fmt "@[(if_then_else %a@ %a@ %a)@]"
	(print_fmla info) f1 (print_fmla info) f2 (print_fmla info) f3
  | Flet (t1, tb) ->
      let v, f2 = f_open_bound tb in
      fprintf fmt "@[(let (%a %a)@ %a)@]" print_var v
        (print_term info) t1 (print_fmla info) f2;
      forget_var v
  | Fcase _ -> unsupportedFmla f 
      "smtv1 : you must eliminate match"
      
and print_expr info fmt = e_apply (print_term info fmt) (print_fmla info fmt)

and print_triggers info fmt tl = print_list comma (print_expr info) fmt tl


let print_logic_binder info fmt v =
  fprintf fmt "%a: %a" print_ident v.vs_name (print_type info) v.vs_ty

let print_type_decl info fmt = function
  | ts, Tabstract when Sid.mem ts.ts_name info.info_rem -> false
  | ts, Tabstract when ts.ts_args = [] ->
      fprintf fmt ":extrasorts (%a)" print_ident ts.ts_name; true
  | _, Tabstract -> unsupported 
          "smtv1 : type with argument are not supported"
  | _, Talgebraic _ -> unsupported 
          "smtv1 : algebraic type are not supported"

let print_logic_decl info fmt (ls,ld) = match ld with
  | None ->
      begin match ls.ls_value with
        | None ->
            fprintf fmt "@[<hov 2>:extrapreds ((%a %a))@]@\n"
              print_ident ls.ls_name
              (print_list space (print_type info)) ls.ls_args
        | Some value ->
            fprintf fmt "@[<hov 2>:extrafuns ((%a %a %a))@]@\n"
              print_ident ls.ls_name
              (print_list space (print_type info)) ls.ls_args 
              (print_type info) value
      end
  | Some _ -> unsupported 
      "Predicate and function definition aren't supported"

let print_logic_decl info fmt d = 
  if Sid.mem (fst d).ls_name info.info_rem then
    false else (print_logic_decl info fmt d; true)
  
let print_decl info fmt d = match d.d_node with
  | Dtype dl ->
      print_list_opt newline (print_type_decl info) fmt dl
  | Dlogic dl ->
      print_list_opt newline (print_logic_decl info) fmt dl
  | Dind _ -> unsupportedDecl d 
      "smt : inductive definition are not supported"
  | Dprop (Paxiom, pr, _) when Sid.mem pr.pr_name info.info_rem -> false
  | Dprop (Paxiom, pr, f) ->
      fprintf fmt "@[<hov 2>;; %s@\n:assumption@ %a@]@\n"
        pr.pr_name.id_string
        (print_fmla info) f; true
  | Dprop (Pgoal, pr, f) ->
      fprintf fmt "@[:formula@\n";
      fprintf fmt "@[;; %a@]@\n" print_ident pr.pr_name;
      (match id_from_user pr.pr_name with
        | None -> ()
        | Some loc -> fprintf fmt " @[;; %a@]@\n" 
            Loc.gen_report_position loc);
      fprintf fmt "  @[(not@ %a)@]" (print_fmla info) f;true
  | Dprop ((Plemma|Pskip), _, _) -> assert false

let print_decl info fmt = catch_unsupportedDecl (print_decl info fmt)

let print_task pr thpr syn fmt task = 
  fprintf fmt "(benchmark why3@\n" 
    (*print_ident (Task.task_goal task).pr_name*);
  fprintf fmt "  :status unknown@\n";
  print_prelude fmt pr;
  print_th_prelude task fmt thpr;
  let info = {
    info_syn = syn;
    info_rem = get_remove_set task }
  in
  let decls = Task.task_decls task in
  ignore (print_list_opt (add_flush newline2) (print_decl info) fmt decls);
  fprintf fmt "@\n)@."

let () = register_printer "smtv1" 
  (fun pr thpr syn fmt task -> 
     forget_all ident_printer;
     print_task pr thpr syn fmt task)
