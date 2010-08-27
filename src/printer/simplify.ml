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
  let bls = ["select";"store"] in
  let san = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer bls ~sanitizer:san

let print_ident fmt id =
  fprintf fmt "%s" (id_unique ident_printer id)

let forget_var v = forget_id ident_printer v.vs_name

let print_var fmt {vs_name = id} = print_ident fmt id

let simplify_max_int = Int64.of_string "2147483646"

let pp_exp fmt e =
  if e="" then () else
    if e.[0] = '-' then
      fprintf fmt "minus%s" (String.sub e 1 (String.length e - 1))
    else
      fprintf fmt "%s" e

let print_real fmt = function
  | RConstDecimal (i, f, e) -> 
      fprintf fmt "%s_%se%a" i f (Pp.print_option pp_exp) e
  | RConstHexa (i, f, e) -> 
      fprintf fmt "0x%s_%sp%a" i f pp_exp e

type info = {
  info_syn : string Mid.t;
  info_rem : Sid.t;
}

let rec print_term info fmt t = match t.t_node with
  | Tbvar _ -> 
      assert false
  | Tconst (ConstInt n) ->
      begin try 
	let n64 = Int64.of_string n in
	if n64 < 0L || n64 > simplify_max_int then raise Exit;
	fprintf fmt "%s" n
      with _ -> (* the constant is too large for Simplify *)
	fprintf fmt "constant_too_large_%s" n
      end
  | Tconst (ConstReal c) ->
      fprintf fmt "real_constant_%a" print_real c 
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

and print_fmla info fmt f = match f.f_node with
  | Fapp ({ ls_name = id }, []) ->
      print_ident fmt id
  | Fapp (ls, tl) -> begin match query_syntax info.info_syn ls.ls_name with
      | Some s -> 
	  syntax_arguments s (print_term info) fmt tl
      | None -> 
	  fprintf fmt "(EQ (%a@ %a) |@@true|)" 
	    print_ident ls.ls_name (print_list space (print_term info)) tl 
    end
  | Fquant (q, fq) ->
      let q = match q with Fforall -> "FORALL" | Fexists -> "EXISTS" in
      let vl, tl, f = f_open_quant fq in
      fprintf fmt "@[(%s (%a)%a@ %a)@]" q (print_list space print_var) vl 
	(print_triggers info) tl (print_fmla info) f;
      List.iter forget_var vl
  | Fbinop (Fand, f1, f2) ->
      fprintf fmt "@[(AND@ %a@ %a)@]" (print_fmla info) f1 (print_fmla info) f2
  | Fbinop (For, f1, f2) ->
      fprintf fmt "@[(OR@ %a@ %a)@]" (print_fmla info) f1 (print_fmla info) f2
  | Fbinop (Fimplies, f1, f2) ->
      fprintf fmt "@[(IMPLIES@ %a@ %a)@]" 
        (print_fmla info) f1 (print_fmla info) f2
  | Fbinop (Fiff, f1, f2) ->
      fprintf fmt "@[(IFF@ %a@ %a)@]" (print_fmla info) f1 (print_fmla info) f2
  | Fnot f ->
      fprintf fmt "@[(NOT@ %a)@]" (print_fmla info) f
  | Ftrue ->
      fprintf fmt "TRUE"
  | Ffalse ->
      fprintf fmt "FALSE"
  | Fif _ ->
      unsupportedFmla f "simplify : you must eliminate if"
  | Flet _ ->
      unsupportedFmla f "simplify : you must eliminate let"
  | Fcase _ -> 
      unsupportedFmla f "simplify : you must eliminate match"
      
and print_expr info fmt = e_apply (print_term info fmt) (print_fmla info fmt)

and print_trigger info fmt = function
  | [] -> ()
  | [Term ({t_node=Tvar _} as t)] -> fprintf fmt "(MPAT %a)" (print_term info) t
  | [t] -> print_expr info fmt t
  | tl -> fprintf fmt "(MPAT %a)" (print_list space (print_expr info)) tl

and print_triggers info fmt = function
  | [] -> ()
  | tl -> fprintf fmt "@ (PATS %a)" (print_list space (print_trigger info)) tl

let print_logic_decl _drv _fmt (_ls,ld) = match ld with
  | None ->
      ()
  | Some _ -> 
      (* TODO: predicate definitions could actually be passed to Simplify *)
      unsupported "Predicate and function definition aren't supported"

let print_logic_decl info fmt d = 
  if Sid.mem (fst d).ls_name info.info_rem then false 
  else begin print_logic_decl info fmt d; true end
  
let print_decl info fmt d = match d.d_node with
  | Dtype _ ->
      false
  | Dlogic dl ->
      print_list_opt newline (print_logic_decl info) fmt dl
  | Dind _ -> 
      unsupportedDecl d "simplify : inductive definition are not supported"
  | Dprop (Paxiom, pr, _) when Sid.mem pr.pr_name info.info_rem -> 
      false
  | Dprop (Paxiom, pr, f) ->
      fprintf fmt "@[(BG_PUSH@\n ;; axiom %s@\n @[<hov 2>%a@])@]@\n"
        pr.pr_name.id_string (print_fmla info) f; 
      true
  | Dprop (Pgoal, pr, f) ->
      fprintf fmt "@[;; %a@]@\n" print_ident pr.pr_name;
      begin match id_from_user pr.pr_name with
        | None -> ()
        | Some loc -> fprintf fmt " @[;; %a@]@\n" 
            Loc.gen_report_position loc 
      end;
      fprintf fmt "@[<hov 2>%a@]@\n" (print_fmla info) f;
      true
  | Dprop ((Plemma|Pskip), _, _) -> 
      assert false

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

let () = register_printer "simplify" 
  (fun pr thpr fmt task ->
     forget_all ident_printer;
     print_task pr thpr fmt task)

