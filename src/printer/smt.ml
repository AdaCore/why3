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

let print_tvsymbols fmt id = assert false

let forget_var v = forget_id ident_printer v.vs_name

let print_var fmt {vs_name = id} =
  let sanitize n = "?" ^ n in
  let n = id_unique ident_printer ~sanitizer:sanitize id in
  fprintf fmt "%s" n


let rec print_type drv fmt ty = match ty.ty_node with
  | Tyvar id -> 
      print_tvsymbols fmt id
  | Tyapp (ts, tl) -> 
      match Driver.query_ident drv ts.ts_name with
        | Driver.Remove -> assert false (* Mettre une erreur *)
        | Driver.Syntax s ->
            Driver.syntax_arguments s (print_type drv) fmt tl
        | Driver.Tag _ -> 
            begin
              match ty.ty_node with
                | Tyvar _ -> assert false
                | Tyapp (ts,[]) -> 
                    print_ident fmt ts.ts_name
                | Tyapp (ts, [ty]) -> 
                    fprintf fmt "%a %a" (print_type drv) 
                      ty print_ident ts.ts_name
                | Tyapp (ts, tyl) ->
                    fprintf fmt "(%a) %a" 
	              (print_list comma (print_type drv)) 
                      tyl print_ident ts.ts_name
            end
let rec print_term drv fmt t = match t.t_node with
  | Tbvar _ -> 
      assert false
  | Tconst c ->
      Pretty.print_const fmt c
  | Tvar v -> print_var fmt v
  | Tapp (ls, tl) ->
      begin      
        match Driver.query_ident drv ls.ls_name with
          | Driver.Remove -> assert false (* Mettre une erreur *)
          | Driver.Syntax s ->
              Driver.syntax_arguments s (print_term drv) fmt tl
          | Driver.Tag _ ->
              match tl with
                | [] -> print_ident fmt ls.ls_name
                | tl ->
              fprintf fmt "@[(%a %a)@]" 
	        print_ident ls.ls_name (print_list space (print_term drv)) tl
      end
  | Tlet (t1, tb) ->
      let v, t2 = t_open_bound tb in
      fprintf fmt "@[(let %a = %a@ in %a)@]" print_ident v.vs_name
        (print_term drv) t1 (print_term drv) t2;
      forget_var v
  | Tcase _ ->
      assert false
  | Teps _ ->
      assert false

let rec print_fmla drv fmt f = match f.f_node with
  | Fapp ({ ls_name = id }, []) ->
      print_ident fmt id
  | Fapp (ls, tl) ->
      begin      
        match Driver.query_ident drv ls.ls_name with
          | Driver.Remove -> assert false (* Mettre une erreur *)
          | Driver.Syntax s ->
              Driver.syntax_arguments s (print_term drv) fmt tl
          | Driver.Tag _ -> 
              fprintf fmt "(%a %a)" 
	        print_ident ls.ls_name (print_list space (print_term drv)) tl
      end
  | Fquant (q, fq) ->
      let q = match q with Fforall -> "forall" | Fexists -> "exists" in
      let vl, tl, f = f_open_quant fq in
      (* TODO trigger *)
      let rec forall fmt = function
        | [] -> print_fmla drv fmt f
        | v::l -> 
	    fprintf fmt "@[(%s (%a %a)@ %a)@]" q print_var v 
              (print_type drv) v.vs_ty forall l
      in
      forall fmt vl;
      List.iter forget_var vl
  | Fbinop (Fand, f1, f2) ->
      fprintf fmt "@[(and@ %a %a)@]" (print_fmla drv) f1 (print_fmla drv) f2
  | Fbinop (For, f1, f2) ->
      fprintf fmt "@[(or@ %a %a)@]" (print_fmla drv) f1 (print_fmla drv) f2
  | Fbinop (Fimplies, f1, f2) ->
      fprintf fmt "@[(implies@ %a %a)@]" 
        (print_fmla drv) f1 (print_fmla drv) f2
  | Fbinop (Fiff, f1, f2) ->
      fprintf fmt "@[(iff@ %a %a)@]" (print_fmla drv) f1 (print_fmla drv) f2
  | Fnot f ->
      fprintf fmt "@[(not@ %a)@]" (print_fmla drv) f
  | Ftrue ->
      fprintf fmt "true"
  | Ffalse ->
      fprintf fmt "false"
  | Fif (f1, f2, f3) ->
      fprintf fmt "@[(if_then_else %a %a %a@]" (* TODO Not sure *)
	(print_fmla drv) f1 (print_fmla drv) f2 (print_fmla drv) f3
  | Flet _ -> (* TODO *)
      assert false
  | Fcase _ ->
      assert false

and print_expr drv fmt = e_apply (print_term drv fmt) (print_fmla drv fmt)

and print_triggers drv fmt tl = print_list comma (print_expr drv) fmt tl


let print_logic_binder drv fmt v =
  fprintf fmt "%a: %a" print_ident v.vs_name (print_type drv) v.vs_ty

let print_type_decl drv fmt = function
  | ts, Tabstract ->
      begin
        match Driver.query_ident drv ts.ts_name with
          | Driver.Remove | Driver.Syntax _ -> false
          | Driver.Tag _ -> 
              match ts.ts_args with
                | [] -> fprintf fmt ":extrasorts (%a)" print_ident ts.ts_name;
                    true
                | _  -> assert false
      end
  | _, Talgebraic _ ->
      assert false

let print_logic_decl drv task fmt (ls,ld) =
  match Driver.query_ident drv ls.ls_name with
    | Driver.Remove | Driver.Syntax _ -> false
    | Driver.Tag s ->
        begin match ld with
          | None ->
              begin match ls.ls_value with
                | None ->
                    fprintf fmt "@[<hov 2>:extrapreds ((%a %a))@]@\n"
                      print_ident ls.ls_name
                      (print_list space (print_type drv)) ls.ls_args
                | Some value ->
                    fprintf fmt "@[<hov 2>:extrafuns ((%a %a %a))@]@\n"
                      print_ident ls.ls_name
                      (print_list space (print_type drv)) ls.ls_args 
                      (print_type drv) value
              end
          | Some ld -> assert false (* Dealt in Encoding *)
        end;
        true
  
let print_decl drv task fmt d = match d.d_node with
  | Dtype dl ->
      print_list_opt newline (print_type_decl drv) fmt dl
  | Dlogic dl ->
      print_list_opt newline (print_logic_decl drv task) fmt dl
  | Dind _ -> assert false (* TODO *)
  | Dprop (Paxiom, pr, _) when
      Driver.query_ident drv pr.pr_name = Driver.Remove -> false
  | Dprop (Paxiom, pr, f) ->
      fprintf fmt "@[<hov 2>:assumption@ %a@]@\n" 
        (print_fmla drv) f; true
  | Dprop (Pgoal, pr, f) ->
      fprintf fmt "@[:formula@\n";
      fprintf fmt "@[;; %a@]@\n" print_ident pr.pr_name;
      (match id_from_user pr.pr_name with
        | None -> ()
        | Some loc -> fprintf fmt " @[;; %a@]@\n" 
            Loc.gen_report_position loc);
      fprintf fmt "  @[(not@ %a)@]" (print_fmla drv) f;true
  | Dprop (Plemma, _, _) ->
      assert false

let print_context drv fmt task = 
  fprintf fmt "(benchmark toto@\n" 
    (*print_ident (Task.task_goal task).pr_name*);
  fprintf fmt "  :status unknown@\n";
  let decls = Task.task_decls task in
  ignore (print_list_opt (add_flush newline2) (print_decl drv task) fmt decls);
  fprintf fmt "@\n)@."

let () = Driver.register_printer "smtv1" 
  (fun drv fmt task -> 
     forget_all ident_printer;
     print_context drv fmt task)
