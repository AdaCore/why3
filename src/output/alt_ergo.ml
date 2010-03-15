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
open Theory

let ident_printer = 
  let bls = ["let"; "forall"; "exists"; "and"; "or"] in
  let san = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer bls ~sanitizer:san

let print_ident fmt id =
  fprintf fmt "%s" (id_unique ident_printer id)

let forget_var v = forget_id ident_printer v.vs_name

let rec print_type drv fmt ty = match ty.ty_node with
  | Tyvar id -> 
      fprintf fmt "'%a" print_ident (tv_name id)
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
                    fprintf fmt "%a %a" (print_type drv) ty print_ident ts.ts_name
                | Tyapp (ts, tyl) ->
                    fprintf fmt "(%a) %a" 
	              (print_list comma (print_type drv)) tyl print_ident ts.ts_name
            end
let rec print_term drv fmt t = match t.t_node with
  | Tbvar _ -> 
      assert false
  | Tconst c ->
      Pretty.print_const fmt c
  | Tvar { vs_name = id } ->
      print_ident fmt id
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
              fprintf fmt "%a(%a)" 
	        print_ident ls.ls_name (print_list comma (print_term drv)) tl
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
              fprintf fmt "%a(%a)" 
	        print_ident ls.ls_name (print_list comma (print_term drv)) tl
      end
  | Fquant (q, fq) ->
      let q = match q with Fforall -> "forall" | Fexists -> "exists" in
      let vl, tl, f = f_open_quant fq in
      let forall fmt v = 
	fprintf fmt "%s %a:%a" q print_ident v.vs_name (print_type drv) v.vs_ty
      in
      fprintf fmt "@[<hov2>(%a%a.@ %a)@]" (print_list dot forall) vl
        (print_list alt (print_triggers drv)) tl (print_fmla drv) f;
      List.iter forget_var vl
  | Fbinop (Fand, f1, f2) ->
      fprintf fmt "(%a and %a)" (print_fmla drv) f1 (print_fmla drv) f2
  | Fbinop (For, f1, f2) ->
      fprintf fmt "(%a or %a)" (print_fmla drv) f1 (print_fmla drv) f2
  | Fbinop (Fimplies, f1, f2) ->
      fprintf fmt "(%a -> %a)" (print_fmla drv) f1 (print_fmla drv) f2
  | Fbinop (Fiff, f1, f2) ->
      fprintf fmt "(%a <-> %a)" (print_fmla drv) f1 (print_fmla drv) f2
  | Fnot f ->
      fprintf fmt "(not %a)" (print_fmla drv) f
  | Ftrue ->
      fprintf fmt "true"
  | Ffalse ->
      fprintf fmt "false"
  | Fif (f1, f2, f3) ->
      fprintf fmt "((%a and %a) or (not %a and %a))"
	(print_fmla drv) f1 (print_fmla drv) f2 (print_fmla drv) f1 (print_fmla drv) f3
  | Flet _ ->
      assert false
  | Fcase _ ->
      assert false

and print_trigger drv fmt = function
  | Term t -> (print_term drv) fmt t
  | Fmla f -> (print_fmla drv) fmt f

and print_triggers drv fmt tl = print_list comma (print_trigger drv) fmt tl


let print_logic_binder drv fmt v =
  fprintf fmt "%a: %a" print_ident v.vs_name (print_type drv) v.vs_ty

let print_type_decl drv fmt = function
  | ts, Tabstract ->
      begin
        match Driver.query_ident drv ts.ts_name with
          | Driver.Remove | Driver.Syntax _ -> false
          | Driver.Tag _ -> fprintf fmt "type %a" print_ident ts.ts_name; true
      end
  | _, Talgebraic _ ->
      assert false

let ac_th = ["algebra";"AC"]


let print_ld drv fmt ld =
  let _,vl,e = open_ls_defn ld in
  begin match e with
    | Term t -> print_term drv fmt t
    | Fmla f -> print_fmla drv fmt f
  end;
  List.iter forget_var vl

let print_ls_defn drv fmt = 
  Util.option_iter (fprintf fmt " =@ %a" (print_ld drv))

let print_ls_type drv fmt = function
  | Some ty -> print_type drv fmt ty
  | None -> fprintf fmt "prop"

let print_logic_decl drv ctxt fmt (ls,ld) =
  match Driver.query_ident drv ls.ls_name with
    | Driver.Remove | Driver.Syntax _ -> false
    | Driver.Tag s ->
        begin match ld with
          | None ->
              let sac = if Snm.mem "AC" s then "ac " else "" in
              fprintf fmt "@[<hov 2>logic %s%a : %a -> %a@]@\n"
                sac print_ident ls.ls_name
                (print_list comma (print_type drv)) ls.ls_args 
                (print_ls_type drv) ls.ls_value
          | Some ld ->
              let _,vl,e = open_ls_defn ld in
              begin match e with
                | Term t ->
                    (* TODO AC? *)
                    fprintf fmt "@[<hov 2>function %a(%a) : %a =@ %a@]@\n" 
                      print_ident ls.ls_name
                      (print_list comma (print_logic_binder drv)) vl 
                      (print_type drv) (Util.of_option ls.ls_value) 
                      (print_term drv) t
                | Fmla f ->
                    fprintf fmt "@[<hov 2>predicate %a(%a) = %a@]"
	              print_ident ls.ls_name 
                      (print_list comma (print_logic_binder drv)) vl 
                      (print_fmla drv) f
              end;
              List.iter forget_var vl
        end;
        true
  
let print_decl drv ctxt fmt d = match d.d_node with
  | Dtype dl ->
      print_list_opt newline (print_type_decl drv) fmt dl
  | Dlogic dl ->
      print_list_opt newline (print_logic_decl drv ctxt) fmt dl
  | Dind _ -> assert false (* TODO *)
  | Dprop (Paxiom, pr, _) when
      Driver.query_ident drv (pr_name pr) = Driver.Remove -> false
  | Dprop (Paxiom, pr, f) ->
      fprintf fmt "@[<hov 2>axiom %a :@ %a@]@\n" 
        print_ident (pr_name pr) (print_fmla drv) f; true
  | Dprop (Pgoal, pr, f) ->
      fprintf fmt "@[<hov 2>goal %a :@ %a@]@\n"
        print_ident (pr_name pr) (print_fmla drv) f; true
  | Dprop (Plemma, _, _) ->
      assert false
  | Duse _ | Dclone _ -> false

let print_context drv fmt ctxt = 
  let decls = Context.get_decls ctxt in
  ignore (print_list_opt newline2 (print_decl drv ctxt) fmt decls)

let () = Driver.register_printer "alt-ergo" 
  (fun drv fmt ctxt -> 
     forget_all ident_printer;
     print_context drv fmt ctxt)

let print_goal drv fmt (id, f, ctxt) =
  print_context drv fmt ctxt;
  fprintf fmt "@\n@[<hov 2>goal %a : %a@]@\n" print_ident id (print_fmla drv) f
