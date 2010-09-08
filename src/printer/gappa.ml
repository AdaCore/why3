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

(** Gappa printer *)

open Format
open Pp
open Printer
open Ident
open Ty
open Term
open Decl
open Task


let ident_printer = 
  let bls = [
  ] 
  in
  let san = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer bls ~sanitizer:san

let print_ident fmt id =
  fprintf fmt "%s" (id_unique ident_printer id)

let constant_value t =
  match t.t_node with
    | Tconst (ConstInt s) -> s
    | _ -> raise Not_found

(* terms *)

let print_term fmt t = match t.t_node with
  | Tbvar _ -> 
      assert false
  | Tconst c ->
      Pretty.print_const fmt c
  | Tvar { vs_name = id } ->
      print_ident fmt id
  | Tapp (ls, _tl) -> 
      unsupportedTerm t 
        ("gappa: function '" ^ ls.ls_name.id_string ^ "' is not supported")
(*
begin match query_syntax info.info_syn ls.ls_name with
      | Some s -> syntax_arguments s (print_term info) fmt tl
      | None -> fprintf fmt "%a%a" print_ident ls.ls_name (print_tapp info) tl
    end
*)
  | Tlet _ -> unsupportedTerm t
      "gappa: you must eliminate let in term"
  | Tif _ -> unsupportedTerm t 
      "gappa: you must eliminate if_then_else"
  | Tcase _ -> unsupportedTerm t 
      "gappa: you must eliminate match"
  | Teps _ -> unsupportedTerm t 
      "gappa : you must eliminate epsilon"


(* predicates *)

let rec print_fmla fmt f = match f.f_node with
  | Fapp ({ ls_name = id }, []) ->
      print_ident fmt id
  | Fapp (ls, [t1;t2]) when ls == ps_equ -> 
      begin try
        let c1 = constant_value t1 in
        fprintf fmt "%a in [%s,%s]" print_term t2 c1 c1          
      with Not_found ->
        try
          let c2 = constant_value t2 in
          fprintf fmt "%a in [%s,%s]" print_term t1 c2 c2          
        with Not_found ->
          fprintf fmt "%a - %a in [0,0]" print_term t1 print_term t2           
      end
  | Fapp (ls, _tl) -> 
      unsupportedFmla f 
        ("gappa: predicate '" ^ ls.ls_name.id_string ^ "' is not supported")
(*
begin match query_syntax info.info_syn ls.ls_name with
      | Some s -> syntax_arguments s (print_term info) fmt tl
      | None -> fprintf fmt "%a(%a)" print_ident ls.ls_name 
                    (print_list comma (print_term info)) tl
    end
*)
  | Fquant (_q, _fq) ->
      unsupportedFmla f 
        "gappa: quantifiers are not supported"     
(*
      let q = match q with Fforall -> "forall" | Fexists -> "exists" in
      let vl, tl, f = f_open_quant fq in
      let forall fmt v = 
	fprintf fmt "%s %a:%a" q print_ident v.vs_name (print_type info) v.vs_ty
      in
      fprintf fmt "@[(%a%a.@ %a)@]" (print_list dot forall) vl
        (print_triggers info) tl (print_fmla info) f;
      List.iter forget_var vl
*)
  | Fbinop (Fand, f1, f2) ->
      fprintf fmt "(%a /\\@ %a)" print_fmla f1 print_fmla f2
  | Fbinop (For, f1, f2) ->
      fprintf fmt "(%a \\/@ %a)" print_fmla f1 print_fmla f2
  | Fbinop (Fimplies, f1, f2) ->
      fprintf fmt "(%a ->@ %a)" print_fmla f1 print_fmla f2
  | Fbinop (Fiff, _f1, _f2) ->
      unsupportedFmla f 
        "gappa: connector <-> is not supported"     
  | Fnot f ->
      fprintf fmt "not %a" print_fmla f
  | Ftrue -> 
      fprintf fmt "(0 in [0,0])"
  | Ffalse ->
      fprintf fmt "(1 in [0,0])"
  | Fif (_f1, _f2, _f3) ->
      unsupportedFmla f
        "gappa: you must eliminate if in formula"
  | Flet _ -> unsupportedFmla f
      "gappa: you must eliminate let in formula"
  | Fcase _ -> unsupportedFmla f 
      "gappa: you must eliminate match"
  
let print_decl (* ?old *) fmt d = 
  match d.d_node with
  | Dtype _ -> ()
(*
unsupportedDecl d 
      "gappa : type declarations are not supported"
*)
  | Dlogic _ -> ()
(*
unsupportedDecl d 
      "gappa : logic declarations are not supported"
*)
  | Dind _ -> unsupportedDecl d 
      "gappa: inductive definitions are not supported"
  | Dprop (Paxiom, _pr, _f) -> ()
(*
      unsupportedDecl d 
        "gappa: axioms are not supported"
*)
  | Dprop (Pgoal, pr, f) ->
      fprintf fmt "# goal '%a'@\n" print_ident pr.pr_name;
      fprintf fmt "@[<hv 2>{ %a@ }@]@\n" print_fmla f
  | Dprop ((Plemma|Pskip), _, _) ->
      unsupportedDecl d 
        "gappa: lemmas are not supported"

let print_decl ?old fmt = 
  ignore(old);
  catch_unsupportedDecl (print_decl (* ?old *) fmt)

let print_decls ?old fmt dl =
  fprintf fmt "@[<hov>%a@\n@]" (print_list nothing (print_decl ?old)) dl

let print_task pr thpr ?old fmt task =
(*
  forget_all ();
*)
  print_prelude fmt pr;
  print_th_prelude task fmt thpr;
  print_decls ?old fmt (Task.task_decls task)

let () = register_printer "gappa" print_task


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
