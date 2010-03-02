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

let print_list_paren x = print_list_delim lparen rparen x

let print_ident =
  let printer = create_printer () in
  let print fmt id = Format.fprintf fmt "%s" (id_unique printer id) in
  print

let print_typevar fmt x =
  fprintf fmt "'%a" print_ident x

let rec print_ty fmt ty = match ty.ty_node with
  | Tyvar n ->
      fprintf fmt "'%a" print_ident n
  | Tyapp (s, []) -> 
      print_ident fmt s.ts_name
  | Tyapp (s, [t]) -> 
      fprintf fmt "%a %a" print_ty t print_ident s.ts_name
  | Tyapp (s, l) -> 
      fprintf fmt "(%a)@ %a" (print_list comma print_ty) l print_ident s.ts_name
  
let rec print_term fmt t = match t.t_node with
  | Tbvar n -> 
      assert false
  | Tvar n -> 
      print_ident fmt n.vs_name
  | Tconst _ ->
      fprintf fmt "[const]"
  | Tapp (s, tl) ->
      fprintf fmt "(%a(%a)@ : %a)" 
	print_ident s.fs_name (print_list comma print_term) tl
	print_ty t.t_ty
  | Tlet (t1,tbound) -> 
      let vs,t2 = t_open_bound tbound in
      fprintf fmt "(let %a = %a in@ %a)"
      print_ident vs.vs_name print_term t1 print_term t2
  | Tcase _ -> assert false (*TODO*)
  | Teps _ -> assert false

let print_vs fmt vs = 
  fprintf fmt "%a :@ %a" print_ident vs.vs_name print_ty vs.vs_ty

let rec print_fmla fmt f = match f.f_node with
  | Fapp (s,tl) -> 
      fprintf fmt "(%a(%a))" 
	print_ident s.ps_name (print_list comma print_term) tl
  | Fquant (q,fquant) ->
      let vl,tl,f = f_open_quant fquant in
      fprintf fmt "(%s %a %a.@ %a)"
        (match q with Fforall -> "forall" | Fexists -> "exists")
        (print_list comma print_vs) vl print_tl tl print_fmla f
  | Ftrue -> fprintf fmt "true"
  | Ffalse -> fprintf fmt "false)"
  | Fbinop (b,f1,f2) -> 
      fprintf fmt "(%a@ %s@ %a)"
        print_fmla f1
        (match b with 
           | Fand -> "and" | For -> "or" 
           | Fimplies -> "->" | Fiff -> "<->")
        print_fmla f2
  | Fnot f -> fprintf fmt "(not@ %a)" print_fmla f
  | _ -> assert false (*TODO*) 

and print_tl fmt tl =
  fprintf fmt "[%a]" (print_list alt (print_list comma print_tr)) tl

and print_tr fmt = function
  | TrTerm t -> print_term fmt t
  | TrFmla f -> print_fmla fmt f


let print_fsymbol fmt {fs_name = fs_name; fs_scheme = tyl,ty} = 
  fprintf fmt "%a%a :@ %a" 
    print_ident fs_name
    (print_list_paren comma print_ty) tyl 
    print_ty ty

let print_psymbol fmt {ps_name = ps_name; ps_scheme = tyl} = 
  fprintf fmt "%a%a" 
    print_ident ps_name
    (print_list_paren comma print_ty) tyl 

let print_ty_decl fmt (ts,tydef) = match tydef,ts.ts_def with
  | Tabstract,None -> fprintf fmt "type %a %a" 
      (print_list_paren comma print_typevar) ts.ts_args
      print_ident ts.ts_name
  | Tabstract,Some f -> fprintf fmt "type %a %a =@ %a" 
      (print_list_paren comma print_typevar) ts.ts_args
      print_ident ts.ts_name
      print_ty f
  | Talgebraic d, None -> fprintf fmt "type %a %a =@ %a" 
      (print_list_paren comma print_typevar) ts.ts_args
      print_ident ts.ts_name
      (print_list newline print_fsymbol) d
  | Talgebraic _, Some _ -> assert false

let print_vsymbol fmt {vs_name = vs_name; vs_ty = vs_ty} =
  fprintf fmt "%a :@ %a" print_ident vs_name print_ty vs_ty

let print_logic_decl fmt = function
  | Lfunction (fs,None) -> fprintf fmt "@[<hov 2>logic %a@]" print_fsymbol fs
  | Lfunction (fs,Some fd) -> 
      fprintf fmt "@[<hov 2>logic %a :@ %a@]" print_ident fs.fs_name
        print_fmla fd
  | Lpredicate (fs,None) -> fprintf fmt "@[<hov 2>logic %a@]" print_psymbol fs
  | Lpredicate (ps,Some fd) -> 
      fprintf fmt "@[<hov 2>logic %a :@ %a@]" print_ident ps.ps_name
        print_fmla fd
  | Linductive _ -> assert false (*TODO*)

let print_decl fmt d = match d.d_node with
  | Dtype tl -> fprintf fmt "(* *)@\n%a" (print_list newline print_ty_decl) tl
  | Dlogic ldl -> fprintf fmt "(* *)@\n%a" 
      (print_list newline print_logic_decl) ldl 
  | Dprop (k,id,fmla) -> 
      fprintf fmt "%s %a :@ %a@\n" 
        (match k with Paxiom -> "axiom" | Pgoal -> "goal" | Plemma -> "lemma")
        print_ident id
        print_fmla fmla

let print_decl_or_use fmt = function
  | Decl d -> fprintf fmt "%a" print_decl d
  | Use u -> fprintf fmt "use export %a@\n" print_ident u.th_name

let print_theory fmt t =
  fprintf fmt "@[@[<hov 2>theory %a@\n%a@]@\nend@]@\n@\n" print_ident t.th_name 
    (print_list newline print_decl_or_use) t.th_decls;
  fprintf fmt "@?"

