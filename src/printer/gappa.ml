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
open Theory
open Task

(* Gappa pre-compilation *)

type info = {
  info_symbols : Sls.t;
  info_ops_of_rel : (string * string) Mls.t;
  info_syn : string Mid.t;
  info_rem : Sid.t;
}

let int_le = ref ps_equ
let int_ge = ref ps_equ
let int_lt = ref ps_equ
let int_gt = ref ps_equ

let real_le = ref ps_equ
let real_ge = ref ps_equ
let real_lt = ref ps_equ
let real_gt = ref ps_equ

let single_value = ref ps_equ

let get_info = 
  let arith_symbols = ref None in
  let ops_of_rels = ref Mls.empty in
  fun env task ->
    let l =
      match !arith_symbols with 
	| None ->
            let int_theory = Env.find_theory env ["int"] "Int" in
            let find_int = Theory.ns_find_ls int_theory.Theory.th_export in
            let int_add = find_int ["infix +"] in
            let int_sub = find_int ["infix -"] in
            let int_mul = find_int ["infix *"] in
            int_le := Theory.ns_find_ls int_theory.Theory.th_export ["infix <="];
            int_ge := Theory.ns_find_ls int_theory.Theory.th_export ["infix >="];
            int_lt := Theory.ns_find_ls int_theory.Theory.th_export ["infix <"];
            int_gt := Theory.ns_find_ls int_theory.Theory.th_export ["infix >"];
            let int_abs_theory = Env.find_theory env ["int"] "Abs" in
            let int_abs = Theory.ns_find_ls int_abs_theory.Theory.th_export ["abs"] in
            let real_theory = Env.find_theory env ["real"] "Real" in
            let find_real = Theory.ns_find_ls real_theory.Theory.th_export in
            let real_add = find_real ["infix +"] in
            let real_sub = find_real ["infix -"] in
            let real_mul = find_real ["infix *"] in
            let real_div = find_real ["infix /"] in
            real_le := Theory.ns_find_ls real_theory.Theory.th_export ["infix <="];
            real_ge := Theory.ns_find_ls real_theory.Theory.th_export ["infix >="];
            real_lt := Theory.ns_find_ls real_theory.Theory.th_export ["infix <"];
            real_gt := Theory.ns_find_ls real_theory.Theory.th_export ["infix >"];
            let real_abs_theory = Env.find_theory env ["real"] "Abs" in
            let real_abs = Theory.ns_find_ls real_abs_theory.Theory.th_export ["abs"] in
	    let single_theory = Env.find_theory env ["floating_point"] "Single" in
	    single_value := Theory.ns_find_ls single_theory.Theory.th_export ["value"];
            (* sets of known symbols *)
            let l = 
              List.fold_right Sls.add 
                [ps_equ; 
                 int_add; int_sub; int_mul;
                 !int_le; !int_ge; !int_lt; !int_gt;
		 int_abs;
		 real_add; real_sub; real_mul; real_div;
                 !real_le; !real_ge; !real_lt; !real_gt;
                 real_abs;
		 !single_value] Sls.empty 
            in
            arith_symbols := Some l;
	    ops_of_rels :=
	      List.fold_left
		(fun acc (ls,op,rev_op) -> Mls.add ls (op,rev_op) acc)
		Mls.empty
		[ !int_le,"<=",">=" ;
		  !int_ge,">=","<=" ;
		  !int_lt,"<",">" ;
		  !int_gt,">","<" ;
		  !real_le,"<=",">=" ;
		  !real_ge,">=","<=" ;
		  !real_lt,"<",">" ;
		  !real_gt,">","<" ;
		];	  
            l
        | Some l -> l
    in
    {
      info_symbols = l;
      info_ops_of_rel = !ops_of_rels;
      info_syn = get_syntax_map task;
      info_rem = get_remove_set task;
    }

(* Gappa printing *)

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
(*
    | Tconst (ConstInt s) -> s
    | Tconst (ConstReal r) -> sprintf "%a" Pretty.print_const r
*)
    | Tconst c -> 
	fprintf str_formatter "%a" Pretty.print_const c;
	flush_str_formatter ()
    | _ -> raise Not_found

(* terms *)

(*
let int_theory = Env.find_theory env ["int"] "Int"

let plus_symbol = Theory.ns_find_ls int_theory.Theory.th_export ["infix +"]
*)

let rec print_term info fmt t = 
  let term = print_term info in
  match t.t_node with
  | Tbvar _ -> 
      assert false
  | Tconst c ->
      Pretty.print_const fmt c
  | Tvar { vs_name = id } 
  | Tapp ( { ls_name = id } ,[] ) ->
      print_ident fmt id
  | Tapp (ls, tl) -> 
      begin match query_syntax info.info_syn ls.ls_name with
	| Some s -> syntax_arguments s term fmt tl
	| None -> 
	    unsupportedTerm t 
              ("gappa: function '" ^ ls.ls_name.id_string ^ "' is not supported")
      end
  | Tlet _ -> unsupportedTerm t
      "gappa: you must eliminate let in term"
  | Tif _ -> unsupportedTerm t 
      "gappa: you must eliminate if_then_else"
  | Tcase _ -> unsupportedTerm t 
      "gappa: you must eliminate match"
  | Teps _ -> unsupportedTerm t 
      "gappa : you must eliminate epsilon"


(* predicates *)

let rec print_fmla info fmt f = 
  let term = print_term info in
  let fmla = print_fmla info in
  match f.f_node with
  | Fapp ({ ls_name = id }, []) ->
      print_ident fmt id
  | Fapp (ls, [t1;t2]) when ls_equal ls ps_equ -> 
      begin try
        let c1 = constant_value t1 in
        fprintf fmt "%a in [%s,%s]" term t2 c1 c1          
      with Not_found ->
        try
          let c2 = constant_value t2 in
          fprintf fmt "%a in [%s,%s]" term t1 c2 c2          
        with Not_found ->
          fprintf fmt "%a - %a in [0,0]" term t1 term t2           
      end
  | Fapp (ls, [t1;t2]) when Mls.mem ls info.info_ops_of_rel -> 
      let op,rev_op = try Mls.find ls info.info_ops_of_rel
	with Not_found -> assert false
      in
      begin try
        let c1 = constant_value t1 in
        fprintf fmt "%a %s %s" term t2 rev_op c1
      with Not_found ->
        try
          let c2 = constant_value t2 in
          fprintf fmt "%a %s %s" term t1 op c2
        with Not_found ->
          fprintf fmt "%a - %a %s 0" term t1 term t2 op
      end
  | Fapp (ls, tl) -> 
      begin match query_syntax info.info_syn ls.ls_name with
	| Some s -> syntax_arguments s term fmt tl
	| None -> 
	    unsupportedFmla f 
              ("gappa: predicate '" ^ ls.ls_name.id_string ^ "' is not supported")
      end
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
      fprintf fmt "(%a /\\@ %a)" fmla f1 fmla f2
  | Fbinop (For, f1, f2) ->
      fprintf fmt "(%a \\/@ %a)" fmla f1 fmla f2
  | Fbinop (Fimplies, f1, f2) ->
      fprintf fmt "(%a ->@ %a)" fmla f1 fmla f2
  | Fbinop (Fiff, _f1, _f2) ->
      unsupportedFmla f 
        "gappa: connector <-> is not supported"     
  | Fnot f ->
      fprintf fmt "not %a" fmla f
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
  
(*
let print_decl (* ?old *) info fmt d = 
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
  | Dprop (Paxiom, pr, f) -> 
      fprintf fmt "# hypothesis '%a'@\n" print_ident pr.pr_name;
      fprintf fmt "@[<hv 2>%a ->@]@\n" (print_fmla info) f     
  | Dprop (Pgoal, pr, f) ->
      fprintf fmt "# goal '%a'@\n" print_ident pr.pr_name;
(*
      fprintf fmt "@[<hv 2>{ %a@ }@]@\n" (print_fmla info) f
*)
      fprintf fmt "@[<hv 2>%a@]@\n" (print_fmla info) f
  | Dprop ((Plemma|Pskip), _, _) ->
      unsupportedDecl d 
        "gappa: lemmas are not supported"
*)

(*
let print_decl ?old:_ info fmt = 
  catch_unsupportedDecl (print_decl (* ?old *) info fmt)

let print_decls ?old info fmt dl =
  fprintf fmt "@[<hov>{ %a }@\n@]" (print_list nothing (print_decl ?old info)) dl
*)

let filter_hyp eqs hyps pr f =
  match f.f_node with
    | Fapp(ls,[t1;t2]) when ls == ps_equ -> 
	begin match t1.t_node with
	  | Tapp(_,[]) ->
	      ((pr,t1,t2)::eqs,hyps)
	  | _ ->
	      match t2.t_node with
		| Tapp(_,[]) ->
		    ((pr,t2,t1)::eqs,hyps)
		| _ -> (eqs, (pr,f)::hyps)
	end
	  (* todo: support more kinds of hypotheses *)
    | _ -> (eqs,hyps)

let filter_goal pr f =
  match f.f_node with
    | Fapp(_,[]) -> None 
	(* todo: filter more goals *)
    | _ -> Some(pr,f)
  
let prepare ((eqs,hyps,goal) as acc) d =
  match d.d_node with
    | Dtype _ -> acc
    | Dlogic _ -> acc
    | Dind _ -> 
	unsupportedDecl d 
	  "please remove inductive definitions before calling gappa printer"
    | Dprop (Paxiom, pr, f) -> 
	let (eqs,hyps) = filter_hyp eqs hyps pr f in (eqs,hyps,goal)
    | Dprop (Pgoal, pr, f) ->
	begin
	  match goal with
	    | None -> (eqs,hyps,filter_goal pr f)
	    | Some _ -> assert false
	end
    | Dprop ((Plemma|Pskip), _, _) ->
	unsupportedDecl d 
          "gappa: lemmas are not supported"

let print_equation info fmt (pr,t1,t2) =
  fprintf fmt "# equation '%a'@\n" print_ident pr.pr_name;
  fprintf fmt "%a = %a ;@\n" (print_term info) t1 (print_term info) t2
 
let print_hyp info fmt (pr,f) =
  fprintf fmt "# hypothesis '%a'@\n" print_ident pr.pr_name;
  fprintf fmt "%a ->@\n" (print_fmla info) f
  
let print_goal info fmt g =
  match g with
    | Some(pr,f) ->
	fprintf fmt "# goal '%a'@\n" print_ident pr.pr_name;
	fprintf fmt "%a@\n" (print_fmla info) f
    | None -> 
	fprintf fmt "# (unsupported kind of goal)@\n";
	fprintf fmt "1 in [0,0]@\n"
  
let print_task env pr thpr ?old:_ fmt task =
  forget_all ident_printer;
  let info = get_info env task in
  let task = 
    Abstraction.abstraction 
      (fun f -> Sls.mem f info.info_symbols)
      task 
  in
  print_prelude fmt pr;
  print_th_prelude task fmt thpr;  
  let equations,hyps,goal = 
    List.fold_left prepare ([],[],None) (Task.task_decls task) 
  in
  List.iter (print_equation info fmt) equations;
  fprintf fmt "@[<hov>{ %a %a }@\n@]" (print_list nothing (print_hyp info)) hyps
    (print_goal info) goal
(*  
  print_decls ?old info fmt (Task.task_decls task)
*)

let () = register_printer "gappa" print_task


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
