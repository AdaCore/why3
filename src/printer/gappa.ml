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

open Register
open Format
open Pp
open Ident
open Ty
open Term
open Decl
open Task


(* Gappa terms and formulas *)

(* fields of the float model *)
type float_field = Rounded | Exact | Model
(* formats of the float model *)
type float_fmt = Int | Single | Double | Binary80
(* modes of the float model *)
type mode = RndNE | RndZR | RndUP | RndDN | RndNA

type gterm =
  | Gvar of string
  | Gfld of float_field * string
  | Grnd of float_fmt * mode * gterm
  | Gcst of string
  | Gsqrt of gterm
  | Gneg of gterm
  | Gadd of gterm * gterm
  | Gsub of gterm * gterm
  | Gmul of gterm * gterm
  | Gdiv of gterm * gterm
  | Gabs of gterm

type gpred =
  | Gle of gterm * string
  | Gge of gterm * string
  | Gin of gterm * string * string
  | Grel of gterm * gterm * string
  | Gimplies of gpred * gpred
  | Gand of gpred * gpred
  | Gor of gpred * gpred
  | Gnot of gpred

type gobligation = (string * gterm) list * gpred



(* contains the roundings used *)
let rnd_table = Hashtbl.create 10



let get_format = function
  | Single -> "ieee_32"
  | Double -> "ieee_64"
  | Binary80 -> "x86_80"
  | Int -> "int"

let get_mode = function
  | RndNE -> "ne"
  | RndZR -> "zr"
  | RndUP -> "up"
  | RndDN -> "dn"
  | RndNA -> "na"

let rec print_term fmt = function
  | Gvar x -> fprintf fmt "%s" x
  | Gfld (Rounded, x) -> fprintf fmt "float_%s" x
  | Gfld (Exact,   x) -> fprintf fmt "exact_%s" x
  | Gfld (Model,   x) -> fprintf fmt "model_%s" x
  | Grnd (f, m, t) -> 
      fprintf fmt "rnd_%s%s(%a)" (get_format f) (get_mode m) print_term t
  | Gcst c -> fprintf fmt "%s" c
  | Gneg t -> fprintf fmt "(-%a)" print_term t
  | Gadd (t1, t2) -> fprintf fmt "(%a + %a)" print_term t1 print_term t2
  | Gsub (t1, t2) -> fprintf fmt "(%a - %a)" print_term t1 print_term t2
  | Gmul (t1, t2) -> fprintf fmt "(%a * %a)" print_term t1 print_term t2
  | Gdiv (t1, t2) -> fprintf fmt "(%a / %a)" print_term t1 print_term t2
  | Gabs t -> fprintf fmt "|%a|" print_term t
  | Gsqrt t -> fprintf fmt "sqrt(%a)" print_term t

let rec print_pred_atom fmt = function
  | Gle (t, r1) ->
      fprintf fmt "%a <= %s" print_term t r1
  | Gge (t, r1) ->
      fprintf fmt "%a >= %s" print_term t r1
  | Gin (t, r1, r2) ->
      fprintf fmt "%a in [%s, %s]" print_term t r1 r2
  | Grel (t1, t2, r1) ->
      fprintf fmt "|%a -/ %a| <= %s" print_term t1 print_term t2 r1
  | Gnot p ->
      fprintf fmt "not %a" print_pred_atom p
  | _ as p ->
      fprintf fmt "(%a)" print_pred p
and print_pred_left fmt = function
  | Gand (p1, p2) ->
      fprintf fmt "@[%a /\\@ %a@]" print_pred_atom p1 print_pred_atom p2
  | Gor (p1, p2) ->
      fprintf fmt "@[%a \\/@ %a@]" print_pred_atom p1 print_pred_atom p2
  | _ as p ->
      print_pred_atom fmt p
and print_pred fmt = function
  | Gimplies (p1, p2) ->
      fprintf fmt "@[%a ->@ %a@]" print_pred_left p1 print_pred p2
  | _ as p ->
      print_pred_left fmt p

let print_equation fmt (e, x, t) =
  let e =
    match e with
    | Rounded -> "float_"
    | Exact -> "exact_"
    | Model -> "model_" in
  fprintf fmt "@[%s%s = %a;@]" e x print_term t

let print_obligation fmt (eq,p) =
  Hashtbl.iter 
    (fun (f, m) () ->
       let m = get_mode m in
       match f with 
         | Int ->
             fprintf fmt "@@rnd_int%s = int<%s>;@\n" m m 
         | _ ->
             let f = get_format f in
             fprintf fmt "@@rnd_%s%s = float<%s, %s>;@\n" f m f m) 
    rnd_table;
  fprintf fmt "@\n%a@\n@\n" (print_list newline print_equation) eq;
  fprintf fmt "{ @[%a@] }@." print_pred p

(*
let print_file fmt = Queue.iter (print_obligation fmt) queue

let output_one_file ~allowedit file =
  if allowedit then
    begin
      let sep = "### DO NOT EDIT ABOVE THIS LINE" in
      do_not_edit_above ~file
	~before:print_file
	~sep
	~after:(fun _fmt -> ())
    end
  else
      print_in_file print_file file

let output_file fwe =
  let sep = "### DO NOT EDIT ABOVE THIS LINE" in
  let i = ref 0 in
  Queue.iter
    (fun o ->
       incr i;
       if debug then eprintf "gappa obligation %d@." !i;
       let file = fwe ^ "_why_po_" ^ string_of_int !i ^ ".gappa" in
       do_not_edit_above ~file
	 ~before:(fun fmt -> print_obligation fmt o)
	 ~sep
	 ~after:(fun _fmt -> ()))
    queue
*)



(* compilation to Gappa formulas *)

exception NotGappa

(* TODO: comment faire une table de hash indexée par des termes ? *)
(* 

module Termtbl = Hashtbl.Make(HashedTerm)

(* contains all the terms that have been generalized away,
   because they were not recognized *)
let gen_table = Termtbl.create 10

(* contains the terms associated to variables, especially gen_float variables *)
let var_table = Hashtbl.create 10

(* contains the names already defined,
   so new definitions should be as equalities *)
let def_table = Hashtbl.create 10

(* contains the reverted list of aliases from def_table *)
let def_list = ref []

(* contains the list of format-implied bounds on float variables *)
let bnd_list = ref []








let rec term = function
  | t when is_constant t ->
      Gcst (eval_constant t)
  | Tconst _ ->
      raise NotGappa
  | Tvar id ->
      Gvar (Ident.string id)
  | Tderef id ->
      Gvar (Ident.string id)
  (* int and real ops *)
  | Tapp (id, [t], _) when id == t_neg_real || id = t_neg_int ->
      Gneg (term t)
  | Tapp (id, [t], _) when id == t_abs_real || id == t_abs_int ->
      Gabs (term t)
  | Tapp (id, [t], _) when id == t_sqrt_real ->
      Gsqrt (term t)
  | Tapp (id, [t1; t2], _) when id == t_add_real || id = t_add_int ->
      Gadd (term t1, term t2)
  | Tapp (id, [t1; t2], _) when id == t_sub_real || id = t_sub_int ->
      Gsub (term t1, term t2)
  | Tapp (id, [t1; t2], _) when id == t_mul_real || id = t_mul_int ->
      Gmul (term t1, term t2)
  | Tapp (id, [t1; t2], _) when id == t_div_real ->
      Gdiv (term t1, term t2)
  (* conversion int -> real *)
  | Tapp (id, [t], _) when id == real_of_int ->
      term t
  (* conversion real -> int by truncate, i.e. towards zero *)
  | Tapp (id, [t], _) when id == truncate_real_to_int ->
      let mode = RndZR in
      Hashtbl.replace rnd_table (Int, mode) ();
      Grnd (Int, mode, term t)

  (* [Jessie] rounding *)
  | Tapp (id, [Tapp (m, [], _); t], _)
      when id == round_single ->
      let mode = mode_of_id m in
      Hashtbl.replace rnd_table (Single, mode) ();
      Grnd (Single, mode, term t)
  | Tapp (id, [Tapp (m, [], _); t], _)
      when id == round_double ->
      let mode = mode_of_id m in
      Hashtbl.replace rnd_table (Double, mode) ();
      Grnd (Double, mode, term t)

  | Tapp (id1, [Tapp (id2, l1, l2)], _)
      when id1 == single_value && id2 == round_single_logic ->
      term (Tapp (round_single, l1, l2))
  | Tapp (id1, [Tapp (id2, l1, l2)], _)
      when id1 == double_value && id2 == round_double_logic ->
      term (Tapp (round_double, l1, l2))

  (* casts *)
  | Tapp (id1, [Tapp (id2,[Tapp (m, [], _); t] , l2)], _)  
      when id1 == single_value && id2 == double_to_single ->
      let mode = mode_of_id m in
      Hashtbl.replace rnd_table (Single, mode) ();
      Grnd (Single, mode, term (Tapp (double_value,[t],l2)))

  | Tapp (id1, [Tapp (id2,[Tapp (_m, [], _); t] , l2)], _)  
      when id1 == double_value && id2 == single_to_double ->
        term (Tapp (single_value,[t],l2))


  | Tapp (id, [t], _)
      when (id == single_value || id == double_value || id == single_exact 
         || id == double_exact || id == single_model || id == double_model) ->
      let v = create_var t in
      let f = field_of_id id in
      let add_def fmt =
        if not (Hashtbl.mem def_table (f, v)) then begin
          Hashtbl.add def_table (f, v) ();
          Hashtbl.replace rnd_table (fmt, RndNE) ();
          def_list := (f, v, Grnd (fmt, RndNE, Gvar ("dummy_float_" ^ v))) :: !def_list;
          let b =
            if fmt = Single then "0x1.FFFFFEp127" else
            if fmt = Double then "0x1.FFFFFFFFFFFFFp1023" else
            assert false in
          bnd_list := Gin (Gfld (f, v), "-"^b, b) :: !bnd_list
        end in
      if id == single_value then add_def Single else
      if id == double_value then add_def Double;
      Gfld (f, v)

  | Tapp (id, [t], _) 
    when id == single_round_error || id == double_round_error ->
    let v = create_var t in
    Gabs (Gsub (Gfld (Rounded, v), Gfld (Exact, v)))

  | Tnamed(_,t) -> term t

  (* anything else is generalized as a fresh variable *)
  | Tapp _ as t ->
      Gvar (create_var t)

let termo t = try Some (term (subst_var t)) with NotGappa -> None







let ident_printer = 
  let bls = [
    "ac"; "and"; "array"; "as"; "axiom"; "bool"; "else"; "exists";
    "false"; "forall"; "function"; "goal"; "if"; "int"; "bitv";
    "logic"; "not"; "or"; "parameter"; "predicate";
    "prop"; "real"; "then"; "true"; "type"; "unit"; "void";
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

let rec print_type drv fmt ty = match ty.ty_node with
  | Tyvar id -> 
      print_tvsymbols fmt id
  | Tyapp (ts, tl) -> begin match Driver.query_syntax drv ts.ts_name with
      | Some s -> Driver.syntax_arguments s (print_type drv) fmt tl
      | None -> fprintf fmt "%a%a" (print_tyapp drv) tl print_ident ts.ts_name
    end

and print_tyapp drv fmt = function
  | [] -> ()
  | [ty] -> fprintf fmt "%a " (print_type drv) ty
  | tl -> fprintf fmt "(%a) " (print_list comma (print_type drv)) tl

let rec print_term drv fmt t = match t.t_node with
  | Tbvar _ -> 
      assert false
  | Tconst c ->
      Pretty.print_const fmt c
  | Tvar { vs_name = id } ->
      print_ident fmt id
  | Tapp (ls, tl) -> begin match Driver.query_syntax drv ls.ls_name with
      | Some s -> Driver.syntax_arguments s (print_term drv) fmt tl
      | None -> fprintf fmt "%a%a" print_ident ls.ls_name (print_tapp drv) tl
    end
  | Tlet _ -> unsupportedTerm t
      "alt-ergo : you must eliminate let in term"
  | Tif _ -> unsupportedTerm t 
      "alt-ergo : you must eliminate if_then_else"
  | Tcase _ -> unsupportedTerm t 
      "alt-ergo : you must eliminate match"
  | Teps _ -> unsupportedTerm t 
      "alt-ergo : you must eliminate epsilon"

and print_tapp drv fmt = function
  | [] -> ()
  | tl -> fprintf fmt "(%a)" (print_list comma (print_term drv)) tl

let rec print_fmla drv fmt f = match f.f_node with
  | Fapp ({ ls_name = id }, []) ->
      print_ident fmt id
  | Fapp (ls, tl) -> begin match Driver.query_syntax drv ls.ls_name with
      | Some s -> Driver.syntax_arguments s (print_term drv) fmt tl
      | None -> fprintf fmt "%a(%a)" print_ident ls.ls_name 
                    (print_list comma (print_term drv)) tl
    end
  | Fquant (q, fq) ->
      let q = match q with Fforall -> "forall" | Fexists -> "exists" in
      let vl, tl, f = f_open_quant fq in
      let forall fmt v = 
	fprintf fmt "%s %a:%a" q print_ident v.vs_name (print_type drv) v.vs_ty
      in
      fprintf fmt "@[(%a%a.@ %a)@]" (print_list dot forall) vl
        (print_triggers drv) tl (print_fmla drv) f;
      List.iter forget_var vl
  | Fbinop (Fand, f1, f2) ->
      fprintf fmt "(%a and@ %a)" (print_fmla drv) f1 (print_fmla drv) f2
  | Fbinop (For, f1, f2) ->
      fprintf fmt "(%a or@ %a)" (print_fmla drv) f1 (print_fmla drv) f2
  | Fbinop (Fimplies, f1, f2) ->
      fprintf fmt "(%a ->@ %a)" (print_fmla drv) f1 (print_fmla drv) f2
  | Fbinop (Fiff, f1, f2) ->
      fprintf fmt "(%a <->@ %a)" (print_fmla drv) f1 (print_fmla drv) f2
  | Fnot f ->
      fprintf fmt "(not %a)" (print_fmla drv) f
  | Ftrue ->
      fprintf fmt "true"
  | Ffalse ->
      fprintf fmt "false"
  | Fif (f1, f2, f3) ->
      fprintf fmt "((%a and %a) or (not %a and %a))"
	(print_fmla drv) f1 (print_fmla drv) f2 (print_fmla drv)
        f1 (print_fmla drv) f3
  | Flet _ -> unsupportedFmla f
      "alt-ergo : you must eliminate let in formula"
  | Fcase _ -> unsupportedFmla f 
      "alt-ergo : you must eliminate match"
  

and print_expr drv fmt = e_apply (print_term drv fmt) (print_fmla drv fmt)

and print_triggers drv fmt tl =
  let filter = function 
    | Term _ | Fmla {f_node = Fapp _} -> true
    | _ -> false in
  let tl = List.map (List.filter filter)
    tl in
  let tl = List.filter (function [] -> false | _::_ -> true) tl in
  if tl = [] then () else fprintf fmt "@ [%a]"
    (print_list alt (print_list comma (print_expr drv))) tl

let print_logic_binder drv fmt v =
  fprintf fmt "%a: %a" print_ident v.vs_name (print_type drv) v.vs_ty

let print_type_decl fmt ts = match ts.ts_args with
  | [] -> fprintf fmt "type %a" print_ident ts.ts_name
  | tl -> fprintf fmt "type (%a) %a" 
      (print_list comma print_tvsymbols) tl print_ident ts.ts_name

let print_type_decl drv fmt = function
  | ts, Tabstract when Driver.query_remove drv ts.ts_name -> false
  | ts, Tabstract -> print_type_decl fmt ts; true
  | _, Talgebraic _ -> unsupported 
      "alt-ergo : algebraic datatype are not supported"

let ac_th = ["algebra";"AC"]

let print_logic_decl drv fmt (ls,ld) =
  let tags = Driver.query_tags drv ls.ls_name in
  match ld with
    | None ->
        let sac = if Util.Sstr.mem "AC" tags then "ac " else "" in
        fprintf fmt "@[<hov 2>logic %s%a : %a%s%a@]@\n"
          sac print_ident ls.ls_name
          (print_list comma (print_type drv)) ls.ls_args 
          (if ls.ls_args = [] then "" else " -> ")
          (print_option_or_default "prop" (print_type drv)) ls.ls_value
    | Some ld ->
        let vl,e = open_ls_defn ld in
        begin match e with
          | Term t ->
              (* TODO AC? *)
              fprintf fmt "@[<hov 2>function %a(%a) : %a =@ %a@]@\n" 
                print_ident ls.ls_name
                (print_list comma (print_logic_binder drv)) vl 
                (print_type drv) (Util.of_option ls.ls_value) 
                (print_term drv) t
          | Fmla f ->
              fprintf fmt "@[<hov 2>predicate %a(%a) =@ %a@]"
                print_ident ls.ls_name 
                (print_list comma (print_logic_binder drv)) vl 
                (print_fmla drv) f
        end;
        List.iter forget_var vl

let print_logic_decl drv fmt d =
  if Driver.query_remove drv (fst d).ls_name then
    false else (print_logic_decl drv fmt d; true)

let print_decl drv fmt d = match d.d_node with
  | Dtype dl ->
      print_list_opt newline (print_type_decl drv) fmt dl
  | Dlogic dl ->
      print_list_opt newline (print_logic_decl drv) fmt dl
  | Dind _ -> unsupportedDecl d 
      "alt-ergo : inductive definition are not supported"
  | Dprop (Paxiom, pr, _) when Driver.query_remove drv pr.pr_name -> false
  | Dprop (Paxiom, pr, f) ->
      fprintf fmt "@[<hov 2>axiom %a :@ %a@]@\n" 
        print_ident pr.pr_name (print_fmla drv) f; true
  | Dprop (Pgoal, pr, f) ->
      fprintf fmt "@[<hov 2>goal %a :@ %a@]@\n"
        print_ident pr.pr_name (print_fmla drv) f; true
  | Dprop (Plemma, _, _) ->
      assert false

let print_decl drv fmt = catch_unsupportedDecl (print_decl drv fmt)

*)

let print_task drv fmt task = 
  Driver.print_full_prelude drv task fmt;
  let _decls = Task.task_decls task in
  assert false (* TODO *)
(*
  ignore (print_list_opt (add_flush newline2) (print_decl drv) fmt decls)
*)

let () = register_printer "gappa" 
  (fun drv fmt task -> 
(*
     forget_all ident_printer;
*)
     print_task drv fmt task)


let print_goal drv fmt (_id, _f, task) =  
  print_task drv fmt task;
(*
  fprintf fmt "@\n@[<hov 2>goal %a : %a@]@\n" print_ident id (print_fmla drv) f
*)



(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
