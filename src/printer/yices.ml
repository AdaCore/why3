(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** SMT v1 printer with some extensions *)

open Format
open Pp
open Ident
open Ty
open Term
open Decl
open Theory
open Printer

let ident_printer =
  let bls = (*["and";" benchmark";" distinct";"exists";"false";"flet";"forall";
     "if then else";"iff";"implies";"ite";"let";"logic";"not";"or";
     "sat";"theory";"true";"unknown";"unsat";"xor";
     "assumption";"axioms";"defintion";"extensions";"formula";
     "funs";"extrafuns";"extrasorts";"extrapreds";"language";
     "notes";"preds";"sorts";"status";"theory";"Int";"Real";"Bool";
     "Array";"U";"select";"store"]*)
    (** smtlib2 V2 p71 *)
    [(** General: *)
      "!";"_"; "as"; "DECIMAL"; "exists"; "forall"; "let"; "NUMERAL";
      "par"; "STRING"; "if"; "ite";
       (**Command names:*)
      "define";
      "define-type";"exit";"get-assertions";"get-assignment"; "get-info";
      "get-option"; "get-proof"; "get-unsat-core"; "get-value"; "pop"; "push";
      "set-logic"; "set-info"; "set-option";
       (** for security *)
      "bool";"unsat";"sat";"true";"false";
      "true";"check";"assert";"TYPE";"SUBTYPE";
      "scalar";"select";"update";"int";"real";"subtype";"subrange";"mk-bv";
      "bv-concat";"bv-extract";"bv-shift-right0";"div";"mod";"bitvector";
      "lambda";
]
  in
  let san = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer bls ~sanitizer:san

let print_ident fmt id =
  fprintf fmt "%s" (id_unique ident_printer id)

(** type *)
type info = {
  info_syn : syntax_map;
  complex_type : ty Hty.t;
}

let rec print_type info fmt ty = match ty.ty_node with
  | Tyvar _ -> unsupported "yices: you must encode polymorphism"
  | Tyapp (ts, []) -> begin match query_syntax info.info_syn ts.ts_name with
      | Some s -> syntax_arguments s (print_type info) fmt []
      | None -> fprintf fmt "%a" print_ident ts.ts_name
  end
  | Tyapp (ts, l) ->
     begin match query_syntax info.info_syn ts.ts_name with
      | Some s -> syntax_arguments s (print_type info) fmt l
      | None -> print_type info fmt (Hty.find info.complex_type ty)
     end

(* and print_tyapp info fmt = function *)
(*   | [] -> () *)
(*   | [ty] -> fprintf fmt "%a " (print_type info) ty *)
(*   | tl -> fprintf fmt "(%a) " (print_list comma (print_type info)) tl *)

let rec iter_complex_type info fmt () ty = match ty.ty_node with
  | Tyvar _ -> unsupported "yices: you must encode polymorphism"
  | Tyapp (_, []) -> ()
  | Tyapp (ts, l) ->
    begin match query_syntax info.info_syn ts.ts_name with
      | Some _ -> List.iter (iter_complex_type info fmt ()) l
      | None when not (Hty.mem info.complex_type ty) ->
        let id = id_fresh (Pp.string_of_wnl Pretty.print_ty ty) in
        let ts = create_tysymbol id [] None in
        let cty = ty_app ts [] in
        fprintf fmt "(define-type %a)@."
          print_ident ts.ts_name;
        Hty.add info.complex_type ty cty
      | None -> ()
    end

let find_complex_type info fmt f =
  t_ty_fold (iter_complex_type info fmt) () f

let find_complex_type_expr info fmt f =
  TermTF.t_selecti
    (t_ty_fold (iter_complex_type info fmt))
    (t_ty_fold (iter_complex_type info fmt))
    () f

let print_type info fmt =
  catch_unsupportedType (print_type info fmt)

let print_type_value info fmt = function
  | None -> fprintf fmt "bool"
  | Some ty -> print_type info fmt ty

(** var *)
let forget_var v = forget_id ident_printer v.vs_name

let print_var fmt {vs_name = id} =
  let n = id_unique ident_printer id in
  fprintf fmt "%s" n

let print_typed_var info fmt vs =
  fprintf fmt "%a::%a" print_var vs
    (print_type info) vs.vs_ty

let print_var_list info fmt vsl =
  print_list space (print_typed_var info) fmt vsl

(** expr *)
let rec print_term info fmt t = match t.t_node with
  | Tconst c ->
      let number_format = {
          Print_number.long_int_support = true;
          Print_number.dec_int_support = Print_number.Number_default;
          Print_number.hex_int_support = Print_number.Number_unsupported;
          Print_number.oct_int_support = Print_number.Number_unsupported;
          Print_number.bin_int_support = Print_number.Number_unsupported;
          Print_number.def_int_support = Print_number.Number_unsupported;
          Print_number.dec_real_support = Print_number.Number_unsupported;
          Print_number.hex_real_support = Print_number.Number_unsupported;
          Print_number.frac_real_support = Print_number.Number_custom
            (Print_number.PrintFracReal ("%s", "(* %s %s)", "(/ %s %s)"));
          Print_number.def_real_support = Print_number.Number_unsupported;
        } in
      Print_number.print number_format fmt c
  | Tvar v -> print_var fmt v
  | Tapp (ls, tl) -> begin match query_syntax info.info_syn ls.ls_name with
      | Some s -> syntax_arguments_typed s (print_term info)
        (print_type info) t fmt tl
      | None -> begin match tl with
          | [] -> fprintf fmt "%a" print_ident ls.ls_name
          | _ -> fprintf fmt "@,(%a %a)"
              print_ident ls.ls_name (print_list space (print_term info)) tl
        end end
  | Tlet (t1, tb) ->
      let v, t2 = t_open_bound tb in
      fprintf fmt "@[(let ((%a %a)) %a)@]" print_var v
        (print_term info) t1 (print_term info) t2;
      forget_var v
  | Tif (f1,t1,t2) ->
      fprintf fmt "@[(if %a@ %a@ %a)@]"
        (print_fmla info) f1 (print_term info) t1 (print_term info) t2
  | Tcase _ -> unsupportedTerm t
      "yices: you must eliminate match"
  | Teps _ -> unsupportedTerm t
      "yices: you must eliminate epsilon"
  | Tquant _ | Tbinop _ | Tnot _ | Ttrue | Tfalse -> raise (TermExpected t)

and print_fmla info fmt f = match f.t_node with
  | Tapp ({ ls_name = id }, []) ->
      print_ident fmt id
  | Tapp (ls, tl) -> begin match query_syntax info.info_syn ls.ls_name with
      | Some s -> syntax_arguments_typed s (print_term info)
        (print_type info) f fmt tl
      | None -> begin match tl with
          | [] -> fprintf fmt "%a" print_ident ls.ls_name
          | _ -> fprintf fmt "(%a %a)"
              print_ident ls.ls_name (print_list space (print_term info)) tl
        end end
  | Tquant (q, fq) ->
      let q = match q with Tforall -> "forall" | Texists -> "exists" in
      let vl, tl, f = t_open_quant fq in
      (* TODO trigger dépend des capacités du prover : 2 printers?
      smtwithtriggers/smtstrict *)
      if true (*tl = []*) then
        fprintf fmt "@[(%s@ (%a)@ %a)@]"
          q
          (print_var_list info) vl
          (print_fmla info) f
      else
        fprintf fmt "@[(%s@ (%a)%a@ %a)@]"
          q
          (print_var_list info) vl
          (print_triggers info) tl
          (print_fmla info) f;
      List.iter forget_var vl
  | Tbinop (Tand, f1, f2) ->
      fprintf fmt "@[(and %a@ %a)@]" (print_fmla info) f1 (print_fmla info) f2
  | Tbinop (Tor, f1, f2) ->
      fprintf fmt "@[(or %a@ %a)@]" (print_fmla info) f1 (print_fmla info) f2
  | Tbinop (Timplies, f1, f2) ->
      fprintf fmt "@[(=> %a@ %a)@]"
        (print_fmla info) f1 (print_fmla info) f2
  | Tbinop (Tiff, f1, f2) ->
      fprintf fmt "@[(and (=> %a@ %a) (=> %a@ %a))@]"
         (print_fmla info) f1 (print_fmla info) f2
         (print_fmla info) f2 (print_fmla info) f1
  | Tnot f ->
      fprintf fmt "@[(not@ %a)@]" (print_fmla info) f
  | Ttrue ->
      fprintf fmt "true"
  | Tfalse ->
      fprintf fmt "false"
  | Tif (f1, f2, f3) ->
      fprintf fmt "@[(if %a@ %a@ %a)@]"
        (print_fmla info) f1 (print_fmla info) f2 (print_fmla info) f3
  | Tlet (t1, tb) ->
      let v, f2 = t_open_bound tb in
      fprintf fmt "@[(let ((%a %a)) %a)@]" print_var v
        (print_term info) t1 (print_fmla info) f2;
      forget_var v
  | Tcase _ -> unsupportedTerm f
      "yices: you must eliminate match"
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)

and print_expr info fmt =
  TermTF.t_select (print_term info fmt) (print_fmla info fmt)

(** I don't know how to print trigger for yices *)
and print_triggers info fmt = function
  | [] -> ()
  | a::l -> fprintf fmt "PATTERN (%a):@ %a"
    (print_list space (print_expr info)) a
    (print_triggers info) l

let print_logic_binder info fmt v =
  fprintf fmt "%a: %a" print_ident v.vs_name
    (print_type info) v.vs_ty

let print_type_decl info fmt ts =
  if Mid.mem ts.ts_name info.info_syn then false else
  if ts.ts_args = [] then
  (fprintf fmt "(define-type %a)" print_ident ts.ts_name; true)
  else false

let print_data_decl _info fmt = function
  | ts, csl (* monomorphic enumeration *)
    when ts.ts_args = [] && List.for_all (fun (_,l) -> l = []) csl ->
      let print_cs fmt (ls,_) = print_ident fmt ls.ls_name in
      fprintf fmt "@[<hov 2>(define-type %a@ (scalar %a))@]@\n@\n"
        print_ident ts.ts_name (print_list space print_cs) csl
  | _, _ ->
      unsupported "yices: algebraic types are not supported"

let print_data_decl info fmt (ts, _ as d) =
  if Mid.mem ts.ts_name info.info_syn then false
  else begin print_data_decl info fmt d; true end

let print_param_decl info fmt ls =
  List.iter (iter_complex_type info fmt ()) ls.ls_args;
  Util.option_iter (iter_complex_type info fmt ()) ls.ls_value;
  match ls.ls_args with
  | [] ->
    fprintf fmt "@[<hov 2>(define %a::%a)@]@\n"
      print_ident ls.ls_name
      (print_type_value info) ls.ls_value
  | _ ->
    fprintf fmt "@[<hov 2>(define %a::(-> %a %a))@]@\n"
      print_ident ls.ls_name
      (print_list space (print_type info)) ls.ls_args
      (print_type_value info) ls.ls_value

let print_param_decl info fmt ls =
  if Mid.mem ls.ls_name info.info_syn then
    false else (print_param_decl info fmt ls; true)

let print_decl info fmt d = match d.d_node with
  | Dtype ts ->
      print_type_decl info fmt ts
  | Ddata dl ->
      print_list_opt nothing (print_data_decl info) fmt dl
  | Dparam ls ->
      print_param_decl info fmt ls
  | Dlogic _ -> unsupportedDecl d
      "yices: function and predicate definitions are not supported"
  | Dind _ -> unsupportedDecl d
      "yices: inductive definitions are not supported"
  | Dprop (Paxiom, pr, _) when Mid.mem pr.pr_name info.info_syn -> false
  | Dprop (Paxiom, pr, f) ->
    find_complex_type info fmt f;
      fprintf fmt "@[<hov 2>;; %s@\n(assert@ %a);@]@\n"
        pr.pr_name.id_string
        (print_fmla info) f; true
  | Dprop (Pgoal, pr, f) ->
    find_complex_type info fmt f;
      fprintf fmt "@[(assert@\n";
      fprintf fmt "@[;; %a@]@\n" print_ident pr.pr_name;
      (match pr.pr_name.id_loc with
        | None -> ()
        | Some loc -> fprintf fmt " @[;; %a@]@\n"
            Loc.gen_report_position loc);
      fprintf fmt "  @[(not %a)@])@]@\n(check)" (print_fmla info) f;
      true
  | Dprop ((Plemma|Pskip), _, _) -> assert false

let print_decl info fmt = catch_unsupportedDecl (print_decl info fmt)

let distingued =
  let dist_syntax mls = function
    | [MAls ls;MAstr s] -> Mls.add ls s mls
    | _ -> assert false in
  let dist_dist syntax mls = function
    | [MAls ls;MAls lsdis] ->
      begin try
              Mid.add lsdis.ls_name (Mls.find ls syntax) mls
        with Not_found -> mls end
    | _ -> assert false in
  Trans.on_meta meta_syntax_logic (fun syntax ->
    let syntax = List.fold_left dist_syntax Mls.empty syntax in
    Trans.on_meta Discriminate.meta_lsinst (fun dis ->
      let dis2 = List.fold_left (dist_dist syntax) Mid.empty dis in
      Trans.return dis2))

let print_task pr thpr _blacklist fmt task =
  print_prelude fmt pr;
  print_th_prelude task fmt thpr;
  let info = {
    info_syn = Mid.union (fun _ _ s -> Some s)
      (get_syntax_map task) (Trans.apply distingued task);
    complex_type = Hty.create 5;
  }
  in
  let decls = Task.task_decls task in
  ignore (print_list_opt (add_flush newline2) (print_decl info) fmt decls)

let () = register_printer "yices"
  (fun _env pr thpr blacklist ?old:_ fmt task ->
     forget_all ident_printer;
     print_task pr thpr blacklist fmt task)
  ~desc:"Printer@ for@ the@ Yices@ theorem@ prover version 1."
