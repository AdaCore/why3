(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
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
open Printer

let ident_printer =
  let bls = (*["and";" benchmark";" distinct";"exists";"false";"flet";"forall";
     "if then else";"iff";"implies";"ite";"let";"logic";"not";"or";
     "sat";"theory";"true";"unknown";"unsat";"xor";
     "assumption";"axioms";"definition";"extensions";"formula";
     "funs";"extrafuns";"extrasorts";"extrapreds";"language";
     "notes";"preds";"sorts";"status";"theory";"Int";"Real";"Bool";
     "Array";"U";"select";"store"]*)
    (* smtlib2 V2 p71 *)
    [(* General: *)
      "!";"_"; "as"; "DECIMAL"; "exists"; "forall"; "let"; "NUMERAL";
      "par"; "STRING";
       (* Command names: *)
      "assert";"check-sat"; "declare-sort";"declare-fun";"define-sort";
      "define-fun";"exit";"get-assertions";"get-assignment"; "get-info";
      "get-option"; "get-proof"; "get-unsat-core"; "get-value"; "pop"; "push";
      "set-logic"; "set-info"; "set-option";
       (* for security *)
      "BOOLEAN";"unsat";"sat";"TRUE";"FALSE";
      "TRUE";"CHECK";"QUERY";"ASSERT";"TYPE";"SUBTYPE"]
  in
  let san = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer bls ~sanitizer:san

let print_ident fmt id =
  fprintf fmt "%s" (id_unique ident_printer id)

type info = {
  info_syn     : syntax_map;
  complex_type : ty Mty.t ref;
  urg_output   : string list ref;
}

(** type *)
let complex_type = Wty.memoize 3 (fun ty ->
  let s = Pp.string_of_wnl Pretty.print_ty ty in
  create_tysymbol (id_fresh s) [] NoDef)

let rec print_type info fmt ty = match ty.ty_node with
  | Tyvar _ -> unsupported "cvc3: you must encode the polymorphism"
  | Tyapp (ts, l) ->
      begin match query_syntax info.info_syn ts.ts_name, l with
      | Some s, _ -> syntax_arguments s (print_type info) fmt l
      | None, [] -> fprintf fmt "%a" print_ident ts.ts_name
      | None, _ ->
          begin match Mty.find_opt ty !(info.complex_type) with
          | Some ty -> print_type info fmt ty
          | None ->
              let ts = complex_type ty in let cty = ty_app ts [] in
              let us = Pp.sprintf "%a: TYPE;@\n@\n" print_ident ts.ts_name in
              info.complex_type := Mty.add ty cty !(info.complex_type);
              info.urg_output := us :: !(info.urg_output);
              print_type info fmt cty
          end
      end

let print_type info fmt ty = try print_type info fmt ty
  with Unsupported s -> raise (UnsupportedType (ty,s))

let print_type_value info fmt = function
  | None -> fprintf fmt "BOOLEAN"
  | Some ty -> print_type info fmt ty

(** var *)
let forget_var v = forget_id ident_printer v.vs_name

let print_var fmt {vs_name = id} =
  let n = id_unique ident_printer id in
  fprintf fmt "%s" n

let print_typed_var info fmt vs =
  fprintf fmt "%a : %a" print_var vs
    (print_type info) vs.vs_ty

let print_var_list info fmt vsl =
  print_list comma (print_typed_var info) fmt vsl

(** expr *)
let rec print_term info fmt t = match t.t_node with
  | Tconst c ->
      let number_format = {
          Number.long_int_support = true;
          Number.extra_leading_zeros_support = true;
          Number.negative_int_support = Number.Number_default;
          Number.dec_int_support = Number.Number_default;
          Number.hex_int_support = Number.Number_unsupported;
          Number.oct_int_support = Number.Number_unsupported;
          Number.bin_int_support = Number.Number_unsupported;
          Number.def_int_support = Number.Number_unsupported;
          Number.negative_real_support = Number.Number_default;
          Number.dec_real_support = Number.Number_unsupported;
          Number.hex_real_support = Number.Number_unsupported;
          Number.frac_real_support = Number.Number_custom
            (Number.PrintFracReal ("%s", "(%s * %s)", "(%s / %s)"));
          Number.def_real_support = Number.Number_unsupported;
        } in
      Number.print number_format fmt c
  | Tvar v -> print_var fmt v
  | Tapp (ls, tl) -> begin match query_syntax info.info_syn ls.ls_name with
      | Some s -> syntax_arguments_typed s (print_term info)
        (print_type info) t fmt tl
      | None -> begin match tl with (* for cvc3 wich doesn't accept (toto ) *)
          | [] -> fprintf fmt "%a" print_ident ls.ls_name
          | _ -> fprintf fmt "@,%a(%a)"
              print_ident ls.ls_name (print_list comma (print_term info)) tl
        end end
  | Tlet (t1, tb) ->
      let v, t2 = t_open_bound tb in
      fprintf fmt "@[(LET %a =@ %a IN@ %a)@]" print_var v
        (print_term info) t1 (print_term info) t2;
      forget_var v
  | Tif (f1,t1,t2) ->
      fprintf fmt "@[(IF %a@ THEN %a@ ELSE %a ENDIF)@]"
        (print_fmla info) f1 (print_term info) t1 (print_term info) t2
  | Tcase _ -> unsupportedTerm t
      "cvc3: you must eliminate match"
  | Teps _ -> unsupportedTerm t
      "cvc3: you must eliminate epsilon"
  | Tquant _ | Tbinop _ | Tnot _ | Ttrue | Tfalse -> raise (TermExpected t)

and print_fmla info fmt f = match f.t_node with
  | Tapp ({ ls_name = id }, []) ->
      print_ident fmt id
  | Tapp (ls, tl) -> begin match query_syntax info.info_syn ls.ls_name with
      | Some s -> syntax_arguments_typed s (print_term info)
        (print_type info) f fmt tl
      | None -> begin match tl with
          | [] -> fprintf fmt "%a" print_ident ls.ls_name
          | _ -> fprintf fmt "(%a(%a))"
              print_ident ls.ls_name (print_list comma (print_term info)) tl
        end end
  | Tquant (q, fq) ->
      let q = match q with Tforall -> "FORALL" | Texists -> "EXISTS" in
      let vl, tl, f = t_open_quant fq in
      (* TODO trigger dépend des capacités du prover : 2 printers?
      smtwithtriggers/smtstrict *)
      if tl = [] then
        fprintf fmt "@[(%s@ (%a):@ %a)@]"
          q
          (print_var_list info) vl
          (print_fmla info) f
      else
        fprintf fmt "@[(%s@ (%a):%a@ %a)@]"
          q
          (print_var_list info) vl
          (print_triggers info) tl
          (print_fmla info) f;
      List.iter forget_var vl
  | Tbinop (Tand, f1, f2) ->
      fprintf fmt "@[(%a@ AND %a)@]" (print_fmla info) f1 (print_fmla info) f2
  | Tbinop (Tor, f1, f2) ->
      fprintf fmt "@[(%a@ OR %a)@]" (print_fmla info) f1 (print_fmla info) f2
  | Tbinop (Timplies, f1, f2) ->
      fprintf fmt "@[(%a@ => %a)@]"
        (print_fmla info) f1 (print_fmla info) f2
  | Tbinop (Tiff, f1, f2) ->
      fprintf fmt "@[(%a@ <=> %a)@]" (print_fmla info) f1 (print_fmla info) f2
  | Tnot f ->
      fprintf fmt "@[(NOT@ %a)@]" (print_fmla info) f
  | Ttrue ->
      fprintf fmt "TRUE"
  | Tfalse ->
      fprintf fmt "FALSE"
  | Tif (f1, f2, f3) ->
      fprintf fmt "@[(IF %a@ THEN %a@ ELSE %a ENDIF)@]"
        (print_fmla info) f1 (print_fmla info) f2 (print_fmla info) f3
  | Tlet (t1, tb) ->
      let v, f2 = t_open_bound tb in
      fprintf fmt "@[(LET %a =@ %a IN@ %a)@]" print_var v
        (print_term info) t1 (print_fmla info) f2;
      forget_var v
  | Tcase _ -> unsupportedTerm f
      "cvc3: you must eliminate match"
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)

and print_expr info fmt =
  TermTF.t_select (print_term info fmt) (print_fmla info fmt)

and print_triggers info fmt = function
  | [] -> ()
  | a::l -> fprintf fmt "PATTERN (%a):@ %a"
    (print_list comma (print_expr info)) a
    (print_triggers info) l

let print_type_decl info fmt ts =
  if ts.ts_args = [] && not (is_alias_type_def ts.ts_def) then
  if not (Mid.mem ts.ts_name info.info_syn) then
  fprintf fmt "%a : TYPE;@\n@\n" print_ident ts.ts_name

let print_lsargs info fmt = function
  | [] -> ()
  | l  -> fprintf fmt "(%a) -> " (print_list comma (print_type info)) l

let print_param_decl info fmt ls =
  fprintf fmt "@[<hov 2>%a: %a%a;@]@\n@\n"
    print_ident ls.ls_name
    (print_lsargs info) ls.ls_args
    (print_type_value info) ls.ls_value

let print_param_decl info fmt ls =
  if not (Mid.mem ls.ls_name info.info_syn)
  then print_param_decl info fmt ls

let print_logic_decl info fmt (ls,def) =
  let vsl,expr = Decl.open_ls_defn def in
  fprintf fmt "@[<hov 2>%a: %a%a = LAMBDA (%a): %a;@]@\n@\n"
    print_ident ls.ls_name
    (print_lsargs info) ls.ls_args
    (print_type_value info) ls.ls_value
    (print_var_list info) vsl
    (print_expr info) expr;
  List.iter forget_var vsl

let print_logic_decl info fmt d =
  if not (Mid.mem (fst d).ls_name info.info_syn)
  then print_logic_decl info fmt d

let print_decl info fmt d = match d.d_node with
  | Dtype ts ->
      print_type_decl info fmt ts
  | Ddata _ -> unsupportedDecl d
      "cvc3: algebraic type are not supported"
  | Dparam ls ->
      print_param_decl info fmt ls
  | Dlogic dl ->
      print_list nothing (print_logic_decl info) fmt dl
  | Dind _ -> unsupportedDecl d
      "cvc3: inductive definition are not supported"
  | Dprop (Paxiom, pr, _) when Mid.mem pr.pr_name info.info_syn -> ()
  | Dprop (Paxiom, pr, f) ->
      fprintf fmt "@[<hov 2>%% %s@\nASSERT@ %a;@]@\n@\n"
        pr.pr_name.id_string (print_fmla info) f
  | Dprop (Pgoal, pr, f) ->
      fprintf fmt "@[QUERY@\n";
      fprintf fmt "@[%% %a@]@\n" print_ident pr.pr_name;
      (match pr.pr_name.id_loc with
        | Some loc -> fprintf fmt " @[%% %a@]@\n" Loc.gen_report_position loc
        | None -> ());
      fprintf fmt "  @[%a;@]@]@\n" (print_fmla info) f
  | Dprop (Plemma, _, _) -> assert false

let print_decls =
  let print_decl (sm,ct) fmt d =
    let info = {info_syn = sm; complex_type = ref ct; urg_output = ref []} in
    try print_decl info fmt d; (sm, !(info.complex_type)), !(info.urg_output)
    with Unsupported s -> raise (UnsupportedDecl (d,s)) in
  let print_decl = Printer.sprint_decl print_decl in
  let print_decl task acc = print_decl task.Task.task_decl acc in
  Discriminate.on_syntax_map (fun sm ->
    Trans.fold print_decl ((sm,Mty.empty),[]))

let print_task args ?old:_ fmt task =
  (* In trans-based p-printing [forget_all] is a no-no *)
  (* forget_all ident_printer; *)
  print_prelude fmt args.prelude;
  print_th_prelude task fmt args.th_prelude;
  let rec print = function
    | x :: r -> print r; Pp.string fmt x
    | [] -> () in
  print (snd (Trans.apply print_decls task));
  pp_print_flush fmt ()

let () = register_printer "cvc3" print_task
  ~desc:"Printer@ for@ the@ CVC3@ theorem@ prover."
