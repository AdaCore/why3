(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
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

(** SMTLIB tokens taken from CVC4: src/parser/smt2/Smt2.g *)
let ident_printer =
  let bls = (*["and";" benchmark";" distinct";"exists";"false";"flet";"forall";
     "if then else";"iff";"implies";"ite";"let";"logic";"not";"or";
     "sat";"theory";"true";"unknown";"unsat";"xor";
     "assumption";"axioms";"defintion";"extensions";"formula";
     "funs";"extrafuns";"extrasorts";"extrapreds";"language";
     "notes";"preds";"sorts";"status";"theory";"Int";"Real";"Bool";
     "Array";"U";"select";"store"]*)
    (** smtlib2 V2 p71 *)
    [(** Base SMT-LIB tokens *)
      "assert"; "check-sat"; "declare-fun"; "declare-sort"; "define-fun";
      "define-sort"; "get-value"; "get-assignment"; "get-assertions";
      "get-proof"; "get-unsat-core"; "exit"; "ite"; "let"; "!"; "_";
      "set-logic"; "set-info"; "get-info"; "set-option"; "get-option";
      "push"; "pop"; "as";

      (** extended commands *)
      "declare-datatypes"; "get-model"; "echo"; "assert-rewrite";
      "assert-reduction"; "assert-propagation"; "declare-sorts";
      "declare-funs"; "declare-preds"; "define"; "declare-const";
      "simplify";

      (** attributes *)

      (** operators, including theory symbols *)
      "and"; "distinct"; "exists"; "forall"; "is_int"; "not"; "or"; "select";
      "store"; "to_int"; "to_real"; "xor";

      "div"; "mod";

      "concat"; "bvnot"; "bvand"; "bvor"; "bvneg"; "bvadd"; "bvmul"; "bvudiv";
      "bvurem"; "bvshl"; "bvlshr"; "bvult"; "bvnand"; "bvnor"; "bvxor";
      "bvcomp"; "bvsub"; "bvsdiv"; "bvsrem"; "bvsmod"; "bvashr"; "bvule";
      "bvugt"; "bvuge"; "bvslt"; "bvsle"; "bvsgt"; "bvsge"; "rotate_left"; "rotate_right";

      "cos"; "sin"; "tan"; "atan"; "pi";

      (** Other stuff that Why3 seems to need *)
      "DECIMAL"; "NUMERAL"; "par"; "STRING";
      "unsat";"sat";
      "Bool"; "true"; "false";
      "Array";"const";
      "abs";
      "BitVec"; "extract"; "bv2nat"; "nat2bv";

      (** From Z3 *)
      "map"
      ]
  in
  let san = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer bls ~sanitizer:san

let print_ident fmt id =
  fprintf fmt "%s" (id_unique ident_printer id)

type info = {
  info_syn        : syntax_map;
  info_converters : converter_map;
}

(** type *)
let rec print_type info fmt ty = match ty.ty_node with
  | Tyvar _ -> unsupported "smt : you must encode the polymorphism"
  | Tyapp (ts, l) ->
     begin match query_syntax info.info_syn ts.ts_name, l with
      | Some s, _ -> syntax_arguments s (print_type info) fmt l
      | None, [] -> fprintf fmt "%a" print_ident ts.ts_name
      | None, _ -> fprintf fmt "(%a %a)" print_ident ts.ts_name
          (print_list space (print_type info)) l
     end

let print_type info fmt ty = try print_type info fmt ty
  with Unsupported s -> raise (UnsupportedType (ty,s))

let print_type_value info fmt = function
  | None -> fprintf fmt "Bool"
  | Some ty -> print_type info fmt ty

(** var *)
let forget_var v = forget_id ident_printer v.vs_name

let print_var fmt {vs_name = id} =
  let n = id_unique ident_printer id in
  fprintf fmt "%s" n

let print_typed_var info fmt vs =
  fprintf fmt "(%a %a)" print_var vs
    (print_type info) vs.vs_ty

let print_var_list info fmt vsl =
  print_list space (print_typed_var info) fmt vsl

(** expr *)
let rec print_term info fmt t = match t.t_node with
  | Tconst c ->
      let number_format = {
          Number.long_int_support = true;
          Number.extra_leading_zeros_support = false;
          Number.dec_int_support = Number.Number_default;
          Number.hex_int_support = Number.Number_unsupported;
          Number.oct_int_support = Number.Number_unsupported;
          Number.bin_int_support = Number.Number_unsupported;
          Number.def_int_support = Number.Number_unsupported;
          Number.dec_real_support = Number.Number_unsupported;
          Number.hex_real_support = Number.Number_unsupported;
          Number.frac_real_support = Number.Number_custom
            (Number.PrintFracReal ("%s.0", "(* %s.0 %s.0)", "(/ %s.0 %s.0)"));
          Number.def_real_support = Number.Number_unsupported;
        } in
      Number.print number_format fmt c
  | Tvar v -> print_var fmt v
  | Tapp (ls, tl) ->
    (* let's check if a converter applies *)
    begin try
      match tl with
      | [ { t_node = Tconst _} ] ->
        begin match query_converter info.info_converters ls with
        | None -> raise Exit
        | Some s -> syntax_arguments s (print_term info) fmt tl
        end
      | _ -> raise Exit
    with Exit ->
    (* non converter applies, then ... *)
    match query_syntax info.info_syn ls.ls_name with
      | Some s -> syntax_arguments_typed s (print_term info)
        (print_type info) t fmt tl
      | None -> begin match tl with (* for cvc3 wich doesn't accept (toto ) *)
          | [] -> fprintf fmt "@[%a@]" print_ident ls.ls_name
          | _ -> fprintf fmt "@[(%a@ %a)@]"
              print_ident ls.ls_name (print_list space (print_term info)) tl
        end end
  | Tlet (t1, tb) ->
      let v, t2 = t_open_bound tb in
      fprintf fmt "@[(let ((%a %a))@ %a)@]" print_var v
        (print_term info) t1 (print_term info) t2;
      forget_var v
  | Tif (f1,t1,t2) ->
      fprintf fmt "@[(ite %a@ %a@ %a)@]"
        (print_fmla info) f1 (print_term info) t1 (print_term info) t2
  | Tcase _ -> unsupportedTerm t
      "smtv2 : you must eliminate match"
  | Teps _ -> unsupportedTerm t
      "smtv2 : you must eliminate epsilon"
  | Tquant _ | Tbinop _ | Tnot _ | Ttrue | Tfalse -> raise (TermExpected t)

and print_fmla info fmt f = match f.t_node with
  | Tapp ({ ls_name = id }, []) ->
      print_ident fmt id
  | Tapp (ls, tl) -> begin match query_syntax info.info_syn ls.ls_name with
      | Some s -> syntax_arguments_typed s (print_term info)
        (print_type info) f fmt tl
      | None -> begin match tl with (* for cvc3 wich doesn't accept (toto ) *)
          | [] -> fprintf fmt "%a" print_ident ls.ls_name
          | _ -> fprintf fmt "(%a@ %a)"
              print_ident ls.ls_name (print_list space (print_term info)) tl
        end end
  | Tquant (q, fq) ->
      let q = match q with Tforall -> "forall" | Texists -> "exists" in
      let vl, tl, f = t_open_quant fq in
      (* TODO trigger dépend des capacités du prover : 2 printers?
      smtwithtriggers/smtstrict *)
      if tl = [] then
        fprintf fmt "@[(%s@ (%a)@ %a)@]"
          q
          (print_var_list info) vl
          (print_fmla info) f
      else
        fprintf fmt "@[(%s@ (%a)@ (! %a %a))@]"
          q
          (print_var_list info) vl
          (print_fmla info) f
          (print_triggers info) tl;
      List.iter forget_var vl
  | Tbinop (Tand, f1, f2) ->
      fprintf fmt "@[(and@ %a@ %a)@]" (print_fmla info) f1 (print_fmla info) f2
  | Tbinop (Tor, f1, f2) ->
      fprintf fmt "@[(or@ %a@ %a)@]" (print_fmla info) f1 (print_fmla info) f2
  | Tbinop (Timplies, f1, f2) ->
      fprintf fmt "@[(=>@ %a@ %a)@]"
        (print_fmla info) f1 (print_fmla info) f2
  | Tbinop (Tiff, f1, f2) ->
      fprintf fmt "@[(=@ %a@ %a)@]" (print_fmla info) f1 (print_fmla info) f2
  | Tnot f ->
      fprintf fmt "@[(not@ %a)@]" (print_fmla info) f
  | Ttrue ->
      fprintf fmt "true"
  | Tfalse ->
      fprintf fmt "false"
  | Tif (f1, f2, f3) ->
      fprintf fmt "@[(ite %a@ %a@ %a)@]"
        (print_fmla info) f1 (print_fmla info) f2 (print_fmla info) f3
  | Tlet (t1, tb) ->
      let v, f2 = t_open_bound tb in
      fprintf fmt "@[(let ((%a %a))@ %a)@]" print_var v
        (print_term info) t1 (print_fmla info) f2;
      forget_var v
  | Tcase _ -> unsupportedTerm f
      "smtv2 : you must eliminate match"
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)

and print_expr info fmt =
  TermTF.t_select (print_term info fmt) (print_fmla info fmt)

and print_trigger info fmt e = fprintf fmt "%a" (print_expr info) e

and print_triggers info fmt = function
  | [] -> ()
  | a::l -> fprintf fmt ":pattern (%a) %a"
    (print_list space (print_trigger info)) a
    (print_triggers info) l

let print_type_decl info fmt ts =
  if ts.ts_def <> None then () else
  if Mid.mem ts.ts_name info.info_syn then () else
  fprintf fmt "(declare-sort %a %i)@\n@\n"
    print_ident ts.ts_name (List.length ts.ts_args)

let print_param_decl info fmt ls =
  if Mid.mem ls.ls_name info.info_syn then () else
  fprintf fmt "@[<hov 2>(declare-fun %a (%a) %a)@]@\n@\n"
    print_ident ls.ls_name
    (print_list space (print_type info)) ls.ls_args
    (print_type_value info) ls.ls_value

let print_logic_decl info fmt (ls,def) =
  if Mid.mem ls.ls_name info.info_syn then () else
  let vsl,expr = Decl.open_ls_defn def in
  fprintf fmt "@[<hov 2>(define-fun %a (%a) %a %a)@]@\n@\n"
    print_ident ls.ls_name
    (print_var_list info) vsl
    (print_type_value info) ls.ls_value
    (print_expr info) expr;
  List.iter forget_var vsl

let print_prop_decl info fmt k pr f = match k with
  | Paxiom ->
      fprintf fmt "@[<hov 2>;; %s@\n(assert@ %a)@]@\n@\n"
        pr.pr_name.id_string (* FIXME? collisions *)
        (print_fmla info) f
  | Pgoal ->
      fprintf fmt "@[(assert@\n";
      fprintf fmt "@[;; %a@]@\n" print_ident pr.pr_name;
      (match pr.pr_name.id_loc with
        | None -> ()
        | Some loc -> fprintf fmt " @[;; %a@]@\n"
            Loc.gen_report_position loc);
      fprintf fmt "  @[(not@ %a))@]@\n" (print_fmla info) f;
      fprintf fmt "@[(check-sat)@]@\n"
  | Plemma| Pskip -> assert false

let print_decl info fmt d = match d.d_node with
  | Dtype ts ->
      print_type_decl info fmt ts
  | Ddata _ -> unsupportedDecl d
      "smtv2 : algebraic type are not supported"
  | Dparam ls ->
      print_param_decl info fmt ls
  | Dlogic dl ->
      print_list nothing (print_logic_decl info) fmt dl
  | Dind _ -> unsupportedDecl d
      "smtv2 : inductive definition are not supported"
  | Dprop (k,pr,f) ->
      if Mid.mem pr.pr_name info.info_syn then () else
      print_prop_decl info fmt k pr f

let print_decls =
  let print_decl (sm, cm) fmt d =
    try print_decl {info_syn = sm; info_converters = cm} fmt d; (sm, cm), []
    with Unsupported s -> raise (UnsupportedDecl (d,s)) in
  let print_decl = Printer.sprint_decl print_decl in
  let print_decl task acc = print_decl task.Task.task_decl acc in
  Discriminate.on_syntax_map (fun sm ->
  Printer.on_converter_map (fun cm ->
      Trans.fold print_decl ((sm, cm),[])))

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

let () = register_printer "smtv2" print_task
  ~desc:"Printer@ for@ the@ SMTlib@ version@ 2@ format."
