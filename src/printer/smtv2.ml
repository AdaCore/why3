(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2015   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** SMT v2 printer with some extensions *)

open Format
open Pp
open Ident
open Ty
open Term
open Decl
open Printer

let debug = Debug.register_info_flag "smtv2_printer"
  ~desc:"Print@ debugging@ messages@ about@ printing@ \
         the@ input@ of@ smtv2."

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
      "bvugt"; "bvuge"; "bvslt"; "bvsle"; "bvsgt"; "bvsge"; "rotate_left";
      "rotate_right";

      "cos"; "sin"; "tan"; "atan"; "pi";

      (** Other stuff that Why3 seems to need *)
      "DECIMAL"; "NUMERAL"; "par"; "STRING";
      "unsat";"sat";
      "Bool"; "true"; "false";
      "Array";"const";
      "abs";
      "BitVec"; "extract"; "bv2nat"; "nat2bv";

      (** From Z3 *)
      "map"; "bv"; "subset"; "union"
      ]
  in
  let san = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer bls ~sanitizer:san

let print_ident fmt id =
  fprintf fmt "%s" (id_unique ident_printer id)

type info = {
  info_syn        : syntax_map;
  info_converters : converter_map;
  mutable info_model : term list;
}

let debug_print_term message t =
  let form = Debug.get_debug_formatter () in
  begin
    Debug.dprintf debug message;
    if Debug.test_flag debug then 
      Pretty.print_term form t;
    Debug.dprintf debug "@.";
  end

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

let model_label = Ident.create_label "model"

let collect_model_ls info ls =
  if ls.ls_args = [] && Slab.mem model_label ls.ls_name.id_label then
    let t = t_app ls [] ls.ls_value in
    info.info_model <-
      (t_label ?loc:ls.ls_name.id_loc ls.ls_name.id_label t) :: info.info_model

(** expr *)
let rec print_term info fmt t = 
  debug_print_term "Printing term: " t; 

  if Slab.mem model_label t.t_label then
    info.info_model <- (t) :: info.info_model;

  match t.t_node with
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
  | Tcase({t_node = Tvar v}, bl) ->
      print_branches info v print_term fmt bl
  | Tcase(t, bl) ->
      let subject = create_vsymbol (id_fresh "subject") (t_type t) in
      fprintf fmt "@[(let ((%a @[%a@]))@ %a)@]"
        print_var subject (print_term info) t
        (print_branches info subject print_term) bl;
      forget_var subject
  | Teps _ -> unsupportedTerm t
      "smtv2: you must eliminate epsilon"
  | Tquant _ | Tbinop _ | Tnot _ | Ttrue | Tfalse -> raise (TermExpected t)

and print_fmla info fmt f = 
  debug_print_term "Printing formula: " f;  
  if Slab.mem model_label f.t_label then
    info.info_model <- (f) :: info.info_model;
  
  match f.t_node with
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
  | Tcase({t_node = Tvar v}, bl) ->
      print_branches info v print_fmla fmt bl
  | Tcase(t, bl) ->
      let subject = create_vsymbol (id_fresh "subject") (t_type t) in
      fprintf fmt "@[(let ((%a @[%a@]))@ %a)@]"
        print_var subject (print_term info) t
        (print_branches info subject print_fmla) bl;
      forget_var subject
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)

and print_branches info subject pr fmt bl = match bl with
  | [] -> assert false
  | br::bl ->
      let (p,t) = t_open_branch br in
      let error () = unsupportedPattern p
        "smtv2: you must compile nested pattern matching" in
      match p.pat_node with
      | Pwild -> pr info fmt t
      | Papp (cs,args) ->
          let args = List.map (function
            | {pat_node = Pvar v} -> v | _ -> error ()) args in
          if bl = [] then print_branch info subject pr fmt (cs,args,t)
          else fprintf fmt "@[(ite (is-%a %a) %a %a)@]"
            print_ident cs.ls_name print_var subject
            (print_branch info subject pr) (cs,args,t)
            (print_branches info subject pr) bl
      | _ -> error ()

and print_branch info subject pr fmt (cs,vars,t) =
  if vars = [] then pr info fmt t else
  let tvs = t_freevars Mvs.empty t in
  if List.for_all (fun v -> not (Mvs.mem v tvs)) vars then pr info fmt t else
  let i = ref 0 in
  let pr_proj fmt v = incr i;
    if Mvs.mem v tvs then fprintf fmt "(%a (%a_proj_%d %a))"
      print_var v print_ident cs.ls_name !i print_var subject in
  fprintf fmt "@[(let (%a) %a)@]" (print_list space pr_proj) vars (pr info) t

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
  if Mid.mem ls.ls_name info.info_syn then () else begin
    collect_model_ls info ls;
    let vsl,expr = Decl.open_ls_defn def in
    fprintf fmt "@[<hov 2>(define-fun %a (%a) %a %a)@]@\n@\n"
      print_ident ls.ls_name
      (print_var_list info) vsl
      (print_type_value info) ls.ls_value
      (print_expr info) expr;
    List.iter forget_var vsl
  end

let print_info_model cntexample fmt info =
  (* Prints the content of info.info_model *)
  let info_model = info.info_model in
  if info_model != [] && cntexample then 
    begin
	  (*
            fprintf fmt "@[(get-value (%a))@]@\n"
            (Pp.print_list Pp.space (print_fmla info_copy)) model_list;*)
      fprintf fmt "@[(get-value (";
      List.iter (fun f -> 
	fprintf str_formatter "%a" (print_fmla info) f;
        let s = flush_str_formatter () in
        fprintf fmt "%s " s;
      ) info_model;
      fprintf fmt "))@]@\n";

      (* Printing model has modification of info.info_model as undesirable
	 side-effect. Revert it back. *)
      info.info_model <- info_model
    end

let print_prop_decl cntexample args info fmt k pr f = match k with
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
      fprintf fmt "@[(check-sat)@]@\n";
      print_info_model cntexample fmt info;
      
      args.printer_mapping <- { lsymbol_m = args.printer_mapping.lsymbol_m;
				queried_terms = info.info_model; }
	  
  | Plemma| Pskip -> assert false


let print_constructor_decl info fmt (ls,args) =
  match args with
  | [] -> fprintf fmt "(%a)" print_ident ls.ls_name
  | _ ->
     fprintf fmt "@[(%a@ " print_ident ls.ls_name;
     let _ =
       List.fold_left2
         (fun i ty pr ->
          begin match pr with
                | Some pr -> fprintf fmt "(%a" print_ident pr.ls_name
                | None -> fprintf fmt "(%a_proj_%d" print_ident ls.ls_name i
          end;
          fprintf fmt " %a)" (print_type info) ty;
          succ i) 1 ls.ls_args args
     in
     fprintf fmt ")@]"

let print_data_decl info fmt (ts,cl) =
  fprintf fmt "@[(%a@ %a)@]"
    print_ident ts.ts_name
    (print_list space (print_constructor_decl info)) cl

let print_decl cntexample args info fmt d = match d.d_node with
  | Dtype ts ->
      print_type_decl info fmt ts
  | Ddata dl ->
    (*unsupportedDecl d
      "smtv2 : algebraic type are not supported" *)
    fprintf fmt "@[(declare-datatypes ()@ (%a))@]@\n"
      (print_list space (print_data_decl info)) dl
  | Dparam ls ->
      collect_model_ls info ls;
      print_param_decl info fmt ls
  | Dlogic dl ->
      print_list nothing (print_logic_decl info) fmt dl
  | Dind _ -> unsupportedDecl d
      "smtv2 : inductive definition are not supported"
  | Dprop (k,pr,f) ->
      if Mid.mem pr.pr_name info.info_syn then () else
      print_prop_decl cntexample args info fmt k pr f

let print_decls cntexample args =
  let print_decl (sm, cm, model) fmt d =
    try let info = {info_syn = sm; info_converters = cm; info_model = model} in
        print_decl cntexample args info fmt d; (sm, cm, info.info_model), []
    with Unsupported s -> raise (UnsupportedDecl (d,s)) in
  let print_decl = Printer.sprint_decl print_decl in
  let print_decl task acc = print_decl task.Task.task_decl acc in
  Discriminate.on_syntax_map (fun sm ->
  Printer.on_converter_map (fun cm ->
      Trans.fold print_decl ((sm, cm, []),[])))

let set_produce_models fmt cntexample = 
  if cntexample then
    fprintf fmt "(set-option :produce-models true)@\n"
  
let print_task args ?old:_ fmt task =
  (* In trans-based p-printing [forget_all] is a no-no *)
  (* forget_all ident_printer; *)

  let cntexample = Prepare_for_counterexmp.get_counterexmp task in

  print_prelude fmt args.prelude;
  set_produce_models fmt cntexample;
  print_th_prelude task fmt args.th_prelude;
  let rec print = function
    | x :: r -> print r; Pp.string fmt x
    | [] -> () in
  print (snd (Trans.apply (print_decls cntexample args) task));
  pp_print_flush fmt ()

let () = register_printer "smtv2" print_task
  ~desc:"Printer@ for@ the@ SMTlib@ version@ 2@ format."
