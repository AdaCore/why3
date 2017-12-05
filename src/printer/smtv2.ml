(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
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
open Cntexmp_printer

let debug = Debug.register_info_flag "smtv2_printer"
  ~desc:"Print@ debugging@ messages@ about@ printing@ \
         the@ input@ of@ smtv2."

(** SMTLIB tokens taken from CVC4: src/parser/smt2/{Smt2.g,smt2.cpp} *)
let ident_printer () =
  let bls =
    [(* Base SMT-LIB commands, see page 43 *)
      "assert"; "check-sat"; "check-sat-assuming"; "declare-const";
      "declare-datatype"; "declare-datatypes"; "declare-fun"; "declare-sort";
      "define-fun"; "define-fun-rec"; "define-funs-rec"; "define-sort";
      "echo"; "exit";
      "get-assignment"; "get-assertions";
      "get-info"; "get-model"; "get-option"; "get-proof";
      "get-unsat-assumptions"; "get-unsat-core"; "get-value";
      "pop"; "push";
      "reset"; "reset-assertions";
      "set-info"; "set-logic";  "set-option";

     (* Base SMT-LIB tokens, see page 22*)
      "BINARY"; "DECIMAL"; "HEXADECIMAL"; "NUMERAL"; "STRING";
      "_"; "!"; "as"; "let"; "exists"; "forall"; "match"; "par";

     (* extended commands *)
      "assert-rewrite";
      "assert-reduction"; "assert-propagation"; "declare-sorts";
      "declare-funs"; "declare-preds"; "define";
      "simplify";

     (* operators, including theory symbols *)
      "ite";
      "and"; "distinct"; "is_int"; "not"; "or"; "select";
      "store"; "to_int"; "to_real"; "xor";

      "div"; "mod"; "rem";

      "concat"; "bvnot"; "bvand"; "bvor"; "bvneg"; "bvadd"; "bvmul"; "bvudiv";
      "bvurem"; "bvshl"; "bvlshr"; "bvult"; "bvnand"; "bvnor"; "bvxor";
      "bvcomp"; "bvsub"; "bvsdiv"; "bvsrem"; "bvsmod"; "bvashr"; "bvule";
      "bvugt"; "bvuge"; "bvslt"; "bvsle"; "bvsgt"; "bvsge"; "rotate_left";
      "rotate_right"; "bvredor"; "bvredand";

      "sin"; "cos"; "tan"; "asin"; "acos"; "atan"; "pi";

     (* the new floating point theory - updated to the 2014-05-27 standard *)
      "FloatingPoint"; "fp";
      "Float16"; "Float32"; "Float64"; "Float128";
      "RoundingMode";
      "roundNearestTiesToEven"; "RNE";
      "roundNearestTiesToAway"; "RNA";
      "roundTowardPositive";    "RTP";
      "roundTowardNegative";    "RTN";
      "roundTowardZero";        "RTZ";
      "NaN"; "+oo"; "-oo"; "+zero"; "-zero";
      "fp.abs"; "fp.neg"; "fp.add"; "fp.sub"; "fp.mul"; "fp.div";
      "fp.fma"; "fp.sqrt"; "fp.rem"; "fp.roundToIntegral"; "fp.min"; "fp.max";
      "fp.leq"; "fp.lt"; "fp.geq"; "fp.gt"; "fp.eq";
      "fp.isNormal"; "fp.isSubnormal"; "fp.isZero";
      "fp.isInfinite"; "fp.isNaN";
      "fp.isNegative"; "fp.isPositive";
      "to_fp"; "to_fp_unsigned";
      "fp.to_ubv"; "fp.to_sbv"; "fp.to_real";

     (* the new proposed string theory *)
      "String";
      "str.++"; "str.len"; "str.substr"; "str.contains"; "str.at";
      "str.indexof"; "str.prefixof"; "str.suffixof"; "int.to.str";
      "str.to.int"; "u16.to.str"; "str.to.u16"; "u32.to.str"; "str.to.u32";
      "str.in.re"; "str.to.re"; "re.++"; "re.union"; "re.inter";
      "re.*"; "re.+"; "re.opt"; "re.range"; "re.loop";

     (* the new proposed set theory *)
      "union"; "intersection"; "setminus"; "subset"; "member";
      "singleton"; "insert";

     (* built-in sorts *)
      "Bool"; "Int"; "Real"; "BitVec"; "Array";

     (* Other stuff that Why3 seems to need *)
      "unsat"; "sat";
      "true"; "false";
      "const";
      "abs";
      "BitVec"; "extract"; "bv2nat"; "nat2bv";

     (* From Z3 *)
      "map"; "bv"; "default";
      "difference";
      ]
  in
  let san = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer bls ~sanitizer:san

type info = {
  info_syn        : syntax_map;
  info_converters : converter_map;
  info_rliteral   : syntax_map;
  mutable info_model : S.t;
  mutable info_in_goal : bool;
  info_vc_term : vc_term_info;
  info_printer : ident_printer;
}

let debug_print_term message t =
  let form = Debug.get_debug_formatter () in
  begin
    Debug.dprintf debug message;
    if Debug.test_flag debug then
      Pretty.print_term form t;
    Debug.dprintf debug "@.";
  end

let print_ident info fmt id =
  fprintf fmt "%s" (id_unique info.info_printer id)

(** type *)
let rec print_type info fmt ty = match ty.ty_node with
  | Tyvar _ -> unsupported "smt : you must encode the polymorphism"
  | Tyapp (ts, l) ->
     begin match query_syntax info.info_syn ts.ts_name, l with
      | Some s, _ -> syntax_arguments s (print_type info) fmt l
      | None, [] -> fprintf fmt "%a" (print_ident info) ts.ts_name
      | None, _ -> fprintf fmt "(%a %a)" (print_ident info) ts.ts_name
          (print_list space (print_type info)) l
     end

let print_type info fmt ty = try print_type info fmt ty
  with Unsupported s -> raise (UnsupportedType (ty,s))

let print_type_value info fmt = function
  | None -> fprintf fmt "Bool"
  | Some ty -> print_type info fmt ty

(** var *)
let forget_var info v = forget_id info.info_printer v.vs_name

let print_var info fmt {vs_name = id} =
  let n = id_unique info.info_printer id in
  fprintf fmt "%s" n

let print_typed_var info fmt vs =
  fprintf fmt "(%a %a)" (print_var info) vs
    (print_type info) vs.vs_ty

let print_var_list info fmt vsl =
  print_list space (print_typed_var info) fmt vsl

let model_projected_label = Ident.create_label "model_projected"

let collect_model_ls info ls =
  if ls.ls_args = [] && (Slab.mem model_label ls.ls_name.id_label ||
  Slab.mem model_projected_label ls.ls_name.id_label) then
    let t = t_app ls [] ls.ls_value in
    info.info_model <-
      add_model_element
      (t_label ?loc:ls.ls_name.id_loc ls.ls_name.id_label t) info.info_model

let number_format = {
  Number.long_int_support = true;
  Number.extra_leading_zeros_support = false;
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
    (Number.PrintFracReal ("%s.0", "(* %s.0 %s.0)", "(/ %s.0 %s.0)"));
  Number.def_real_support = Number.Number_unsupported;
}

(** expr *)
let rec print_term info fmt t =
  debug_print_term "Printing term: " t;

  if Slab.mem model_label t.t_label then
    info.info_model <- add_model_element t info.info_model;

  check_enter_vc_term t info.info_in_goal info.info_vc_term;

  let () = match t.t_node with
  | Tconst c ->
      let ts = match t.t_ty with
        | Some { ty_node = Tyapp (ts, []) } -> ts
        | _ -> assert false (* impossible *) in
      (* look for syntax literal ts in driver *)
      begin match query_syntax info.info_rliteral ts.ts_name, c with
        | Some st, Number.ConstInt c ->
          syntax_range_literal st fmt c
        | Some st, Number.ConstReal c ->
          let fp = match ts.ts_def with
            | Float fp -> fp
            | _ -> assert false in
          syntax_float_literal st fp fmt c
        | None, _ -> Number.print number_format fmt c
        (* TODO/FIXME: we must assert here that the type is either
            ty_int or ty_real, otherwise it makes no sense to print
            the literal. Do we ensure that preserved literal types
            are exactly those that have a dedicated syntax? *)
      end
  | Tvar v -> print_var info fmt v
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
          | [] ->
	    let vc_term_info = info.info_vc_term in
	    if vc_term_info.vc_inside then begin
	      match vc_term_info.vc_loc with
	      | None -> ()
	      | Some loc ->
		let labels = match vc_term_info.vc_func_name with
		  | None ->
		    ls.ls_name.id_label
		  | Some _ ->
		    model_trace_for_postcondition ~labels:ls.ls_name.id_label info.info_vc_term in
		let _t_check_pos = t_label ~loc labels t in
		(* TODO: temporarily disable collecting variables inside the term triggering VC *)
		(*info.info_model <- add_model_element t_check_pos info.info_model;*)
		()
	    end;
	    fprintf fmt "@[%a@]" (print_ident info) ls.ls_name
          | _ ->
	    fprintf fmt "@[(%a@ %a)@]"
	      (print_ident info) ls.ls_name
              (print_list space (print_term info)) tl
        end end
  | Tlet (t1, tb) ->
      let v, t2 = t_open_bound tb in
      fprintf fmt "@[(let ((%a %a))@ %a)@]" (print_var info) v
        (print_term info) t1 (print_term info) t2;
      forget_var info v
  | Tif (f1,t1,t2) ->
      fprintf fmt "@[(ite %a@ %a@ %a)@]"
        (print_fmla info) f1 (print_term info) t1 (print_term info) t2
  | Tcase(t, bl) ->
    let ty = t_type t in
    begin
      match ty.ty_node with
      | Tyapp (ts,_) when ts_equal ts ts_bool ->
        print_boolean_branches info t print_term fmt bl
      | _ ->
        match t.t_node with
        | Tvar v -> print_branches info v print_term fmt bl
        | _ ->
          let subject = create_vsymbol (id_fresh "subject") (t_type t) in
          fprintf fmt "@[(let ((%a @[%a@]))@ %a)@]"
            (print_var info) subject (print_term info) t
            (print_branches info subject print_term) bl;
          forget_var info subject
    end
  | Teps _ -> unsupportedTerm t
      "smtv2: you must eliminate epsilon"
  | Tquant _ | Tbinop _ | Tnot _ | Ttrue | Tfalse -> raise (TermExpected t)
  in

  check_exit_vc_term t info.info_in_goal info.info_vc_term;


and print_fmla info fmt f =
  debug_print_term "Printing formula: " f;
  if Slab.mem model_label f.t_label then
    info.info_model <- add_model_element f info.info_model;

  check_enter_vc_term f info.info_in_goal info.info_vc_term;

  let () = match f.t_node with
  | Tapp ({ ls_name = id }, []) ->
      print_ident info fmt id
  | Tapp (ls, tl) -> begin match query_syntax info.info_syn ls.ls_name with
      | Some s -> syntax_arguments_typed s (print_term info)
        (print_type info) f fmt tl
      | None -> begin match tl with (* for cvc3 wich doesn't accept (toto ) *)
          | [] -> print_ident info fmt ls.ls_name
          | _ -> fprintf fmt "(%a@ %a)"
              (print_ident info) ls.ls_name
              (print_list space (print_term info)) tl
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
      List.iter (forget_var info) vl
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
      fprintf fmt "@[(let ((%a %a))@ %a)@]" (print_var info) v
        (print_term info) t1 (print_fmla info) f2;
      forget_var info v
  | Tcase(t, bl) ->
    let ty = t_type t in
    begin
      match ty.ty_node with
      | Tyapp (ts,_) when ts_equal ts ts_bool ->
        print_boolean_branches info t print_fmla fmt bl
      | _ ->
        match t.t_node with
        | Tvar v -> print_branches info v print_fmla fmt bl
        | _ ->
          let subject = create_vsymbol (id_fresh "subject") (t_type t) in
          fprintf fmt "@[(let ((%a @[%a@]))@ %a)@]"
            (print_var info) subject (print_term info) t
            (print_branches info subject print_fmla) bl;
          forget_var info subject
    end
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f) in

  check_exit_vc_term f info.info_in_goal info.info_vc_term

and print_boolean_branches info subject pr fmt bl =
  let error () = unsupportedTerm subject
    "smtv2: bad pattern-matching on Boolean (compile_match missing?)"
  in
  match bl with
  | [br1 ; br2] ->
    let (p1,t1) = t_open_branch br1 in
    let (_p2,t2) = t_open_branch br2 in
    begin
      match p1.pat_node with
      | Papp(cs,_) ->
        let csname = if ls_equal cs fs_bool_true then "true" else "false" in
        fprintf fmt "@[(ite (= %a %s) %a %a)@]"
          (print_term info) subject
          csname
          (pr info) t1
          (pr info) t2
      | _ -> error ()
    end
  | _ -> error ()

and print_branches info subject pr fmt bl = match bl with
  | [] -> assert false
  | br::bl ->
      let (p,t) = t_open_branch br in
      let error () = unsupportedPattern p
        "smtv2: you must compile nested pattern-matching" in
      match p.pat_node with
      | Pwild -> pr info fmt t
      | Papp (cs,args) ->
          let args = List.map (function
            | {pat_node = Pvar v} -> v | _ -> error ()) args in
          if bl = [] then print_branch info subject pr fmt (cs,args,t)
          else fprintf fmt "@[(ite (is-%a %a) %a %a)@]"
            (print_ident info) cs.ls_name (print_var info) subject
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
      (print_var info) v (print_ident info) cs.ls_name
      !i (print_var info) subject in
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
  if is_alias_type_def ts.ts_def then () else
  if Mid.mem ts.ts_name info.info_syn then () else
  fprintf fmt "(declare-sort %a %i)@\n@\n"
    (print_ident info) ts.ts_name (List.length ts.ts_args)

let print_param_decl info fmt ls =
  if Mid.mem ls.ls_name info.info_syn then () else
    match ls.ls_args with
    (* only in SMTLIB 2.5
    | [] -> fprintf fmt "@[<hov 2>(declare-const %a %a)@]@\n@\n"
              (print_ident info) ls.ls_name
              (print_type_value info) ls.ls_value
     *)
    | _  -> fprintf fmt "@[<hov 2>(declare-fun %a (%a) %a)@]@\n@\n"
                    (print_ident info) ls.ls_name
                    (print_list space (print_type info)) ls.ls_args
                    (print_type_value info) ls.ls_value

let print_logic_decl info fmt (ls,def) =
  if Mid.mem ls.ls_name info.info_syn then () else begin
    collect_model_ls info ls;
    let vsl,expr = Decl.open_ls_defn def in
    fprintf fmt "@[<hov 2>(define-fun %a (%a) %a %a)@]@\n@\n"
      (print_ident info) ls.ls_name
      (print_var_list info) vsl
      (print_type_value info) ls.ls_value
      (print_expr info) expr;
    List.iter (forget_var info) vsl
  end

let print_info_model cntexample fmt info =
  (* Prints the content of info.info_model *)
  let info_model = info.info_model in
  if not (S.is_empty info_model) && cntexample then
    begin
      fprintf fmt "@[(get-model ";
      let model_map =
	S.fold (fun f acc ->
          fprintf str_formatter "%a" (print_fmla info) f;
          let s = flush_str_formatter () in
	  Stdlib.Mstr.add s f acc)
	info_model
	Stdlib.Mstr.empty in
      fprintf fmt ")@]@\n";

      (* Printing model has modification of info.info_model as undesirable
	 side-effect. Revert it back. *)
      info.info_model <- info_model;
      model_map
    end
  else
    Stdlib.Mstr.empty

let print_prop_decl vc_loc cntexample args info fmt k pr f = match k with
  | Paxiom ->
      fprintf fmt "@[<hov 2>;; %s@\n(assert@ %a)@]@\n@\n"
        pr.pr_name.id_string (* FIXME? collisions *)
        (print_fmla info) f
  | Pgoal ->
      fprintf fmt "@[(assert@\n";
      fprintf fmt "@[;; %a@]@\n" (print_ident info) pr.pr_name;
      (match pr.pr_name.id_loc with
        | None -> ()
        | Some loc -> fprintf fmt " @[;; %a@]@\n"
            Loc.gen_report_position loc);
      info.info_in_goal <- true;
      fprintf fmt "  @[(not@ %a))@]@\n" (print_fmla info) f;
      info.info_in_goal <- false;
      (*if cntexample then fprintf fmt "@[(push)@]@\n"; (* z3 specific stuff *)*)
      fprintf fmt "@[(check-sat)@]@\n";
      let model_list = print_info_model cntexample fmt info in

      args.printer_mapping <- { lsymbol_m = args.printer_mapping.lsymbol_m;
				vc_term_loc = vc_loc;
				queried_terms = model_list; }
  | Plemma| Pskip -> assert false


let print_constructor_decl info fmt (ls,args) =
  match args with
  | [] -> fprintf fmt "(%a)" (print_ident info) ls.ls_name
  | _ ->
     fprintf fmt "@[(%a@ " (print_ident info) ls.ls_name;
     let _ =
       List.fold_left2
         (fun i ty pr ->
          begin match pr with
          | Some pr -> fprintf fmt "(%a" (print_ident info) pr.ls_name
          | None -> fprintf fmt "(%a_proj_%d" (print_ident info) ls.ls_name i
          end;
          fprintf fmt " %a)" (print_type info) ty;
          succ i) 1 ls.ls_args args
     in
     fprintf fmt ")@]"

let print_data_decl info fmt (ts,cl) =
  fprintf fmt "@[(%a@ %a)@]"
    (print_ident info) ts.ts_name
    (print_list space (print_constructor_decl info)) cl

let print_decl vc_loc cntexample args info fmt d =
  match d.d_node with
  | Dtype ts ->
      print_type_decl info fmt ts
  | Ddata [(ts,_)] when query_syntax info.info_syn ts.ts_name <> None -> ()
  | Ddata dl ->
      fprintf fmt "@[(declare-datatypes ()@ (%a))@]@\n"
        (print_list space (print_data_decl info)) dl
  | Dparam ls ->
      collect_model_ls info ls;
      print_param_decl info fmt ls
  | Dlogic dl ->
      print_list nothing (print_logic_decl info) fmt dl
  | Dind _ -> unsupportedDecl d
      "smtv2: inductive definitions are not supported"
  | Dprop (k,pr,f) ->
      if Mid.mem pr.pr_name info.info_syn then () else
      print_prop_decl vc_loc cntexample args info fmt k pr f

let set_produce_models fmt cntexample =
  if cntexample then
    fprintf fmt "(set-option :produce-models true)@\n"

let print_task args ?old:_ fmt task =
  let cntexample = Prepare_for_counterexmp.get_counterexmp task in
  let vc_loc = Intro_vc_vars_counterexmp.get_location_of_vc task in
  let vc_info = {vc_inside = false; vc_loc = None; vc_func_name = None} in
  let info = {
    info_syn = Discriminate.get_syntax_map task;
    info_converters = Printer.get_converter_map task;
    info_rliteral = Printer.get_rliteral_map task;
    info_model = S.empty;
    info_in_goal = false;
    info_vc_term = vc_info;
    info_printer = ident_printer () } in
  print_prelude fmt args.prelude;
  set_produce_models fmt cntexample;
  print_th_prelude task fmt args.th_prelude;
  let rec print_decls = function
    | Some t ->
        print_decls t.Task.task_prev;
        begin match t.Task.task_decl.Theory.td_node with
        | Theory.Decl d ->
            begin try print_decl vc_loc cntexample args info fmt d
            with Unsupported s -> raise (UnsupportedDecl (d,s)) end
        | _ -> () end
    | None -> () in
  print_decls task;
  pp_print_flush fmt ()

let () = register_printer "smtv2" print_task
  ~desc:"Printer@ for@ the@ SMTlib@ version@ 2@ format."
