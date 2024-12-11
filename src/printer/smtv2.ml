(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** SMT v2 printer with some extensions *)

open Format
open Pp
open Wstdlib
open Ident
open Ty
open Term
open Decl
open Printer
open Cntexmp_printer

let debug = Debug.register_info_flag "smtv2_printer"
  ~desc:"Print@ debugging@ messages@ about@ printing@ \
         the@ input@ of@ smtv2."

let debug_incremental = Debug.register_flag "force_incremental"
    ~desc:"Force@ incremental@ mode@ for@ smtv2@ provers"

(** SMTLIB tokens taken from CVC4/CVC5: src/parser/smt2/{Smt2.g,smt2.cpp} *)
let ident_printer () =
  let bls =
    [(* Base SMT-LIB commands, see page 43 *)
      "assert"; "check-sat"; "check-sat-assuming";
      "declare-const"; "define-const";
      "declare-datatype"; "declare-datatypes"; "declare-fun"; "declare-sort";
      "define-fun"; "define-fun-rec"; "define-funs-rec"; "define-sort";
      "echo"; "exit";
      "get-assignment"; "get-assertions"; "get-difficulty";
      "get-info"; "get-model"; "get-option"; "get-proof";
      "get-unsat-assumptions"; "get-unsat-core"; "get-value";
      "get-learned-literals";
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
      "simplify"; "include";
      "declare-codatatype"; "declare-codatatypes";
      "block-model"; "block-model-values";
      "get-qe"; "get-qe-disjunct";
      "get-abduct"; "get-abduct-next";
      "get-interpolant"; "get-interpolant-next";
      "declare-heap"; "declare-pool";

      (* operators, including theory symbols *)
      "="; "=>";
      "+"; "-"; "*"; "^" ;
      "<"; "<="; ">"; ">=";
      "ite";
      "and"; "distinct"; "is_int"; "not"; "or"; "select";
      "store"; "to_int"; "to_real"; "xor";
      "/"; "div"; "mod"; "rem";

      "concat"; "bvnot"; "bvand"; "bvor"; "bvneg"; "bvadd"; "bvmul"; "bvudiv";
      "bvurem"; "bvshl"; "bvlshr"; "bvult"; "bvnand"; "bvnor"; "bvxor"; "bvxnor";
      "bvcomp"; "bvsub"; "bvsdiv"; "bvsrem"; "bvsmod"; "bvashr"; "bvule";
      "bvugt"; "bvuge"; "bvslt"; "bvsle"; "bvsgt"; "bvsge";
      "rotate_left"; "rotate_right";
      "bvredor"; "bvredand";
      "bvuaddo"; "bvsaddo";
      "bvumulo"; "bvsmulo";
      "bvusubo"; "bvssubo";
      "bvsdivo";
      "zero_extend"; "sign_extend";

      "sqrt"; "sin"; "cos"; "tan"; "asin"; "acos"; "atan"; "pi";
      "exp"; "csc"; "sec"; "cot";
      "arcsin"; "arccos"; "arctan"; "arccsc"; "arcsec"; "arccot";

      (* tuple operators *)
      "tuple";
      "tuple.select"; "tuple.update"; "tuple.project";

      (* bags *)
      "bag";
      "table.project"; "table.aggr"; "table.join"; "table.group";

      (* sets *)
      "rel.group"; "rel.aggr"; "rel.project";

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
      "to_fp_bv"; "to_fp_fp"; "to_fp_real"; "to_fp_signed";

     (* the new proposed string theory *)
      "String"; "str.<"; "str.<=";
      "str.++"; "str.len"; "str.substr"; "str.contains"; "str.at";
      "str.indexof"; "str.prefixof"; "str.suffixof"; "int.to.str";
      "str.to.int"; "u16.to.str"; "str.to.u16"; "u32.to.str"; "str.to.u32";
      "str.in.re"; "str.to.re";
      "str.replace"; "str.tolower"; "str.toupper"; "str.rev";
      "str.to_lower"; "str.to_upper";
      "str.from_code"; "str.is_digit"; "str.from_int"; "str.to_int";
      "str.in_re"; "str.to_re"; "str.to_code"; "str.replace_all";
      "str.replace_re"; "str.replace_re_all";
      "str.indexof_re"; "str.update";
      "int.to.str"; "str.to.int"; "str.code"; "str.replaceall";

      (* sequences *)
      "seq.++";
      "seq.len";
      "seq.extract";
      "seq.update";
      "seq.at";
      "seq.contains";
      "seq.indexof";
      "seq.replace";
      "seq.prefixof";
      "seq.suffixof";
      "seq.rev";
      "seq.replace_all";
      "seq.unit";
      "seq.nth";

      "re.++"; "re.union"; "re.inter";
      "re.*"; "re.+"; "re.opt"; "re.^"; "re.range"; "re.loop";
      "re.comp"; "re.diff";

     (* the new proposed set theory *)
      "union"; "intersection"; "setminus"; "subset"; "member";
      "singleton"; "insert"; "card"; "complement"; "join";
      "product"; "transpose"; "tclosure";
      "set.comprehension";

     (* built-in sorts *)
      "Bool"; "Int"; "Real"; "BitVec"; "Array";

     (* Other stuff that Why3 seems to need *)
      "unsat"; "sat";
      "true"; "false";
      "const";
      "abs";
      "BitVec"; "extract"; "repeat"; "bv2nat"; "nat2bv";

     (* From Z3 *)
      "map"; "bv"; "default";
      "difference";

     (* From CVC4 / CVC5 *)
      "char"; "choose"; "is"; "update";

     (* Counterexamples specific keywords *)
      "lambda"; "LAMBDA"; "model";

      (* various stuff from
         "sed -n -e 's/^.*addOperator.*\"\([^\"]*\)\".*/\1/p' src/parser/smt2/smt2.cpp"

       *)

      "inst-closure"; "dt.size"; "sep"; "pto"; "wand"; "emp";
      "fmf.card"; "fmf.card.val";

    ]
  in
  let san = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer bls ~sanitizer:san

type version = V20 | V26 | V26Par

type info = {
  info_syn        : syntax_map;
  info_rliteral   : syntax_map;
  mutable info_model : S.t;
  mutable info_in_goal : bool;
  info_vc_term : vc_term_info;
  info_printer : ident_printer;
  mutable type_coercions : Sls.t Mty.t;
  mutable type_fields : (lsymbol list) Mty.t;
  mutable type_sorts  : tysymbol Mstr.t;
  mutable ty_tysymbol : ty Mts.t;
  info_version : version;
  meta_model_projection : Sls.t;
  meta_record_def : Sls.t;
  mutable record_fields : (lsymbol list) Mls.t;
  mutable constr_proj_id : string list Mls.t;
  mutable constructors: lsymbol Mstr.t;
  info_cntexample_need_push : bool;
  info_cntexample: bool;
  info_incremental: bool;
  info_set_incremental: bool;
  info_supports_reason_unknown : bool;
  info_supports_minimize: bool;
  mutable info_labels: Sattr.t Mstr.t;
  mutable incr_list_axioms: (prsymbol * term) list;
  mutable incr_list_ldecls: (lsymbol * vsymbol list * term) list;
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
  pp_print_string fmt (id_unique info.info_printer id)

(** type *)

let print_tv info fmt tv =
  pp_print_string fmt (id_unique info.info_printer tv.tv_name)

(** print `(par ...)` around the given body to print *)
let print_par info (* body *) =
  (* Format.kdprintf *) (fun print_body ->
      (fun fmt tvs ->
         if Ty.Stv.is_empty tvs
         then print_body fmt
         else if info.info_version = V26Par
         then
           Format.fprintf fmt "(par (%a)@ %t)"
             (print_iter1 Ty.Stv.iter pp_print_space (print_tv info)) tvs
             print_body
         else
           unsupported "smt: polymorphism must be encoded"
      ) ) (* body *)

let rec print_type info fmt ty = match ty.ty_node with
  | Tyvar s ->
      begin match info.info_version with
      | V20 -> unsupported "smtv2: you must encode type polymorphism"
      | V26 | V26Par -> print_tv info fmt s
      end
  | Tyapp (ts, l) ->
      begin match query_syntax info.info_syn ts.ts_name, l with
      | Some s, _ ->
        info.type_sorts <- Mstr.add s ts info.type_sorts;
        info.ty_tysymbol <- Mts.add ts ty info.ty_tysymbol;
        syntax_arguments s (print_type info) fmt l
      | None, [] -> print_ident info fmt ts.ts_name
      | None, _ -> fprintf fmt "(%a %a)" (print_ident info) ts.ts_name
          (print_list space (print_type info)) l
     end

let print_type info fmt ty = try print_type info fmt ty
  with Unsupported s -> raise (UnsupportedType (ty,s))

let print_type_value info fmt = function
  | None -> pp_print_string fmt "Bool"
  | Some ty -> print_type info fmt ty

(** var *)
let forget_var info v = forget_id info.info_printer v.vs_name

let print_var info fmt {vs_name = id} =
  let n = id_unique info.info_printer id in
  pp_print_string fmt n

let print_typed_var info fmt vs =
  fprintf fmt "(%a %a)" (print_var info) vs
    (print_type info) vs.vs_ty

let print_var_list info fmt vsl =
  print_list space (print_var info) fmt vsl

let print_typed_var_list info fmt vsl =
  print_list space (print_typed_var info) fmt vsl

let collect_model_ls info ls =
  if Sls.mem ls info.meta_model_projection then
    begin match ls.ls_args with
    | [ty] ->
      let coercions = Sls.add ls (Mty.find_def Sls.empty ty info.type_coercions) in
      info.type_coercions <- Mty.add ty coercions info.type_coercions
    | _ -> assert false
    end;
  if Sls.mem ls info.meta_record_def then
    begin match ls.ls_args with
    | [ty] ->
      let fields = ls :: (Mty.find_def [] ty info.type_fields) in
      info.type_fields <- Mty.add ty fields info.type_fields
    | _ -> assert false
    end;
  if relevant_for_counterexample ls.ls_name then
    info.info_model <-
      add_model_element (ls, ls.ls_name.id_loc, ls.ls_name.id_attrs) info.info_model

let number_format = {
    Number.long_int_support = `Default;
    Number.negative_int_support = `Default;
    Number.dec_int_support = `Default;
    Number.hex_int_support = `Unsupported;
    Number.oct_int_support = `Unsupported;
    Number.bin_int_support = `Unsupported;
    Number.negative_real_support = `Default;
    Number.dec_real_support = `Unsupported;
    Number.hex_real_support = `Unsupported;
    Number.frac_real_support =
      `Custom
        ((fun fmt i -> fprintf fmt "%s.0" i),
         (fun fmt i n -> fprintf fmt "(/ %s.0 %s.0)" i n));
}

let escape c = match c with
  | '\\'  -> "\\x5C"
  | '\"'  -> "\\x22"
  | '\032' .. '\126' -> Format.sprintf "%c" c
  | '\000' .. '\031'
  | '\127' .. '\255' -> Format.sprintf "\\x%02X" (Char.code c)

(* can the type of a value be derived from the type of the arguments? *)
let unambig_fs version fs =
  let rec lookup v ty = match ty.ty_node with
    | Tyvar u when tv_equal u v -> true
    | _ -> ty_any (lookup v) ty
  in
  let lookup v = List.exists (lookup v) fs.ls_args in
  let rec inspect ty = match ty.ty_node with
    | Tyvar u when not (lookup u) -> false
    | _ -> ty_all inspect ty
  in
  match version with
  | V20 -> true
  | V26 | V26Par ->  inspect (Option.get fs.ls_value)

(** expr *)
let rec print_term info fmt t =
  debug_print_term "Printing term: " t;
  if check_for_counterexample t
  then
    begin match t.t_node with
    | Tapp (ls,_) ->
      info.info_model <- add_model_element (ls,t.t_loc,t.t_attrs) info.info_model
    | _ -> assert false (* cannot happen because check_for_counterexample is true *)
    end;

  begin
   let ty = t.t_ty in
    match ty with
    | None -> ()
    | Some ty ->
      match ty.ty_node with
      | Tyvar _ -> ()
      | Tyapp (ts, _) ->
    info.ty_tysymbol <- Mts.add ts ty info.ty_tysymbol
  end;

  check_enter_vc_term t info.info_in_goal info.info_vc_term;

  let () = match t.t_node with
  | Tconst c ->
      let ts = match t.t_ty with
        | Some ({ ty_node = Tyapp (ts, []) } as ty) ->
          info.ty_tysymbol <- Mts.add ts ty info.ty_tysymbol;
          ts
        | _ -> assert false (* impossible *) in
      (* look for syntax literal ts in driver *)
      begin match query_syntax info.info_rliteral ts.ts_name, c with
        | Some st, Constant.ConstInt c ->
          info.type_sorts <- Mstr.add st ts info.type_sorts;
          syntax_range_literal st fmt c
        | Some st, Constant.ConstReal c ->
          info.type_sorts <- Mstr.add st ts info.type_sorts;
          let fp = match ts.ts_def with
            | Float fp -> fp
            | _ -> assert false in
          syntax_float_literal st fp fmt c
        | _, Constant.ConstStr _
        | None, _ ->
            (* we must check here that the type is either ty_int or
               ty_real, otherwise it makes no sense to print the
               literal. This may happen since we can't ensure that
               preserved literal types are exactly those that have a
               dedicated syntax rule *)
            if ts_equal ts ts_int || ts_equal ts ts_real || ts_equal ts ts_str then
              Constant.print number_format escape fmt c
            else
              unsupportedTerm t
                "smtv2: don't know how to print this literal, consider adding a syntax rule in the driver"
      end
  | Tvar v -> print_var info fmt v
  | Tapp (ls, tl) ->
    begin match query_syntax info.info_syn ls.ls_name with
      | Some s -> syntax_arguments_typed s (print_term info)
        (print_type info) t fmt tl
      | None -> begin match tl with (* for cvc3 wich doesn't accept (toto ) *)
          | [] ->

            let str_ls = sprintf "%a" (print_ident info) ls.ls_name in
            let cur_var = info.info_labels in
            let new_var = update_info_labels str_ls cur_var t ls in
            let () = info.info_labels <- new_var in
            let vc_term_info = info.info_vc_term in
            if vc_term_info.vc_inside then begin
              match vc_term_info.vc_loc with
              | None -> ()
              | Some loc ->
                let attrs = (* match vc_term_info.vc_func_name with
                  | None -> *)
                    ls.ls_name.id_attrs
                  (* | Some _ ->
                    model_trace_for_postcondition ~attrs:ls.ls_name.id_attrs info.info_vc_term
                   *)
                in
		let _t_check_pos = t_attr_set ~loc attrs t in
		(* TODO: temporarily disable collecting variables inside the term triggering VC *)
		(*info.info_model <- add_model_element t_check_pos info.info_model;*)
		()
	    end;
            if unambig_fs info.info_version ls then
	      fprintf fmt "@[%a@]" (print_ident info) ls.ls_name
            else
              fprintf fmt "@[(as %a %a)@]" (print_ident info) ls.ls_name
                (print_type info) (t_type t)
          | _ ->
            if unambig_fs info.info_version ls then
	      fprintf fmt "@[<hv2>(%a@ %a)@]"
	        (print_ident info) ls.ls_name
                (print_list space (print_term info)) tl
            else
              fprintf fmt "@[<hv2>((as %a@ %a)@ %a)@]"
                (print_ident info) ls.ls_name
                (print_type info) (t_type t)
                (print_list space (print_term info)) tl
        end
    end
  | Tlet (t1, tb) ->
      let v, t2 = t_open_bound tb in
      fprintf fmt "@[<hv2>(let ((%a %a))@ %a)@]" (print_var info) v
        (print_term info) t1 (print_term info) t2;
      forget_var info v
  | Tif (f1,t1,t2) ->
      fprintf fmt "@[<hv2>(ite %a@ %a@ %a)@]"
        (print_fmla info) f1 (print_term info) t1 (print_term info) t2
  | Tcase(t, bl) ->
     print_tcase info t print_term fmt bl
  | Teps _ -> unsupportedTerm t
      "smtv2: you must eliminate epsilon"
  | Tquant _ | Tbinop _ | Tnot _ | Ttrue | Tfalse -> raise (TermExpected t)
  in

  check_exit_vc_term t info.info_in_goal info.info_vc_term;

and print_fmla info fmt f =
  debug_print_term "Printing formula: " f;
  if check_for_counterexample f
  then
    begin match f.t_node with
    | Tapp (ls,_) ->
      info.info_model <- add_model_element (ls,f.t_loc,f.t_attrs) info.info_model
    | _ -> assert false (* cannot happen because check_for_counterexample is true *)
    end;

  check_enter_vc_term f info.info_in_goal info.info_vc_term;

  let () = match f.t_node with
  | Tapp ({ ls_name = id }, []) ->
      print_ident info fmt id
  | Tapp (ls, tl) -> begin match query_syntax info.info_syn ls.ls_name with
      | Some s -> syntax_arguments_typed s (print_term info)
        (print_type info) f fmt tl
      | None -> begin match tl with (* for cvc3 wich doesn't accept (toto ) *)
          | [] ->
              print_ident info fmt ls.ls_name
          | _ -> fprintf fmt "@[<hv2>(%a@ %a)@]"
              (print_ident info) ls.ls_name
              (print_list space (print_term info)) tl
        end end
  | Tquant (q, fq) ->
      let q = match q with Tforall -> "forall" | Texists -> "exists" in
      let vl, tl, f = t_open_quant fq in
      (* TODO trigger dépend des capacités du prover : 2 printers?
      smtwithtriggers/smtstrict *)
      if tl = [] then
        fprintf fmt "@[<hv2>(%s @[<h>(%a)@]@ %a)@]"
          q
          (print_typed_var_list info) vl
          (print_fmla info) f
      else
        fprintf fmt "@[<hv2>(%s @[<h>(%a)@]@ (! %a %a))@]"
          q
          (print_typed_var_list info) vl
          (print_fmla info) f
          (print_triggers info) tl;
      List.iter (forget_var info) vl
  | Tbinop (Tand, f1, f2) ->
      fprintf fmt "@[<hv2>(and@ %a@ %a)@]" (print_fmla info) f1 (print_fmla info) f2
  | Tbinop (Tor, f1, f2) ->
      fprintf fmt "@[<hv2>(or@ %a@ %a)@]" (print_fmla info) f1 (print_fmla info) f2
  | Tbinop (Timplies, f1, f2) ->
      fprintf fmt "@[<hv2>(=>@ %a@ %a)@]"
        (print_fmla info) f1 (print_fmla info) f2
  | Tbinop (Tiff, f1, f2) ->
      fprintf fmt "@[<hv2>(=@ %a@ %a)@]" (print_fmla info) f1 (print_fmla info) f2
  | Tnot f ->
      fprintf fmt "@[<hv2>(not@ %a)@]" (print_fmla info) f
  | Ttrue ->
      pp_print_string fmt "true"
  | Tfalse ->
      pp_print_string fmt "false"
  | Tif (f1, f2, f3) ->
      fprintf fmt "@[<hv2>(ite %a@ %a@ %a)@]"
        (print_fmla info) f1 (print_fmla info) f2 (print_fmla info) f3
  | Tlet (t1, tb) ->
      let v, f2 = t_open_bound tb in
      fprintf fmt "@[<hv2>(let ((%a %a))@ %a)@]" (print_var info) v
        (print_term info) t1 (print_fmla info) f2;
      forget_var info v
  | Tcase(t, bl) ->
     print_tcase info t print_fmla fmt bl
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f) in

  check_exit_vc_term f info.info_in_goal info.info_vc_term

and print_tcase info t pr fmt bl =
     let ty = t_type t in
     match ty.ty_node with
     | Tyapp (ts,_) when ts_equal ts ts_bool ->
        print_boolean_branches info t pr fmt bl
     | _ ->
        match info.info_version with
        | V20 | V26Par -> begin
            (* Use a chain of if-then-else constructs. *)
            match t.t_node with
            | Tvar v -> print_branches info v pr fmt bl
            | _ ->
               let subject = create_vsymbol (id_fresh "subject") (t_type t) in
               fprintf fmt "@[<hv2>(let ((%a @[%a@]))@ %a)@]"
                 (print_var info) subject (print_term info) t
                 (print_branches info subject pr) bl;
               forget_var info subject
          end
        | V26 ->
           fprintf fmt "@[<hv2>(match %a (@[<hv0>%a@]))@]"
             (print_term info) t
             (print_list space (print_match_branch info ty pr)) bl

and print_match_branch info ty pr fmt b =
  let (p,t) = t_open_branch b in
  let error () = unsupportedPattern p
    "smtv2: you must compile nested pattern-matching" in
  match p.pat_node with
  | Pwild ->
     let wild = create_vsymbol (id_fresh "wildcard") ty in
     fprintf fmt "@[<hv2>(%a %a)@]" (print_var info) wild (pr info) t
  | Papp(cs,[]) ->
     fprintf fmt "@[<hv2>(%a %a)@]" (print_ident info) cs.ls_name (pr info) t;
  | Papp(cs,args) ->
     let args = List.map (function
       | {pat_node = Pvar v} -> v | _ -> error ()) args in
     fprintf fmt "@[<hv2>(@[<hv2>(%a %a)@] %a)@]"
       (print_ident info) cs.ls_name (print_list space (print_var info)) args
       (pr info) t
  | _ -> error ()

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
        let t1, t2 = if ls_equal cs fs_bool_true then t1, t2 else t2, t1 in
        fprintf fmt "@[<hv2>(ite %a %a %a)@]"
          (print_term info) subject
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
          else
            begin match info.info_version with
              | V20 (* It was not defined at that time in the standard *) ->
                  fprintf fmt "@[<hv2>(ite (is-%a %a) %a %a)@]"
              | V26 | V26Par ->
                  fprintf fmt "@[<hv2>(ite ((_ is %a) %a) %a %a)@]"
            end
              (print_ident info) cs.ls_name (print_var info) subject
              (print_branch info subject pr) (cs,args,t)
              (print_branches info subject pr) bl
      | _ -> error ()

and print_branch info subject pr fmt (cs,vars,t) =
  if vars = [] then pr info fmt t else
  let tvs = t_freevars Mvs.empty t in
  if List.for_all (fun v -> not (Mvs.mem v tvs)) vars then pr info fmt t else
  let pr_proj fmt (v, p) =
    if Mvs.mem v tvs then fprintf fmt "(%a (%s %a))"
      (print_var info) v p (print_var info) subject in
  let l = List.combine vars (Mls.find cs info.constr_proj_id) in
  fprintf fmt "@[<hv2>(let (%a) %a)@]" (print_list space pr_proj) l (pr info) t

and print_expr info fmt =
  TermTF.t_select (print_term info fmt) (print_fmla info fmt)

and print_trigger info fmt e =
  print_expr info fmt e

and print_triggers info fmt = function
  | [] -> ()
  | a::l -> fprintf fmt ":pattern (%a) %a"
    (print_list space (print_trigger info)) a
    (print_triggers info) l

let print_type_decl info fmt ts =
  if is_alias_type_def ts.ts_def then () else
  if Mid.mem ts.ts_name info.info_syn then () else
  let sort_name = sprintf "%a" (print_ident info) ts.ts_name in
  info.type_sorts <- Mstr.add sort_name ts info.type_sorts;
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
    | _  ->
        let tvs = Term.ls_ty_freevars ls in
        fprintf fmt ";; %S@\n@[<v2>(declare-fun %a %a)@]@\n@\n"
          ls.ls_name.id_string (print_ident info) ls.ls_name
          (print_par info
             (fun fmt -> Format.fprintf fmt "(%a) %a"
                 (print_list space (print_type info)) ls.ls_args
                 (print_type_value info) ls.ls_value)) tvs

let rec has_quantification f =
  match f.t_node with
  | Tquant _ | Teps _ -> true
  | _ -> Term.t_any has_quantification f

let print_logic_decl_aux flag info fmt (ls,def) =
  if not (Mid.mem ls.ls_name info.info_syn) then begin
    collect_model_ls info ls;
    let vsl,expr = Decl.open_ls_defn def in
    if info.info_incremental && has_quantification expr then begin
      print_param_decl info fmt ls;
      info.incr_list_ldecls <- (ls, vsl, expr) :: info.incr_list_ldecls
    end else
      let tvs = Term.ls_ty_freevars ls in
      fprintf fmt ";; %S@\n@[<v2>(define-fun%s %a %a)@]@\n@\n"
        ls.ls_name.id_string flag
        (print_ident info) ls.ls_name
        (print_par info
           (fun fmt -> Format.fprintf fmt "@[<h>(%a) %a@]@ %a"
               (print_typed_var_list info) vsl
               (print_type_value info) ls.ls_value
               (print_expr info) expr)) tvs;
      List.iter (forget_var info) vsl
  end

let print_logic_decl = print_logic_decl_aux ""

let print_rec_logic_decl info fmt = function
  | [] -> ()
  | [ld] ->
      print_logic_decl_aux "-rec" info fmt ld
  | l ->
      let l = List.map (fun (ls,def) ->
          let vsl,expr = Decl.open_ls_defn def in
          (ls,vsl,expr)
        ) l
      in
      let print_decl fmt (ls,vsl,_) =
        if Mid.mem ls.ls_name info.info_syn then () else begin
          collect_model_ls info ls;
          let tvs = Term.ls_ty_freevars ls in
          fprintf fmt "@[<hov 2>(%a %a)@]@\n@\n"
            (print_ident info) ls.ls_name
            (print_par info
               (fun fmt -> Format.fprintf fmt "(%a) %a"
                   (print_typed_var_list info) vsl
                   (print_type_value info) ls.ls_value)) tvs;
        end
      in
      let print_term fmt (ls,_,expr) =
        if Mid.mem ls.ls_name info.info_syn then () else begin
          fprintf fmt "@[<hov 2>%a@]"
            (print_expr info) expr
        end
      in
      fprintf fmt "@[<hov 2>(define-funs-rec (%a) (%a))@]@\n@\n"
        (print_list nothing print_decl) l
        (print_list nothing print_term) l;
      List.iter (fun (_,vsl,_) -> List.iter (forget_var info) vsl) l

let print_info_model info =
  (* Prints the content of info.info_model *)
  let info_model = info.info_model in
  if not (S.is_empty info_model) && info.info_cntexample then
    begin
      let model_map =
        S.fold
          (fun ((ls,_,_) as el) acc ->
            let s = asprintf "%a" (print_ident info) ls.ls_name in
            Mstr.add s el acc)
          info_model
          Mstr.empty in ();

        (* Printing model has modification of info.info_model as undesirable
        side-effect. Revert it back. *)
        info.info_model <- info_model;
        model_map
    end
  else
    Mstr.empty


(* TODO factor out print_prop ? *)
let print_prop info fmt (pr, f) =
  let tvs = Term.t_ty_freevars Ty.Stv.empty f in
  fprintf fmt ";; %S@\n@[<hov 2>(assert@ %a)@]@\n@\n"
    pr.pr_name.id_string (* FIXME? collisions *)
    (print_par info (fun fmt -> print_fmla info fmt f)) tvs

let add_check_sat info fmt =
  if info.info_cntexample && info.info_cntexample_need_push then
    fprintf fmt "@[(push)@]@\n";
  fprintf fmt "@[(check-sat)@]@\n";
  if info.info_supports_reason_unknown then
    fprintf fmt "@[(get-info :reason-unknown)@]@\n";
  if info.info_cntexample then
    fprintf fmt "@[(get-model)@]@\n@\n"

let print_ldecl_axiom info fmt (ls, vls, t) =
  let tvs = Term.t_ty_freevars Ty.Stv.empty t in
  let tvs = List.fold_left (fun acc vs -> Ty.ty_freevars acc vs.vs_ty) tvs vls in
  fprintf fmt ";; %S@\n" ls.ls_name.id_string;
  fprintf fmt
    "@[<hv2>(assert@ @[<hv2>%a@])@]@\n@\n"
    (print_par info (fun fmt -> fprintf fmt
      "(forall @[(%a)@]@ @[<hv2>(= @[<h>(%a %a)@]@ %a)@])"
         (print_typed_var_list info) vls
         (print_ident info) ls.ls_name
         (print_var_list info) vls
         (print_expr info) t
     )) tvs




(* TODO if the property doesnt begin with quantifier, then we print it first.
   Else, we print it afterwards. *)
let print_incremental_axiom info fmt =
  List.iter (print_prop info fmt) info.incr_list_axioms;
  List.iter (print_ldecl_axiom info fmt) info.incr_list_ldecls;
  add_check_sat info fmt

let print_prop_decl vc_loc vc_attrs env printing_info info fmt k pr f = match k with
  | Paxiom ->
      if info.info_incremental && has_quantification f then
        info.incr_list_axioms <- (pr, f) :: info.incr_list_axioms
      else
        print_prop info fmt (pr, f)
  | Pgoal ->
      let tvs = Term.t_ty_freevars Ty.Stv.empty f in
      if not (Ty.Stv.is_empty tvs) then unsupported "smt: monomorphise goal must be applied";
      fprintf fmt ";; Goal %S@\n" pr.pr_name.id_string;
      (match pr.pr_name.id_loc with
        | None -> ()
        | Some loc -> fprintf fmt ";; File %a@\n" Loc.pp_position loc);
      info.info_in_goal <- true;
      fprintf fmt "@[(assert@\n";
      fprintf fmt "  @[(not@ %a))@]@\n@\n" (print_fmla info) f;
      info.info_in_goal <- false;
      add_check_sat info fmt;

      (* If in incremental mode, we empty the list of axioms we stored *)
      if info.info_incremental then
        print_incremental_axiom info fmt;

      let model_list = print_info_model info in

      let type_sorts =
        Mstr.map_filter
          (fun ts -> Mts.find_opt ts info.ty_tysymbol)
          info.type_sorts
      in

      printing_info := Some {
        why3_env = env;
        vc_term_loc = vc_loc;
        vc_term_attrs = vc_attrs;
        queried_terms = model_list;
        type_coercions = info.type_coercions;
        type_fields = info.type_fields;
        type_sorts = type_sorts;
        record_fields = info.record_fields;
        constructors = info.constructors;
        set_str = info.info_labels;
      }
  | Plemma -> assert false

let print_constructor_decl info is_record fmt (ls,args) =
  let cons_name = sprintf "%a" (print_ident info) ls.ls_name in
  info.constructors <- Mstr.add cons_name ls info.constructors;
  let field_names =
    (match args with
    | [] -> fprintf fmt "(%a)" (print_ident info) ls.ls_name; []
    | _ ->
        fprintf fmt "@[(%a@ " (print_ident info) ls.ls_name;
        let field_names, _ =
          List.fold_left2
          (fun (acc, i) ty pr ->
            let field_name =
              match pr with
              | Some pr ->
                  if not is_record then
                    unsupported "smtv2: sum types should not have projections";
                  let field_name = sprintf "%a" (print_ident info) pr.ls_name in
                  fprintf fmt "(%s" field_name;
                  let field_trace =
                    try
                      let attr = Sattr.choose (Sattr.filter (fun l ->
                        Strings.has_prefix "model_trace:" l.attr_string)
                        pr.ls_name.id_attrs) in
                      Strings.remove_prefix "model_trace:" attr.attr_string
                    with
                      Not_found -> ""
                  in
                  {field_name; field_trace; field_ident= Some pr.ls_name}
              | None ->
                  let field_name = id_fresh (ls.ls_name.id_string^"_proj") in
                  let field_name = create_vsymbol field_name ty(*dummy*) in
                  let field_name = sprintf "%a" (print_var info) field_name in
                  fprintf fmt "(%s" field_name;
                  {field_name; field_trace= ""; field_ident= None}
            in
            fprintf fmt " %a)" (print_type info) ty;
            (field_name :: acc, succ i)) ([], 1) ls.ls_args args
        in
        fprintf fmt ")@]";
        List.rev field_names)
  in

  info.constr_proj_id <-
    Mls.add ls (List.map (fun x -> x.field_name) field_names) info.constr_proj_id;
  if Strings.has_suffix "'mk" ls.ls_name.id_string then
    begin try
      let args = List.map Option.get args in
      info.record_fields <- Mls.add ls args info.record_fields
    with _ -> ()
    end

let print_data_decl info fmt (ts,cl) =
  let is_record = match cl with [_] -> true | _ -> false in
  let sort_name = sprintf "%a" (print_ident info) ts.ts_name in
  info.type_sorts <- Mstr.add sort_name ts info.type_sorts;
  fprintf fmt "@[(%a@ %a)@]"
    (print_ident info) ts.ts_name
    (print_list space (print_constructor_decl info is_record)) cl

let print_data_def info fmt (ts,cl) =
  let is_record = match cl with [_] -> true | _ -> false in
  if ts.ts_args <> [] then
    let args = List.map (fun arg -> arg.tv_name) ts.ts_args in
    fprintf fmt "@[(par (%a) (%a))@]"
      (print_list space (print_ident info)) args
      (print_list space (print_constructor_decl info is_record)) cl
  else
    fprintf fmt "@[(%a)@]"
      (print_list space (print_constructor_decl info is_record)) cl

let print_sort_decl info fmt (ts,_) =
  let sort_name = sprintf "%a" (print_ident info) ts.ts_name in
  info.type_sorts <- Mstr.add sort_name ts info.type_sorts;
  fprintf fmt "@[(%a %d)@]"
    (print_ident info) ts.ts_name
    (List.length ts.ts_args)

let set_produce_models fmt info =
  if info.info_cntexample then
    fprintf fmt "(set-option :produce-models true)@\n"

let set_incremental fmt info =
  if info.info_set_incremental then
    fprintf fmt "(set-option :incremental true)@\n"

let meta_counterexmp_need_push =
  Theory.register_meta_excl "counterexample_need_smtlib_push" []
                            ~desc:"Internal@ use@ only"

let meta_incremental =
  Theory.register_meta_excl "meta_incremental" []
                            ~desc:"Internal@ use@ only"

let meta_supports_minimize =
  Theory.register_meta_excl "supports_smtlib_minimize" []
                            ~desc:"solver supports SMTLIB `(minimize term)`"

let smtlib_minimize_attr = Ident.create_attribute "smtlib:minimize"

let meta_supports_reason_unknown =
  Theory.register_meta_excl "supports_smt_get_info_unknown_reason" []
                            ~desc:"Internal@ use@ only"


let print_decl vc_loc vc_attrs env printing_info info fmt d =
  match d.d_node with
  | Dtype ts ->
      print_type_decl info fmt ts
  | Ddata [(ts,_)] when query_syntax info.info_syn ts.ts_name <> None ->
      let st = Option.get (query_syntax info.info_syn ts.ts_name) in
      info.type_sorts <- Mstr.add st ts info.type_sorts
  | Ddata dl ->
      begin match info.info_version with
      | V20 ->
          fprintf fmt "@[<v2>(declare-datatypes ()@ (%a))@]@\n@\n"
            (print_list space (print_data_decl info)) dl
      | V26 | V26Par ->
          fprintf fmt "@[<v2>(declare-datatypes (%a)@ (%a))@]@\n@\n"
            (print_list space (print_sort_decl info)) dl
            (print_list space (print_data_def info)) dl
      end
  | Dparam ls ->
      collect_model_ls info ls;
      print_param_decl info fmt ls
  | Dlogic dl -> begin
      match info.info_version with
      | V20 | V26 ->
          print_list nothing (print_logic_decl info) fmt dl
      | V26Par -> begin
          match dl with
          | ([(s,_) as dl])
            when not (Sid.mem s.ls_name (get_used_syms_decl d)) ->
              print_logic_decl info fmt dl
          | dl ->
              print_rec_logic_decl info fmt dl
        end
    end
  | Dind _ -> unsupportedDecl d
                "smtv2: inductive definitions are not supported"
  | Dprop(Paxiom,_,({t_node = Tapp(_ps,[t]); t_attrs = a }))
    when Sattr.mem smtlib_minimize_attr a ->
      if info.info_supports_minimize then
        fprintf fmt "@[<v2>(minimize %a)@]@\n@\n" (print_term info) t
  | Dprop (k,pr,f) ->
      if Mid.mem pr.pr_name info.info_syn then () else
      print_prop_decl vc_loc vc_attrs env printing_info info fmt k pr f


let print_task version args ?old:_ fmt task =
  let cntexample = Driver.get_counterexmp task in
  let incremental =
    let incr_meta = Task.find_meta_tds task meta_incremental in
    not (Task.HStdecl.is_empty incr_meta)
  in
  let incremental = Debug.test_flag debug_incremental || incremental in
  let need_push =
    let need_push_meta = Task.find_meta_tds task meta_counterexmp_need_push in
    not (Task.HStdecl.is_empty need_push_meta)
  in
  let supports_reason_unknown =
    let m = Task.find_meta_tds task meta_supports_reason_unknown in
    not (Task.HStdecl.is_empty m)
  in
  let supports_minimize =
    let m = Task.find_meta_tds task meta_supports_minimize in
    not (Task.HStdecl.is_empty m)
  in
  let g,_ = Task.task_separate_goal task in
  let vc_loc =
    Theory.(match g.td_node with
        | Decl { d_node = Dprop (_,_,t) } -> t.t_loc
        | _ -> None)
  in
  let vc_attrs = (Task.task_goal_fmla task).t_attrs in
  let vc_info = {vc_inside = false; vc_loc; vc_func_name = None} in
  let info = {
    info_syn = Discriminate.get_syntax_map task;
    info_rliteral = Printer.get_rliteral_map task;
    info_model = S.empty;
    info_in_goal = false;
    info_vc_term = vc_info;
    info_printer = ident_printer ();
    type_coercions = Mty.empty;
    type_fields = Mty.empty;
    type_sorts = Mstr.empty;
    ty_tysymbol = Mts.empty;
    info_version = version;
    meta_model_projection = Task.on_tagged_ls Theory.meta_model_projection task;
    meta_record_def = Task.on_tagged_ls Theory.meta_record task;
    record_fields = Mls.empty;
    constr_proj_id = Mls.empty;
    constructors = Mstr.empty;
    info_cntexample_need_push = need_push;
    info_cntexample = cntexample;
    info_incremental = incremental;
    info_labels = Mstr.empty;
    (* info_set_incremental add the incremental option to the header. It is not
       needed for some provers
    *)
    info_set_incremental = not need_push && incremental;
    info_supports_reason_unknown = supports_reason_unknown;
    info_supports_minimize = supports_minimize;
    incr_list_axioms = [];
    incr_list_ldecls = [];
    }
  in
  print_prelude fmt args.prelude;
  set_produce_models fmt info;
  set_incremental fmt info;
  print_th_prelude task fmt args.th_prelude;
  let rec print_decls = function
    | Some t ->
        print_decls t.Task.task_prev;
        begin match t.Task.task_decl.Theory.td_node with
        | Theory.Decl d ->
            begin try print_decl vc_loc vc_attrs args.env args.printing_info info fmt d
            with Unsupported s -> raise (UnsupportedDecl (d,s)) end
        | _ -> () end
    | None -> () in
  print_decls task;
  pp_print_flush fmt ()

let () = register_printer "smtv2" (print_task V20)
  ~desc:"Printer@ for@ the@ SMTlib@ version@ 2@ format."
let () = register_printer "smtv2.6" (print_task V26)
  ~desc:"Printer@ for@ the@ SMTlib@ version@ 2.6@ format."
let () = register_printer "smtv2.6par" (print_task V26Par)
  ~desc:"Printer@ for@ the@ SMTlib@ version@ 2.6@ format with (par construct from version 3."
