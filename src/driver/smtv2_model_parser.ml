(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2022 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Wstdlib
open Term
open Smtv2_model_defs
open Model_parser

let debug =
  Debug.register_flag "smtv2_parser"
    ~desc:
      "Print@ debugging@ messages@ about@ parsing@ the@ SMTv2@ model@ for@ \
       counterexamples."

(*
**********************************************************************
**  Parsing the prover output (as string) to S-expressions
**********************************************************************
*)

module FromStringToSexp = struct
  exception E of string

  let fix_CVC18_bug_on_float_constants =
    let r = Re.Str.regexp "\\((fp #b[01] #b[01]+ #b[01]+\\)" in
    fun s -> Re.Str.global_replace r "\\1)" s

  let parse_string str =
    Debug.dprintf debug "[parse_string] model_string = %s@." str;
    let lexbuf = Lexing.from_string str in
    try Sexp.read_list lexbuf
    with Sexp.Error -> (
      let msg =
        Format.sprintf "Cannot parse as S-expression at character %d"
          (Lexing.lexeme_start lexbuf)
      in
      (* workaround for CVC4 1.8 bug in printing float constants *)
      let str = fix_CVC18_bug_on_float_constants str in
      let lexbuf = Lexing.from_string str in
      try Sexp.read_list lexbuf with Sexp.Error -> raise (E msg))
end

(*
**********************************************************************
**  Converting S-expressions to Smtv2_model_defs.fun_def
**********************************************************************
*)

module FromSexpToModel = struct
  open Sexp

  exception E of sexp * string

  let error sexp s = raise (E (sexp, s))
  let atom_error a s = raise (E (Atom a, s))

  let is_simple_symbol str =
    String.length str > 0
    &&
    match str.[0] with
    | '_' | 'a' .. 'z' | 'A' .. 'Z' | '#' | '$' -> true
    | _ -> false

  let is_prover_symbol str =
    (* as defined in SMT-LIB Standard *)
    (String.length str > 0 && (str.[0] == '@' || str.[0] == '.'))
    ||
    (* special cases with Z3 prover *)
    match String.split_on_char '!' str with
    | [ _; "val"; _ ] -> true
    | _ -> false

  let is_quoted s =
    String.length s > 2 && s.[0] = '|' && s.[String.length s - 1] = '|'

  let get_quoted s = String.sub s 1 (String.length s - 2)

  let is_string s =
    String.length s >= 2 && s.[0] = '"' && s.[String.length s - 1] = '"'

  let get_string s = String.sub s 1 (String.length s - 2)

  let rec pp_sexp fmt = function
    | Atom s -> Format.pp_print_string fmt s
    | List l ->
        Format.fprintf fmt "@[@[<hv2>(%a@])@]" Pp.(print_list space pp_sexp) l

  let string_of_sexp = Format.asprintf "%a" pp_sexp
  let atom f = function Atom s -> f s | sexp -> error sexp "atom"

  let list f = function
    | List l -> List.map f l
    | Atom _ as sexp -> error sexp "list"

  let string = function
    | Atom s when is_string s -> get_string s
    | sexp -> error sexp "string"

  let bool = atom bool_of_string
  let int = atom int_of_string
  let bigint = atom BigInt.of_string

  let positive_constant_int = function
    | Atom s -> (
        try BigInt.of_string s with _ -> atom_error s "constant_int")
    | sexp -> error sexp "positive_constant_int"

  let negative_constant_int = function
    | List [ Atom "-"; i ] as sexp -> (
        try BigInt.minus (atom BigInt.of_string i)
        with _ -> error sexp "negative_constant_int")
    | sexp -> error sexp "negative_constant_int"

  let constant_int sexp =
    try positive_constant_int sexp
    with _ -> (
      try negative_constant_int sexp with _ -> error sexp "constant_int")

  let positive_constant_dec s =
    try Scanf.sscanf s "%[^.].%s" (fun s1 s2 -> (s1, s2))
    with _ -> atom_error s "constant_dec"

  let constant_dec = function
    | Atom s ->
        let s1, s2 = positive_constant_dec s in
        { real_neg = false; real_int = s1; real_frac = s2 }
    | List [ Atom "-"; Atom s ] ->
        let s1, s2 = positive_constant_dec s in
        { real_neg = true; real_int = s1; real_frac = s2 }
    | sexp -> error sexp "constant_dec"

  let constant_fraction ~neg sexp =
    let positive_constant_int_fraction = function
      | Atom s -> (
          try (false, BigInt.of_string s)
          with _ -> atom_error s "positive_constant_int_fraction")
      | sexp -> error sexp "positive_constant_int_fraction"
    in
    let negative_constant_int_fraction = function
      | List [ Atom "-"; i ] as sexp -> (
          try (true, atom BigInt.of_string i)
          with _ -> error sexp "negative_constant_int_fraction")
      | sexp -> error sexp "negative_constant_int_fraction"
    in
    let constant_int_fraction sexp =
      let zero = "0" in
      let neg, c =
        try positive_constant_int_fraction sexp
        with _ -> (
          try negative_constant_int_fraction sexp
          with _ -> error sexp "constant_int_fraction")
      in
      { real_neg = neg; real_int = BigInt.to_string c; real_frac = zero }
    in
    let constant_int_or_dec_fraction n =
      try constant_int_fraction n with _ -> constant_dec n
    in
    let neg_constant_real { real_neg = neg; real_int = s1; real_frac = s2 } =
      { real_neg = not neg; real_int = s1; real_frac = s2 }
    in
    match sexp with
    | List [ Atom "/"; n1; n2 ] ->
        let r1 = constant_int_or_dec_fraction n1 in
        let r2 = constant_int_or_dec_fraction n2 in
        if neg then Cfraction (neg_constant_real r1, r2) else Cfraction (r1, r2)
    | _ -> error sexp "constant_fraction"

  let constant_fraction sexp =
    match sexp with
    | List [ Atom "-"; frac ] -> constant_fraction ~neg:true frac
    | _ -> constant_fraction ~neg:false sexp

  let constant_bv_bin = function
    | Atom s -> (
        try
          let s' = Strings.remove_prefix "#b" s in
          let bv_value = BigInt.of_string ("0b" ^ s') in
          let bv_length = String.length s' in
          { bv_value; bv_length; bv_verbatim = s }
        with _ -> atom_error s "constant_bv_bin")
    | sexp -> error sexp "constant_bv_bin"

  let constant_bv_hex = function
    | Atom s -> (
        try
          let s' = Strings.remove_prefix "#x" s in
          let bv_value = BigInt.of_string ("0x" ^ s') in
          let bv_length = String.length s' * 4 in
          { bv_value; bv_length; bv_verbatim = s }
        with _ -> atom_error s "constant_bv_hex")
    | sexp -> error sexp "constant_bv_hex"

  let constant_bv_dec = function
    | List [ Atom "_"; Atom n; l ] as sexp -> (
        try
          let bv_value = BigInt.of_string (Strings.remove_prefix "bv" n) in
          let bv_length = int l in
          { bv_value; bv_length; bv_verbatim = string_of_sexp sexp }
        with _ -> error sexp "constant_bv_dec")
    | sexp -> error sexp "constant_bv_dec"

  let constant_bv sexp =
    try constant_bv_dec sexp
    with _ -> (
      try constant_bv_hex sexp
      with _ -> (
        try constant_bv_bin sexp with _ -> error sexp "constant_bv"))

  let constant_float = function
    | List [ Atom "_"; Atom "+zero"; n1; n2 ] ->
        ignore (bigint n1, bigint n2);
        Fpluszero
    | List [ Atom "_"; Atom "-zero"; n1; n2 ] ->
        ignore (bigint n1, bigint n2);
        Fminuszero
    | List [ Atom "_"; Atom "+oo"; n1; n2 ] ->
        ignore (bigint n1, bigint n2);
        Fplusinfinity
    | List [ Atom "_"; Atom "-oo"; n1; n2 ] ->
        ignore (bigint n1, bigint n2);
        Fminusinfinity
    | List [ Atom "_"; Atom "NaN"; n1; n2 ] ->
        ignore (bigint n1, bigint n2);
        Fnan
    | List [ Atom "fp"; sign; exp; mant ] ->
        let sign = constant_bv sign
        and exp = constant_bv exp
        and mant = constant_bv mant in
        Fnumber { sign; exp; mant }
    | sexp -> error sexp "constant_float"

  let constant sexp : term =
    let cst =
      try Cint (constant_int sexp)
      with _ -> (
        try Cdecimal (constant_dec sexp)
        with _ -> (
          try constant_fraction sexp
          with _ -> (
            try Cbitvector (constant_bv sexp)
            with _ -> (
              try Cfloat (constant_float sexp)
              with _ -> (
                try Cbool (bool sexp)
                with _ -> (
                  try Cstring (string sexp) with _ -> error sexp "constant"))))))
    in
    Tconst cst

  let symbol : sexp -> symbol = function
    | Atom s when is_prover_symbol s -> Sprover s
    | Atom s when is_simple_symbol s -> S s
    | Atom s when is_quoted s ->
        let s' = get_quoted s in
        if is_prover_symbol s' then Sprover s' else S s'
    | sexp -> error sexp "symbol"

  let index sexp : index =
    try Idxnumeral (bigint sexp)
    with _ -> ( try Idxsymbol (symbol sexp) with _ -> error sexp "index")

  let identifier sexp : identifier =
    let builtins = [ "="; "*"; "+"; "<="; ">="; "<"; ">" ] in
    match sexp with
    | Atom s when List.mem s builtins -> Isymbol (S s)
    | Atom _ -> Isymbol (symbol sexp)
    | List [ Atom "_"; s; List idx ] ->
        Iindexedsymbol (symbol s, List.map index idx)
    | sexp -> error sexp "identifier"

  let rec sort : sexp -> sort = function
    | Atom "String" -> Sstring
    | Atom "RegLan" -> Sreglan
    | Atom "Int" -> Sint
    | Atom "Real" -> Sreal
    | Atom "RoundingMode" -> Sroundingmode
    | Atom "Bool" -> Sbool
    | List [ Atom "_"; Atom "BitVec"; Atom n ] as sexp -> (
        try Sbitvec (int_of_string n) with _ -> error sexp "bitvector sort")
    | Atom "Float16" -> Sfloatingpoint (5, 11)
    | Atom "Float32" -> Sfloatingpoint (8, 24)
    | Atom "Float64" -> Sfloatingpoint (11, 53)
    | Atom "Float128" -> Sfloatingpoint (15, 113)
    | List [ Atom "_"; Atom "FloatingPoint"; Atom eb; Atom sb ] as sexp -> (
        try Sfloatingpoint (int_of_string eb, int_of_string sb)
        with _ -> error sexp "floatingpoint sort")
    | List [ Atom "Array"; s1; s2 ] -> Sarray (sort s1, sort s2)
    | Atom _ as sexp -> Ssimple (identifier sexp)
    | List (Atom n :: l) -> Smultiple (identifier (Atom n), List.map sort l)
    | sexp -> error sexp "sort"

  let get_type_from_prover_variable name =
    (* we try to infer the type from [name], for example:
        - infer the type int32 from the name @uc_int32_1
        - infer the type ref int32 from the name @uc_(ref int32)_0
        - infer the type ref from the name ref!val!0 *)
    (* should not be useful anymore for CVC5, but still useful for
       CVC4 and Z3 *)
    let opt_name =
      if Strings.has_prefix "@" name || Strings.has_prefix "." name then
        try
          let left = String.index name '_' + 1 in
          let right = String.rindex name '_' in
          Some (String.sub name left (right - left))
        with _ -> None
      else
        match String.split_on_char '!' name with
        | [ ty; _; _ ] -> Some ty
        | _ -> None
    in
    match FromStringToSexp.parse_string (Opt.get_def "" opt_name) with
    | [] -> atom_error name "get_type_from_prover_variable"
    | [ sexp ] -> sexp
    | sexps -> List sexps

  let qualified_identifier sexp : qual_identifier =
    match sexp with
    | Atom _ -> (
        let id = identifier sexp in
        match id with
        | Isymbol (Sprover n') | Iindexedsymbol (Sprover n', _) ->
            let ty_sexp = get_type_from_prover_variable n' in
            Qannotident (id, sort ty_sexp)
        | Isymbol _ | Iindexedsymbol _ -> Qident id)
    | List [ Atom "as"; id; s ] -> Qannotident (identifier id, sort s)
    | sexp -> error sexp "qualified_identifier"

  let arg = function
    | List [ n; s ] -> (symbol n, sort s)
    | sexp -> error sexp "arg"

  let rec term sexp =
    try constant sexp
    with _ -> (
      try Tvar (qualified_identifier sexp)
      with _ -> (
        try ite sexp
        with _ -> (
          try array sexp
          with _ -> (
            try application sexp with _ -> Tunparsed (string_of_sexp sexp)))))

  and ite = function
    | List [ Atom "ite"; t1; t2; t3 ] -> Tite (term t1, term t2, term t3)
    | sexp -> error sexp "ite"

  and var_binding = function
    | List [ Atom s; t ] -> (symbol (Atom s), term t)
    | sexp -> error sexp "var_binding"

  and application = function
    | List (qual_id :: ts) ->
        Tapply (qualified_identifier qual_id, List.map term ts)
    | sexp -> error sexp "application"

  and array sexp =
    match sexp with
    (* "_ as-array" not supported because not associated to sorts for indices/values*)
    | List
        [ List [ Atom "as"; Atom "const"; List [ Atom "Array"; s1; s2 ] ]; t ]
      ->
        Tarray (sort s1, sort s2, { array_indices = []; array_others = term t })
    | List [ Atom "store"; x; t1; t2 ] -> (
        let a = try array x with _ -> error sexp "array" in
        match a with
        | Tarray (s1, s2, elts) ->
            Tarray
              ( s1,
                s2,
                {
                  array_indices = (term t1, term t2) :: elts.array_indices;
                  array_others = elts.array_others;
                } )
        | _ -> error sexp "array")
    | _ -> error sexp "array"

  let fun_def : sexp -> (string * function_def) option = function
    | List [ Atom "define-fun"; Atom n; args; res; body ] ->
        let res = sort res in
        let args = list arg args and body = term body in
        Some (n, (args, res, body))
    | _ -> None

  let is_model_decl = function Atom "define-fun" -> true | _ -> false

  let get_and_check_model sexps =
    if sexps = [] then []
    else
      let model, rest =
        match sexps with
        | List (Atom "model" :: model) :: rest -> (model, rest)
        | List model :: rest when List.exists (Sexp.exists is_model_decl) model
          ->
            (model, rest)
        | _ -> failwith "Cannot read S-expression as model: model not first"
      in
      if List.exists (Sexp.exists is_model_decl) rest then
        failwith
          "Cannot read S-expression as model: next model not separated \
           (missing separator in driver?)"
      else model

  let get_fun_defs model =
    let fun_defs = List.filter_map fun_def model in
    Mstr.of_list fun_defs
end

(*
**********************************************************************
**  Converting Smtv2_model_defs.fun_def to Term.term
**********************************************************************
*)

module FromModelToTerm = struct
  exception E of string
  exception NoArgConstructor
  exception UnknownType
  exception NoBuiltinSymbol
  exception Float_MinusZero
  exception Float_PlusZero
  exception Float_NaN
  exception Float_Infinity
  exception Float_Error

  let error fmt = Format.kasprintf (fun msg -> raise (E msg)) fmt

  type env = {
    (* Why3 environment, used to retrieve builtin theories. *)
    why3_env : Env.env;
    (* Constructors from [pinfo.Printer.constructors]. *)
    constructors : lsymbol Mstr.t;
    type_fields : Term.lsymbol list Ty.Mty.t;
    (* Queried terms from [pinfo.Printer.queried_terms]. *)
    queried_terms : lsymbol Mstr.t;
    (* Function definiions that are not in [pinfo.Printer.queried_terms]. *)
    mutable prover_fun_defs : (Term.term * concrete_syntax_term) Mstr.t;
    (* Prover variables, may have the same name if the sort is different. *)
    mutable prover_vars : vsymbol Ty.Mty.t Mstr.t;
    (* Bound variables in the body of a function or in a let construction. *)
    mutable bound_vars : vsymbol Mstr.t;
    (* Inferred associations between Why3 types and SMT sorts, coming from lsymbols
       in [pinfo.Printer.queried_terms]. *)
    mutable inferred_types : (sort * Ty.ty) list;
    (* Evaluation of prover variables (using type coercions and fields). *)
    mutable eval_prover_vars : (Term.term * concrete_syntax_term) Mvs.t;
  }

  (* Convert a SMT sort [s] to a Why3 type.
     If [update_ty] is equal to [Some ty], the function updates [env.inferred_types]
      with the association [(s,ty)]. *)
  let rec smt_sort_to_ty ?(update_ty = None) env s =
    try
      match s with
      | Sstring -> Ty.ty_str
      | Sint -> Ty.ty_int
      | Sreal -> Ty.ty_real
      | Sbool -> Ty.ty_bool
      | Sarray (s1, s2) -> (
          match update_ty with
          | None ->
              Ty.ty_app Ty.ts_func
                [ smt_sort_to_ty env s1; smt_sort_to_ty env s2 ]
          | Some ty -> (
              match ty.Ty.ty_node with
              | Ty.Tyapp (ts, [ ty1; ty2 ]) when Ty.ts_equal ts Ty.ts_func ->
                  Ty.ty_app Ty.ts_func
                    [
                      smt_sort_to_ty ~update_ty:(Some ty1) env s1;
                      smt_sort_to_ty ~update_ty:(Some ty2) env s2;
                    ]
              | _ ->
                  error "Inconsistent shapes for type %a and sort %a"
                    Pretty.print_ty ty print_sort s))
      | Sroundingmode | Sfloatingpoint _ | Sbitvec _ | Ssimple _ | Smultiple _
        -> (
          match
            List.find_all (fun (s', _) -> sort_equal s s') env.inferred_types
          with
          | [] -> raise UnknownType
          | [ (_, ty) ] -> ty
          | _ ->
              error "Multiple matches in inferred_types for sort %a@."
                print_sort s)
      | _ -> raise UnknownType
    with UnknownType -> (
      match update_ty with
      | None -> error "Cannot infer type from sort %a@." print_sort s
      | Some ty ->
          Debug.dprintf debug
            "[smt_sort_to_ty] updating inferred_types with s = %a, ty = %a@."
            print_sort s Pretty.print_ty ty;
          env.inferred_types <- (s, ty) :: env.inferred_types;
          ty)

  let qual_id_to_term env qid =
    (* Constructors without arguments should not be confused with variables. *)
    let is_no_arg_constructor n constructors =
      match Mstr.find_opt n constructors with
      | Some ls -> List.length ls.ls_args = 0
      | None -> false
    in
    let vs =
      match qid with
      (* For Qident, no sort is associated to the identifier, so we cannot infer
        the type of the variable. So we raise an error if we do not find [n] in
        [env.bound_vars] or in [env.prover_vars]. *)
      | Qident (Isymbol (S n)) ->
          if is_no_arg_constructor n env.constructors then raise NoArgConstructor
          else
            begin try Mstr.find n env.bound_vars
            with Not_found ->
              error
                "No variable in bound_vars matching qualified identifier %a@."
                print_qualified_identifier qid
            end
      | Qident (Isymbol (Sprover n)) -> (
          match Ty.Mty.values (Mstr.find n env.prover_vars) with
          | [] | (exception Not_found) ->
              error
                "No variable in prover_vars matching qualified identifier %a@."
                print_qualified_identifier qid
          | [ vs ] -> vs
          | _ :: _ :: _ ->
              error
                "Multiple variables in prover_vars matching qualified identifier \
                %a@."
                print_qualified_identifier qid)
      (* For Qannotident, there is a sort associated to the identifier, so we can infer
          the type of the variable. *)
      | Qannotident (Isymbol (S n), s) ->
          if is_no_arg_constructor n env.constructors then raise NoArgConstructor
          else
            let vs_ty = smt_sort_to_ty env s in
            let vs =
              try
                let vs = Mstr.find n env.bound_vars in
                if Ty.ty_equal vs.vs_ty vs_ty then vs
                else
                  error "Type %a of variable %a does not match sort %a@."
                    Pretty.print_ty vs.vs_ty Pretty.print_vs vs print_sort s
              with Not_found ->
                (* Create a fresh vsymbol if not found in [env.bound_vars]. *)
                create_vsymbol (Ident.id_fresh n) vs_ty
            in
            vs
      | Qannotident (Isymbol (Sprover n), s) -> (
          let vs_ty = smt_sort_to_ty env s in
          let new_vs = create_vsymbol (Ident.id_fresh n) vs_ty in
          (* Update [env.prover_vars] either if the prover variable [n]
              is not yet stored in [env.prover_vars], or if there already
              exists a mapping for [n] but not for the current sort [s].
              (Because prover variables can have the same name if with different
              sorts). *)
          try
            let mvs = Mstr.find n env.prover_vars in
            match Ty.Mty.find vs_ty mvs with
            | vs -> vs
            | exception Not_found ->
                Debug.dprintf debug
                  "[qual_id_to_term] updating prover_vars with vs = %a / vs_ty = \
                  %a@."
                  Pretty.print_vs new_vs Pretty.print_ty vs_ty;
                env.prover_vars <-
                  Mstr.add n (Ty.Mty.add vs_ty new_vs mvs) env.prover_vars;
                new_vs
          with Not_found ->
            Debug.dprintf debug
              "[qual_id_to_term] updating prover_vars with vs = %a / vs_ty = %a@."
              Pretty.print_vs new_vs Pretty.print_ty vs_ty;
            env.prover_vars <-
              Mstr.add n (Ty.Mty.add vs_ty new_vs Ty.Mty.empty) env.prover_vars;
            new_vs)
      | _ ->
          error "Could not interpret qualified identifier %a@."
            print_qualified_identifier qid
    in
    (t_var vs, concrete_var_from_vs vs)

  let pad_with_zeros width s =
    let filled =
      let len = width - String.length s in
      if len <= 0 then "" else String.make len '0'
    in
    filled ^ s

  let float_of_binary fp =
    match fp with
    | Fplusinfinity | Fminusinfinity -> raise Float_Infinity
    | Fpluszero -> raise Float_PlusZero
    | Fminuszero -> raise Float_MinusZero
    | Fnan -> raise Float_NaN
    | Fnumber { sign; exp; mant } ->
        let fp_str = (sign.bv_verbatim, exp.bv_verbatim, mant.bv_verbatim) in
        let exp_bias = BigInt.pred (BigInt.pow_int_pos 2 (exp.bv_length - 1)) in
        let exp_max = BigInt.pred (BigInt.pow_int_pos 2 exp.bv_length) in
        let frac_len =
          (* Length of the hexadecimal representation (after the ".") *)
          if mant.bv_length mod 4 = 0 then mant.bv_length / 4
          else (mant.bv_length / 4) + 1
        in
        let is_neg =
          match BigInt.to_int sign.bv_value with
          | 0 -> false
          | 1 -> true
          | _ -> raise Float_Error
        in
        (* Compute exponent (int) and frac (string of hexa) *)
        let frac =
          (* The hex value is used after the decimal point. So we need to adjust
              it to the number of binary elements there are.
              Example in 32bits: significand is 23 bits, and the hexadecimal
              representation will have a multiple of 4 bits (ie 24). So, we need to
              multiply by two to account the difference. *)
          if Strings.has_prefix "#b" mant.bv_verbatim then
            let adjust = 4 - (mant.bv_length mod 4) in
            if adjust = 4 then mant.bv_value (* No adjustment needed *)
            else BigInt.mul (BigInt.pow_int_pos 2 adjust) mant.bv_value
          else mant.bv_value
        in
        let frac =
          pad_with_zeros frac_len (Format.sprintf "%x" (BigInt.to_int frac))
        in
        if BigInt.eq exp.bv_value BigInt.zero then
          (* subnormals and zero *)
          (* Case for zero *)
          if BigInt.eq mant.bv_value BigInt.zero then
            if is_neg then raise Float_MinusZero else raise Float_PlusZero
          else
            (* Subnormals *)
            let exp = BigInt.pred exp_bias in
            ( is_neg,
              "0",
              frac,
              Some (String.concat "" [ "-"; BigInt.to_string exp ]),
              fp_str )
        else if BigInt.eq exp.bv_value exp_max (* infinities and NaN *) then
          if BigInt.eq mant.bv_value BigInt.zero then raise Float_Infinity
          else raise Float_NaN
        else
          let exp = BigInt.sub exp.bv_value exp_bias in
          (is_neg, "1", frac, Some (BigInt.to_string exp), fp_str)

  let constant_to_term env c =
    let decimal_string neg s1 s2 =
      if neg then String.concat "" [s1;".";s2]
      else String.concat "" ["-";s1;".";s2]
    in
    match c with
    | Cint bigint ->
      let t = t_const (Constant.int_const bigint) Ty.ty_int in
      let t_concrete = Const (Integer (BigInt.to_string bigint)) in
      (t, t_concrete)
    | Cdecimal { real_neg = neg; real_int = s1; real_frac = s2 } ->
      let t =
        t_const
          (Constant.real_const_from_string ~radix:10 ~neg ~int:s1 ~frac:s2
             ~exp:None)
          Ty.ty_real
      in
      let t_concrete = Const (Real (decimal_string neg s1 s2)) in
      (t, t_concrete)
    | Cfraction
        ( { real_neg = neg; real_int = s1; real_frac = s2 },
          { real_neg = neg'; real_int = s1'; real_frac = s2' } ) -> (
        try
          let t =
            t_const
              (Constant.real_const_from_string ~radix:10 ~neg ~int:s1 ~frac:s2
                 ~exp:None)
              Ty.ty_real
          in
          let t' =
            t_const
              (Constant.real_const_from_string ~radix:10 ~neg:neg' ~int:s1'
                 ~frac:s2' ~exp:None)
              Ty.ty_real
          in
          let th = Env.read_theory env.why3_env [ "real" ] "Real" in
          let div_ls =
            Theory.ns_find_ls th.Theory.th_export [ Ident.op_infix "/" ]
          in
          let t_concrete =
            Const (Fraction (decimal_string neg s1 s2, decimal_string neg' s1' s2'))
          in
          (t_app div_ls [ t; t' ] div_ls.ls_value, t_concrete)
        with _ ->
          error "Could not interpret constant %a as a fraction@." print_constant
            c)
    | Cbitvector { bv_value = bigint; bv_length = n; _ } -> (
        try
          let _, ty =
            List.find
              (function Sbitvec n', _ when n = n' -> true | _ -> false)
              env.inferred_types
          in
          let t_concrete = Const (Integer (BigInt.to_string bigint)) in
          (t_const (Constant.int_const bigint) ty, t_concrete)
        with Not_found ->
          error
            "No matching type found in inferred_type for bitvector constant \
             %a@."
            print_constant c)
    | Cfloat fp -> (
        let sort, ty =
          match
            List.find_all
              (function Sfloatingpoint _, _ -> true | _ -> false)
              env.inferred_types
          with
          | [] ->
              error
                "No matching type found in inferred_type for float constant \
                 %a@."
                print_constant c
          | [ sort_ty ] -> sort_ty
          | _ ->
              (* FIXME we should use the size of bitvectors in [fp] to match more
                 precisely with sorts [Sfloatingpoint _,_] *)
              error
                "Multiple matching types found in inferred_type for float \
                 constant %a@."
                print_constant c
        in
        let float_lib =
          match sort with
          | Sfloatingpoint (a, b) -> "Float" ^ string_of_int (a + b)
          | _ -> assert false
        in
        try
          (* general case *)
          let neg, s1, s2, exp, (sign_str,exp_str,mant_str) = float_of_binary fp in
          let t =
            t_const
              (Constant.real_const_from_string ~radix:16 ~neg ~int:s1 ~frac:s2
                ~exp)
              ty
          in
          let t_concrete = Const (Float (Float_number (sign_str,exp_str,mant_str))) in
          (t, t_concrete)
        with
        (* cases for special float values *)
        | Float_MinusZero ->
          let t =
            t_const
              (Constant.real_const_from_string ~radix:10 ~neg:true ~int:"0"
                 ~frac:"0" ~exp:None)
              ty
          in
          (t, Const (Float Minus_zero))
        | Float_PlusZero ->
          let t =
            t_const
              (Constant.real_const_from_string ~radix:10 ~neg:false ~int:"0"
                 ~frac:"0" ~exp:None)
              ty
          in
          (t, Const (Float Plus_zero))
        | Float_NaN ->
            let is_nan_ls =
              try
                let th =
                  Env.read_theory env.why3_env [ "ieee_float" ] float_lib
                in
                Theory.ns_find_ls th.Theory.th_export [ "is_nan" ]
              with _ -> error "No lsymbol found in theory for is_nan@."
            in
            let x = create_vsymbol (Ident.id_fresh "x") ty in
            let f = t_app is_nan_ls [ t_var x ] None in
            (t_eps_close x f, Const (Float NaN))
        | Float_Infinity ->
            let is_infinite_ls =
              try
                let th =
                  Env.read_theory env.why3_env [ "ieee_float" ] float_lib
                in
                Theory.ns_find_ls th.Theory.th_export [ "is_infinite" ]
              with _ -> error "No lsymbol found in theory for is_infinite@."
            in
            let x = create_vsymbol (Ident.id_fresh "x") ty in
            let f = t_app is_infinite_ls [ t_var x ] None in
            (t_eps_close x f, Const (Float Infinity))
        | Float_Error ->
            error "Error while interpreting float constant %a@." print_constant
              c)
    | Cbool b ->
        (* boolean constants from SMT model are interpreted by default to Why3 terms
           (with type Some ty_bool) and not to formulas: later on in the functions
           apply_to_term and smt_term_to_term we convert Why3 terms to formulas using
           Term.to_prop when needed *)
        if b then (t_bool_true, concrete_const_bool true)
        else (t_bool_false, concrete_const_bool false)
    | Cstring str ->
      let t = t_const (Constant.string_const str) Ty.ty_str in
      let t_concrete = Const (String str) in
      (t, t_concrete)

  let find_builtin_lsymbol env n ts =
    let path, theory, ident =
      match ts with
      | [ t1; t2 ] -> (
          match (t1.t_ty, t2.t_ty) with
          | Some ty1, Some ty2
            when Ty.ty_equal ty1 Ty.ty_int && Ty.ty_equal ty2 Ty.ty_int -> (
              match n with
              | "+" -> ("int", "Int", Ident.op_infix "+")
              | "-" -> ("int", "Int", Ident.op_infix "-")
              | "*" -> ("int", "Int", Ident.op_infix "*")
              | "<" -> ("int", "Int", Ident.op_infix "<")
              | ">" -> ("int", "Int", Ident.op_infix ">")
              | "<=" -> ("int", "Int", Ident.op_infix "<=")
              | ">=" -> ("int", "Int", Ident.op_infix ">=")
              | _ -> raise NoBuiltinSymbol)
          | Some ty1, Some ty2
            when Ty.ty_equal ty1 Ty.ty_real && Ty.ty_equal ty2 Ty.ty_real -> (
              match n with
              | "+" -> ("real", "Real", Ident.op_infix "+")
              | "-" -> ("real", "Real", Ident.op_infix "-")
              | "*" -> ("real", "Real", Ident.op_infix "*")
              | "/" -> ("real", "Real", Ident.op_infix "/")
              | "<" -> ("real", "Real", Ident.op_infix "<")
              | ">" -> ("real", "Real", Ident.op_infix ">")
              | "<=" -> ("real", "Real", Ident.op_infix "<=")
              | ">=" -> ("real", "Real", Ident.op_infix ">=")
              | _ -> raise NoBuiltinSymbol)
          | _ -> raise NoBuiltinSymbol)
      | _ -> raise NoBuiltinSymbol
    in
    let th = Env.read_theory env.why3_env [ path ] theory in
    Theory.ns_find_ls th.Theory.th_export [ ident ]

  let rec term_to_term env t =
    match t with
    | Tconst c -> constant_to_term env c
    | Tvar qid -> (
        try qual_id_to_term env qid
        with NoArgConstructor -> apply_to_term env qid [])
    | Tite (b, t1, t2) ->
        let b', b'_concrete = term_to_term env b in
        let t1', t1'_concrete = term_to_term env t1 in
        let t2', t2'_concrete = term_to_term env t2 in
        (t_if b' t1' t2', If (b'_concrete, t1'_concrete, t2'_concrete))
    | Tapply (qid, ts) -> apply_to_term env qid ts
    | Tarray (s1, s2, a) -> array_to_term env s1 s2 a
    | Tunparsed _ -> error "Could not interpret term %a@." print_term t

  and apply_to_term env qid ts =
    match (qid, ts) with
    | Qident (Isymbol (S "=")), [ t1; t2 ] ->
        let t1', t1'_concrete = term_to_term env t1 in
        let t2', t2'_concrete = term_to_term env t2 in
        (t_equ t1' t2', concrete_apply_equ t1'_concrete t2'_concrete)
    | Qident (Isymbol (S "or")), hd :: tl ->
        let (hd,hd_concrete) = term_to_term env hd in
        List.fold_left
          (fun (t,t_concrete) t' ->
            let (t',t'_concrete) = term_to_term env t' in
            ( t_binary Term.Tor t (Term.to_prop t'),
              Binop (Or, t_concrete, t'_concrete) ))
          (Term.to_prop hd, hd_concrete)
          tl
    | Qident (Isymbol (S "and")), hd :: tl ->
        let (hd,hd_concrete) = term_to_term env hd in
        List.fold_left
          (fun (t,t_concrete) t' ->
            let (t',t'_concrete) = term_to_term env t' in
            ( t_binary Term.Tand t (Term.to_prop t'),
              Binop (And, t_concrete, t'_concrete) ))
          (Term.to_prop hd, hd_concrete)
          tl
    | Qident (Isymbol (S "not")), [ t ] ->
        let (t,t_concrete) = term_to_term env t in
        (t_not (Term.to_prop t), Not t_concrete)
    | Qident (Isymbol (S n)), ts | Qident (Isymbol (Sprover n)), ts -> (
        let ts', ts'_concrete = List.split (List.map (term_to_term env) ts) in
        try
          (* we first search if [n] is the name of a function defined
             elsewhere in the SMT model *)
          let t, t_concrete = Mstr.find n env.prover_fun_defs in
          let vs_args, _, t' = t_open_lambda t in
          let subst = Mvs.of_list (List.combine vs_args ts') in
          begin match t_concrete with
          | Function (_, args_concrete, t'_concrete) ->
            let subst_concrete = Mstr.of_list (List.combine args_concrete ts'_concrete) in
            (t_subst subst t', subst_concrete_term subst_concrete t'_concrete)
          | _ -> 
            Debug.dprintf debug "t_concrete = %a@."
              print_concrete_term t_concrete;
            error "TODO_WIP (apply_to_term #1)"
          end
        with _ -> (
          (* if it fails, we search for [n] in constructors and in builtin symbols *)
          let ls =
            try Mstr.find n env.constructors
            with _ -> (
              try find_builtin_lsymbol env n ts'
              with NoBuiltinSymbol ->
                (* no sort is associated to Qident, so we cannot infer the type of the
                   lsymbol to create and fails instead *)
                error "No lsymbol found for qualified identifier %a@."
                  print_qualified_identifier qid)
          in
          try (t_app ls ts' ls.ls_value,  concrete_apply_from_ls ls ts'_concrete)
          with _ ->
            error "Cannot apply lsymbol %a to terms (%a)@." Pretty.print_ls ls
              (Pp.print_list Pp.comma Pretty.print_term)
              ts'))
    | Qannotident (Isymbol (S n), s), ts
    | Qannotident (Isymbol (Sprover n), s), ts -> (
        let ts', ts'_concrete = List.split (List.map (term_to_term env) ts) in
        try
          (* we first search if [n] is the name of a function defined
             elsewhere in the SMT model *)
          let t, t_concrete = Mstr.find n env.prover_fun_defs in
          let vs_args, _, t' = t_open_lambda t in
          let subst = Mvs.of_list (List.combine vs_args ts') in
          begin match t_concrete with
          | Function (_, args_concrete, t'_concrete) ->
            let subst_concrete = Mstr.of_list (List.combine args_concrete ts'_concrete) in
            (t_subst subst t', subst_concrete_term subst_concrete t'_concrete)
          | _ ->
            Debug.dprintf debug "t_concrete = %a@."
              print_concrete_term t_concrete;
            error "TODO_WIP (apply_to_term #2)"
          end
        with _ -> (
          (* if it fails, we search for [n] in constructors and in builtin symbols *)
          let ls =
            try Mstr.find n env.constructors
            with _ -> (
              try find_builtin_lsymbol env n ts'
              with NoBuiltinSymbol ->
                let ts'_ty =
                  try List.map (fun t -> Opt.get t.t_ty) ts'
                  with _ ->
                    error "Arguments of %a should have a type@."
                      print_qualified_identifier qid
                in
                (* for Qannotident, we can infer the type and create a fresh lsymbol *)
                create_lsymbol (Ident.id_fresh n) ts'_ty
                  (Some (smt_sort_to_ty env s)))
          in
          try (t_app ls ts' ls.ls_value, concrete_apply_from_ls ls ts'_concrete)
          with _ ->
            error "Cannot apply lsymbol %a to terms (%a)@." Pretty.print_ls ls
              (Pp.print_list Pp.comma Pretty.print_term)
              ts'))
    | _ -> error "Could not interpret %a@." print_qualified_identifier qid

  and array_to_term env s1 s2 elts =
    (* arrays are translated using a function of type [ty1] -> [ty2] *)
    let ty1 = smt_sort_to_ty env s1 in
    let ty2 = smt_sort_to_ty env s2 in
    let vs_arg = create_vsymbol (Ident.id_fresh "x") ty1 in
    let vs_name = Format.asprintf "@[<h>%a@]" Pretty.print_vs_qualified vs_arg in
    let mk_case key value (t, t_concrete) =
      let key,key_concrete = term_to_term env key in
      let value,value_concrete = term_to_term env value in
      if Ty.oty_equal key.t_ty (Some ty1) && Ty.oty_equal value.t_ty (Some ty2)
      then
        ( t_if (t_equ (t_var vs_arg) key) value t,
          If ((concrete_apply_equ (Var vs_name) key_concrete), value_concrete, t_concrete) )
      else
        error
          "Type %a for sort %a of array keys and/or type %a for sort %a of \
           array values do not match@."
          (Pp.print_option_or_default "None" Pretty.print_ty)
          key.t_ty print_sort s1
          (Pp.print_option_or_default "None" Pretty.print_ty)
          value.t_ty print_sort s2
    in
    let t_others, others_concrete = term_to_term env elts.array_others in
    let a, a_concrete =
      List.fold_left
        (fun acc (key, value) -> mk_case key value acc)
        (t_others, others_concrete)
        elts.array_indices
    in
    (t_lambda [ vs_arg ] [] a, Function (true, [vs_name], a_concrete))

  let smt_term_to_term ~fmla env t s =
    Debug.dprintf debug "[smt_term_to_term] t = %a@." print_term t;
    let ty_s = smt_sort_to_ty env s in
    let ty_s =
      if Ty.ty_equal ty_s Ty.ty_bool then if fmla then None else Some Ty.ty_bool
      else Some ty_s
    in
    Debug.dprintf debug
      "[smt_term_to_term] interpreted type for sort %a is %a (fmla=%b)@."
      print_sort s
      (Pp.print_option_or_default "None" Pretty.print_ty_qualified)
      ty_s fmla;
    let (t', t'_concrete) = term_to_term env t in
    let t' = if fmla then Term.to_prop t' else t' in
    if Opt.equal Ty.ty_equal ty_s t'.t_ty then (
      Debug.dprintf debug "[smt_term_to_term] t' = %a, t'.t_ty = %a, t'_concrete = %a@."
        Pretty.print_term t'
        (Pp.print_option_or_default "None" Pretty.print_ty_qualified)
        t'.t_ty
        print_concrete_term t'_concrete;
      (t', t'_concrete))
    else
      error "Type %a for sort %a and type %a for term %a do not match@."
        (Pp.print_option_or_default "None" Pretty.print_ty)
        ty_s print_sort s
        (Pp.print_option_or_default "None" Pretty.print_ty)
        t'.t_ty print_term t

  (* Check that the definiton of a function in the SMT model matches the type
     of the corresponding lsymbol in [env.queried_terms]. *)
  let check_fun_def_type env ls (args, res, body) =
    Debug.dprintf debug "-----------------------------@.";
    Debug.dprintf debug "[check_fun_def_type] fun_def = %a@." print_function_def
      (args, res, body);
    Debug.dprintf debug "[check_fun_def_type] ls = %a@." Pretty.print_ls ls;
    Debug.dprintf debug "[check_fun_def_type] ls.ls_value = %a@."
      (Pp.print_option_or_default "None" Pretty.print_ty_qualified)
      ls.ls_value;
    List.iter
      (Debug.dprintf debug "[check_fun_def_type] ls.ls_args = %a@."
         Pretty.print_ty_qualified)
      ls.ls_args;
    let check_or_update_inferred_types s ty =
      Ty.ty_equal ty (smt_sort_to_ty ~update_ty:(Some ty) env s)
    in
    try
      let ls_value =
        match ls.ls_value with None -> Ty.ty_bool | Some ty -> ty
      in
      if
        check_or_update_inferred_types res ls_value
        && List.fold_left2
             (fun acc (_, arg) ls_arg ->
               acc && check_or_update_inferred_types arg ls_arg)
             true args ls.ls_args
      then ()
      else
        error "Type mismatch when interpreting %a with lsymbol %a@."
          print_function_def (args, res, body) Pretty.print_ls ls
    with Invalid_argument _ ->
      error "Function arity mismatch when interpreting %a with lsymbol %a@."
        print_function_def (args, res, body) Pretty.print_ls ls

  (* Interpretation of function definitons in the model to terms. *)
  let interpret_fun_def_to_term ~fmla env (args, res, body) =
    Debug.dprintf debug "-----------------------------@.";
    Debug.dprintf debug "[interpret_fun_def_to_term] fun_def = %a@."
      print_function_def (args, res, body);
    env.bound_vars <- Mstr.empty;
    List.iter
      (fun (symbol, sort) ->
        match symbol with
        | S str | Sprover str ->
            let fresh_str = Ident.id_fresh str in
            let vs = create_vsymbol fresh_str (smt_sort_to_ty env sort) in
            env.bound_vars <- Mstr.add str vs env.bound_vars)
      args;
    Mstr.iter
      (fun key vs ->
        Debug.dprintf debug "[interpret_fun_def_to_term] bound_var = (%s, %a)@."
          key Pretty.print_vs vs)
      env.bound_vars;
    let (t_body, t_body_concrete) = smt_term_to_term ~fmla env body res in
    let t =
      t_lambda
        (Mstr.values env.bound_vars)
        []
        t_body
    in
    let t_concrete =
      if List.length (Mstr.values env.bound_vars) = 0 then
        t_body_concrete
      else
        let args =
          List.map
            (fun vs -> Format.asprintf "@[<h>%a@]" Pretty.print_vs_qualified vs)
            (Mstr.values env.bound_vars)
        in
        Function (false,args,t_body_concrete) (* TODO_WIP *)
    in
    Debug.dprintf debug "[interpret_fun_def_to_term] t = %a@."
      Pretty.print_term t;
    Debug.dprintf debug "[interpret_fun_def_to_term] t_concrete = %a@."
      print_concrete_term t_concrete;
    Debug.dprintf debug "-----------------------------@.";
    t, t_concrete

  let is_vs_in_prover_vars vs prover_vars =
    List.exists
      (fun mvs ->
        Ty.Mty.exists
          (fun ty vs' -> Ty.ty_equal ty vs.vs_ty && Term.vs_equal vs' vs)
          mvs)
      (Mstr.values prover_vars)

  let is_true env t =
    match t.t_node with
    | Term.Tapp (ls, [ t1; t2 ]) when ls_equal ls ps_equ -> (
        match (t1.t_node, t2.t_node) with
        | Term.Tvar v1, Term.Tvar v2
          when is_vs_in_prover_vars v1 env.prover_vars
               && is_vs_in_prover_vars v2 env.prover_vars ->
            (* distinct prover variables are not equal *)
            vs_equal v1 v2
        | _ -> false)
    | Ttrue -> true
    | _ -> t_equal t t_bool_true

  let is_false env t =
    match t.t_node with
    | Term.Tapp (ls, [ t1; t2 ]) when ls_equal ls ps_equ -> (
        match (t1.t_node, t2.t_node) with
        | Term.Tvar v1, Term.Tvar v2
          when is_vs_in_prover_vars v1 env.prover_vars
               && is_vs_in_prover_vars v2 env.prover_vars ->
            (* distinct prover variables are not equal *)
            not (vs_equal v1 v2)
        | _ -> false)
    | Tfalse -> true
    | _ -> t_equal t t_bool_false

  (* EVALUATION OF TERMS *)
  (* Terms interpreted from the SMT model may contain prover variables,
     which can be evaluated using type coercions or fields for record types.
     The goal is to evaluate a term [t] by replacing prover variables with an epsilon term.
     We also perform some trivial evaluation by simplifying if then else terms when
     the condition can be evaluated to true/false, etc. *)

  (* [eval_prover_var] is set to false when we create the epsilon term (which
     may contain other prover variables)
     [seen_prover_vars] records already seen prover variables when evaluating
     a term to avoid unbounded recursion *)
  let rec eval_term env ?(eval_prover_var = true) seen_prover_vars terms (t, t_concrete) =
    match t.t_node, t_concrete with
    | Term.Tvar vs, _ -> (
        match Mvs.find_opt vs env.eval_prover_vars with
        | Some t_vs ->
            (* vs is a prover variable *)
            if eval_prover_var then
              if List.mem vs seen_prover_vars then t_vs
              else
                eval_term env ~eval_prover_var (vs :: seen_prover_vars) terms t_vs
            else (t, t_concrete)
        | None -> (t, t_concrete) (* vs is not a prover variable *))
    | Term.Tapp (ls, [ t1; t2 ]), Apply (concrete_equ, [t1_concrete; t2_concrete])
          when ls_equal ls ps_equ -> (
        match (t1.t_node, t2.t_node) with
        | Term.Tvar v1, Term.Tvar v2
          when is_vs_in_prover_vars v1 env.prover_vars
               && is_vs_in_prover_vars v2 env.prover_vars ->
            (* distinct prover variables are not equal *)
            if vs_equal v1 v2 then (t_true, concrete_const_bool true)
            else (t_false, concrete_const_bool false)
        | _ ->
            (* general case *)
            let (t1', t1'_concrete) =
              eval_term env ~eval_prover_var seen_prover_vars terms (t1, t1_concrete)
            in
            let (t2', t2'_concrete) =
              eval_term env ~eval_prover_var seen_prover_vars terms (t2, t2_concrete)
            in
            if t_equal t1' t2' then (t_true, concrete_const_bool true)
            else
              ( t_app ls [ t1'; t2' ] ls.ls_value),
                concrete_apply_equ t1'_concrete t2'_concrete )
    | Term.Tapp (ls, ts), Apply (ls_name, ts_concrete) ->
        begin try
          let ts' = List.combine ts ts_concrete in
          let ts, ts_concrete = List.split (
            List.map
              (fun x -> eval_term env ~eval_prover_var seen_prover_vars terms x) ts')
          in
          (t_app ls ts ls.ls_value, Apply (ls_name, ts_concrete))
        with _ -> error "TODO_WIP (eval_term Tapp)"
        end
    | Term.Tif (b, t1, t2), If (b_concrete, t1_concrete, t2_concrete) ->
        let b', b'_concrete =
          eval_term env ~eval_prover_var seen_prover_vars terms (b,b_concrete) in
        if is_true env b' then
          eval_term env ~eval_prover_var seen_prover_vars terms (t1,t1_concrete)
        else if is_false env b' then
          eval_term env ~eval_prover_var seen_prover_vars terms (t2,t2_concrete)
        else
          let t1',t1'_concrete =
            eval_term env ~eval_prover_var seen_prover_vars terms (t1,t1_concrete) in
          let t2',t2'_concrete =
            eval_term env ~eval_prover_var seen_prover_vars terms (t2,t2_concrete) in
          (t_if b' t1' t2', If (b'_concrete, t1'_concrete, t2'_concrete))
    | Term.Teps tb, _ -> (
        match Term.t_open_lambda t with
        | [], _, _ ->
          begin match t_concrete with
          | Epsilon (eps_x, eps_term) ->
            let vs, t' = Term.t_open_bound tb in
            let t'_eval, t'_eval_concrete =
              eval_term env ~eval_prover_var seen_prover_vars terms (t',eps_term) in
            (t_eps_close vs t'_eval, Epsilon (eps_x, t'_eval_concrete))
          | Const (Float _) -> (t,t_concrete)
          | _ ->
            Debug.dprintf debug "t_concrete = %a@."
              print_concrete_term t_concrete;
            error "TODO_WIP (eval_term Teps Epsilon)"
          end
        | vsl, trig, t' ->
            let is_array, vsl_concrete, t'_concrete = match t_concrete with
              | Function (is_array, args, body) -> is_array, args, body
              | _ ->
                Debug.dprintf debug "t_concrete = %a@."
                  print_concrete_term t_concrete;
                error "TODO_WIP (eval_term Teps Function)"
            in
            let t'_eval, t'_eval_concrete =
              eval_term env ~eval_prover_var seen_prover_vars terms (t',t'_concrete) in
            (t_lambda vsl trig t'_eval, Function (is_array, vsl_concrete, t'_eval_concrete)))
    | Term.Tquant (q, tq), Quant (q_concrete, vars_concrete, t_concrete) ->
        let vsl, trig, t' = t_open_quant tq in
        let t',t'_concrete =
          eval_term env ~eval_prover_var seen_prover_vars terms (t',t_concrete) in
        ( t_quant q (t_close_quant vsl trig t'),
          Quant (q_concrete, vars_concrete, t'_concrete) )
    | Term.Tbinop (Term.Tor, t1, t2), Binop (Or, t1_concrete, t2_concrete) ->
        let t1,t1_concrete =
          eval_term env ~eval_prover_var seen_prover_vars terms (t1,t1_concrete) in
        let t2,t2_concrete =
          eval_term env ~eval_prover_var seen_prover_vars terms (t2,t2_concrete) in
        if is_true env t1 || is_true env t2 then
          (t_true, concrete_const_bool true)
        else if is_false env t1 || is_false env t2 then
          (t_false, concrete_const_bool false)
        else
          (t_binary Term.Tor t1 t2, Binop (Or, t1_concrete, t2_concrete))
    | Term.Tbinop (Term.Tand, t1, t2), Binop (And, t1_concrete, t2_concrete) ->
        let t1,t1_concrete =
          eval_term env ~eval_prover_var seen_prover_vars terms (t1,t1_concrete) in
        let t2,t2_concrete =
          eval_term env ~eval_prover_var seen_prover_vars terms (t2,t2_concrete) in
        if is_true env t1 && is_true env t2 then
          (t_true, concrete_const_bool true)
        else if is_false env t1 && is_false env t2 then
          (t_true, concrete_const_bool true)
        else if is_true env t1 && is_false env t2 then
          (t_false, concrete_const_bool false)
        else if is_false env t1 && is_true env t2 then
          (t_false, concrete_const_bool false)
        else
          (t_binary Term.Tand t1 t2, Binop (And, t1_concrete, t2_concrete))
    | Term.Tbinop (op, t1, t2), Binop (op_concrete, t1_concrete, t2_concrete) ->
        let t1,t1_concrete =
          eval_term env ~eval_prover_var seen_prover_vars terms (t1,t1_concrete) in
        let t2,t2_concrete =
          eval_term env ~eval_prover_var seen_prover_vars terms (t2,t2_concrete) in
        (t_binary op t1 t2, Binop (op_concrete, t1_concrete, t2_concrete))
    | Term.Tnot t', Not t'_concrete ->
        let t',t'_concrete =
          eval_term env ~eval_prover_var seen_prover_vars terms (t',t'_concrete) in
        if is_true env t' then (t_false, concrete_const_bool false)
        else if is_false env t' then (t_true, concrete_const_bool true)
        else (t_not t', Not t'_concrete)
    | _ -> (t, t_concrete)

  let eval (pinfo : Printer.printing_info) env terms =
    let ty_coercions =
      Ty.Mty.map (* for each set [sls] of lsymbols associated to a type *)
        (fun sls ->
          (* we construct a list of elements [(str,(ls,t))] retrieved
             from [terms] such that [ls] is in [sls]:
             for a given type [ty], it corresponds to all type coercions
             that can be applied to an object of type [ty] *)
          List.concat
            (List.map
               (fun ls ->
                 Mstr.bindings
                   (Mstr.mapi_filter
                      (fun _ ((ls', _, _), (t, t_concrete)) ->
                        if ls_equal ls ls' then Some (ls, t, t_concrete) else None)
                      terms))
               (Sls.elements sls)))
        pinfo.Printer.type_coercions
    in
    Ty.Mty.iter
      (fun key elt ->
        List.iter
          (fun (str, (ls, t, t_concrete)) ->
            Debug.dprintf debug
              "[ty_coercions] ty = %a, str=%s, ls = %a, t=%a, t_concrete=%a@." Pretty.print_ty
              key str Pretty.print_ls ls Pretty.print_term t print_concrete_term t_concrete)
          elt)
      ty_coercions;
    let ty_fields =
      Ty.Mty.map (* for each list of lsymbols associated to a type *)
        (fun lls ->
          (* we construct a list of elements [(str,(ls,t))] retrieved
              from [terms] such that [ls] is in [lls]:
              for a given type [ty], it corresponds to all fields
              that should be used to construct a record object
              from an object of type [ty] *)
          List.concat
            (List.map
               (fun ls ->
                 Mstr.bindings
                   (Mstr.mapi_filter
                      (fun _ ((ls', _, _), (t, t_concrete)) ->
                        if ls_equal ls ls' then Some (ls, t, t_concrete) else None)
                      terms))
               lls))
        pinfo.Printer.type_fields
    in
    Ty.Mty.iter
      (fun key elt ->
        List.iter
          (fun (str, (ls, t, t_concrete)) ->
            Debug.dprintf debug "[ty_fields] ty = %a, str=%s, ls = %a, t=%a, t_concrete=%a@."
              Pretty.print_ty key str Pretty.print_ls ls Pretty.print_term t print_concrete_term t_concrete)
          elt)
      ty_fields;
    (* for each prover variable, we create an epsilon term using type coercions
       or type fields for the type of the prover variable *)
    Mstr.iter
      (fun key value ->
        Ty.Mty.iter
          (fun ty vs ->
            let vs_name = Format.asprintf "@[<h>%a@]" Pretty.print_vs_qualified vs in
            let create_epsilon_term ty l =
              (* create a fresh vsymbol for the variable bound by the epsilon term *)
              let x = create_vsymbol (Ident.id_fresh "x") ty in
              let x_name = Format.asprintf "@[<h>%a@]" Pretty.print_vs_qualified x in
              let aux (_, (ls', t', t'_concrete)) =
                let vs_list', _, t' = t_open_lambda t' in
                match t'_concrete with
                | Function (_, args_concrete, t'_concrete) ->
                  let vs', vs'_concrete_name =
                    match vs_list', args_concrete with
                    | [ vs' ], [ vs_name ] -> vs', vs_name
                    | _ ->
                        error
                          "Only one variable expected when opening lambda-term %a"
                          Pretty.print_term t'
                  in
                  let (t', t'_concrete) =
                    eval_term env ~eval_prover_var:false [] terms
                      ( (t_subst_single vs' (t_var vs) t'),
                        (subst_concrete_term (Mstr.of_list [(vs'_concrete_name, Var vs_name)]) t'_concrete) )
                  in
                  (* substitute [vs] by this new variable in the body [t'] of the function
                      defining the type coercion *)
                  let t' = t_subst_single vs' (t_var x) t' in
                  let t'_concrete = subst_concrete_term (Mstr.of_list [(vs'_concrete_name, Var x_name)]) t'_concrete in
                  let ls'_name = Format.asprintf "@[<h>%a@]" Pretty.print_ls_qualified ls' in
                  (* construct the formula to be used in the epsilon term *)
                  ( t_equ (t_app ls' [ t_var x ] ls'.ls_value) t',
                    concrete_apply_equ (Apply (ls'_name, [ Var x_name ])) t'_concrete )
                | _ ->
                  Debug.dprintf debug "t'_concrete = %a@."
                    print_concrete_term t'_concrete;
                  error "TODO_WIP (eval)"
              in
              let l', l'_concrete = List.split (List.map aux l) in
              let f = t_and_l l' in
              let f_concrete = t_and_l_concrete l'_concrete in
              (* replace [t] by [eps x. f] *)
              (t_eps_close x f, Epsilon (x_name, f_concrete))
            in
            let (eval_var, eval_var_concrete) =
              (* first search if [ty] is associated to some fields *)
              match Ty.Mty.find_def [] ty ty_fields with
              | [] -> (
                  (* if no fields, search if there exists some type coercions for [ty] *)
                  match Ty.Mty.find_def [] ty ty_coercions with
                  | [] ->
                    (t_var vs, Var vs_name)
                  | coercions -> create_epsilon_term ty coercions)
              | fields -> create_epsilon_term ty fields
            in
            Debug.dprintf debug
              "[eval] prover_var = %s, vs = %a, eval_var = %a, eval_var_concrete = %a@."
              key
              Pretty.print_term (t_var vs)
              Pretty.print_term eval_var
              print_concrete_term eval_var_concrete;
            env.eval_prover_vars <-
              Mvs.add vs (eval_var, eval_var_concrete) env.eval_prover_vars)
          value)
      env.prover_vars;
    Mstr.mapi
      (fun _ ((ls, oloc, attrs), (t, t_concrete)) ->
        let (t', t'_concrete) = eval_term env [] terms (t, t_concrete) in
        Debug.dprintf debug "[eval] t = %a ==> t' = %a@." Pretty.print_term t
          Pretty.print_term t';
        ((ls, oloc, attrs), (t', t'_concrete)))
      terms

  let rec maybe_convert_epsilon_terms env (t, t_concrete) =
    match t.t_node, t_concrete with
    | Term.Tapp (ls, ts), Apply (ls_name, ts_concrete) ->
        begin try
          let ts' = List.combine ts ts_concrete in
          let ts, ts_concrete =
            List.split (List.map (maybe_convert_epsilon_terms env ) ts')
          in
          (t_app ls ts ls.ls_value, Apply (ls_name, ts_concrete))
        with _ -> error "TODO_WIP (maybe_convert_epsilon_terms Tapp)"
        end
    | Term.Tif (b, t1, t2), If (b_concrete, t1_concrete, t2_concrete) ->
        let b', b'_concrete = maybe_convert_epsilon_terms env (b,b_concrete) in
        let t1',t1'_concrete = maybe_convert_epsilon_terms env (t1,t1_concrete) in
        let t2',t2'_concrete = maybe_convert_epsilon_terms env (t2,t2_concrete) in
        (t_if b' t1' t2', If (b'_concrete, t1'_concrete, t2'_concrete))
    | Term.Teps tb, _ -> (
        match Term.t_open_lambda t with
        | [], _, _ ->
            begin match t_concrete with
            | Epsilon (eps_x, eps_term) ->
              let vs, t' = Term.t_open_bound tb in
              begin match get_opt_record env (vs,eps_x) (t',eps_term) with
              | None ->
                begin match get_opt_int_range (vs,eps_x) (t',eps_term) with
                | None ->
                  let t', t'_concrete = maybe_convert_epsilon_terms env (t',eps_term) in
                  (t_eps_close vs t', Epsilon (eps_x, t'_concrete))
                | Some int_proj ->
                  (t_eps_close vs t', Const (Integer int_proj))
                end
              | Some fields_values -> (t_eps_close vs t', Record fields_values)
              end
            | Const (Float _) -> (t,t_concrete)
            | _ ->
              Debug.dprintf debug "t_concrete = %a@."
                print_concrete_term t_concrete;
              error "TODO_WIP (maybe_convert_epsilon_terms Teps Epsilon)"
            end
        | vsl, trig, t' ->
            let is_array, vsl_concrete, t'_concrete = match t_concrete with
              | Function (is_array, args, body) -> is_array, args, body
              | _ ->
                Debug.dprintf debug "t_concrete = %a@."
                  print_concrete_term t_concrete;
                error "TODO_WIP (maybe_convert_epsilon_terms Teps Function)"
            in
            let t', t'_concrete = maybe_convert_epsilon_terms env (t',t'_concrete) in
            (t_lambda vsl trig t', Function (is_array, vsl_concrete, t'_concrete)))
    | Term.Tquant (q, tq), Quant (q_concrete, vars_concrete, t_concrete) ->
        let vsl, trig, t' = t_open_quant tq in
        let t',t'_concrete = maybe_convert_epsilon_terms env (t',t_concrete) in
        ( t_quant q (t_close_quant vsl trig t'),
          Quant (q_concrete, vars_concrete, t'_concrete) )
    | Term.Tbinop (op, t1, t2), Binop (op_concrete, t1_concrete, t2_concrete) ->
        let t1,t1_concrete =
          maybe_convert_epsilon_terms env (t1,t1_concrete) in
        let t2,t2_concrete =
          maybe_convert_epsilon_terms env (t2,t2_concrete) in
        (t_binary op t1 t2, Binop (op_concrete, t1_concrete, t2_concrete))
    | Term.Tnot t', Not t'_concrete ->
        let t',t'_concrete =
          maybe_convert_epsilon_terms env (t',t'_concrete) in
        (t_not t', Not t'_concrete)
    | _ -> (t, t_concrete)

  and get_opt_record env (vs,vs_name) (t',t'_concrete) =
    (* check if t is of the form epsilon x:ty. x.f1 = v1 /\ ... /\ x.fn = vn
    with f1,...,fn the fields associated to type ity *)
    let exception UnexpectedPattern in
    let rec get_conjuncts (t',t'_concrete) =
      match t'.t_node, t'_concrete with
      | Tbinop (Tand, t1, t2), Binop (And, ct1, ct2) ->
        (t1,ct1) :: (get_conjuncts (t2,ct2))
      | _ -> [(t',t'_concrete)]
    in
    try
      let expected_fields =
        try Ty.Mty.find (vs.vs_ty) env.type_fields
        with _ -> raise UnexpectedPattern
      in
      let list_of_fields_values =
        List.fold_left
          (fun acc (t,ct) ->
            match t.t_node, ct with
            | Tapp (ls, [proj;term_value]), Apply (concrete_equ, [cproj;cterm_value])
                when ls_equal ls ps_equ -> (
              match proj.t_node, cproj with
              | Tapp (ls, [x]), Apply (ls_name, [Var vs_name]) when t_equal x (t_var vs) ->
                if List.mem ls expected_fields then
                  let term_value', cterm_value' =
                    maybe_convert_epsilon_terms env (term_value,cterm_value) in
                  ((ls,ls_name),(term_value',cterm_value')) :: acc
                else raise UnexpectedPattern
              | _ -> raise UnexpectedPattern
            )
            | _ -> raise UnexpectedPattern
          )
          []
          (get_conjuncts (t',t'_concrete))
      in
      if List.length expected_fields = List.length list_of_fields_values then
        Some (List.map
          (fun ((ls,ls_name),(t,ct)) -> (ls_name,ct))
          list_of_fields_values)
      else
        raise UnexpectedPattern
    with UnexpectedPattern -> None
  
  and get_opt_int_range (vs,vs_name) (t',t'_concrete) =
  (* special case for range types:
     if t is of the form epsilon x:ty. ty'int x = v, check that v is in the
     range of values defined by type ty *)
    let exception UnexpectedPattern in
    try
      let ((proj_ls,proj_ls_name), (proj_v,c_proj_v)) =
        match t'.t_node, t'_concrete with
        | Tapp (ls, [proj;term_value]), Apply (concrete_equ, [cproj;cterm_value])
            when ls_equal ls ps_equ -> (
          match proj.t_node, cproj with
          | Tapp (ls, [x]), Apply (ls_name, [Var vs_name]) when t_equal x (t_var vs) ->
            ((ls,ls_name),(term_value,cterm_value))
          | _ -> raise UnexpectedPattern
        )
        | _ -> raise UnexpectedPattern
      in
      Debug.dprintf debug "[get_opt_int_range] vs.vs_ty = %a@."
        Pretty.print_ty vs.vs_ty;
      match vs.vs_ty.ty_node with
      | Tyapp (ts,_) ->
        begin match ts.ts_def, proj_v.t_node with
        | Ty.Range r, Tconst (Constant.ConstInt c)
          (* when proj_ls.ls_name.id_string = ts.Ty.ts_name.id_string ^ "'int"
            && Opt.equal Ty.ty_equal proj_ls.ls_value (Some Ty.ty_int) *) ->
          Some (BigInt.to_string c.il_int)
        | _ -> raise UnexpectedPattern
        end
      | _ -> raise UnexpectedPattern
    with UnexpectedPattern -> None

  (* If some prover variables remain after evaluation, we remove the terms
     containing those prover variables. *)
  let clean env terms =
    Mstr.map_filter
      (fun ((ls, oloc, attr), (t, t_concrete)) ->
        if Term.t_v_any (fun vs -> is_vs_in_prover_vars vs env.prover_vars) t
        then None
        else
          let (t, t_concrete) = maybe_convert_epsilon_terms env (t, t_concrete) in
          Some ((ls, oloc, attr), (t, t_concrete)))
      terms

  let get_terms (pinfo : Printer.printing_info)
      (fun_defs : Smtv2_model_defs.function_def Mstr.t) =
    let qterms = pinfo.Printer.queried_terms in
    Mstr.iter
      (fun key _ -> Debug.dprintf debug "[fun_defs] name = %s@." key)
      fun_defs;
    Mstr.iter
      (fun key (ls, _, _) ->
        Debug.dprintf debug "[queried_terms] name = %s, ls = %a@." key
          Pretty.print_ls ls)
      qterms;
    Mstr.iter
      (fun key ls ->
        Debug.dprintf debug "[constructors] name = %s, ls = %a/%d@." key
          Pretty.print_ls ls (List.length ls.ls_args))
      pinfo.Printer.constructors;
    let env =
      {
        why3_env = pinfo.Printer.why3_env;
        prover_vars = Mstr.empty;
        bound_vars = Mstr.empty;
        constructors = pinfo.Printer.constructors;
        type_fields = pinfo.Printer.type_fields;
        inferred_types = [];
        queried_terms = Mstr.map (fun (ls, _, _) -> ls) qterms;
        eval_prover_vars = Mvs.empty;
        prover_fun_defs = Mstr.empty;
      }
    in
    let queried_fun_defs, prover_fun_defs =
      Mstr.partition (fun n _ -> Mstr.mem n qterms) fun_defs
    in
    let queried_fun_defs =
      Mstr.mapi_filter
        (fun n def ->
          match Mstr.find n qterms with
          | ls, _, _ -> (
              try
                check_fun_def_type env ls def;
                Some def
              with
              | E str ->
                  Debug.dprintf debug "Error while interpreting %s: %s@." n str;
                  None
              | _ ->
                  Debug.dprintf debug "Error while interpreting %s@." n;
                  None)
          | exception Not_found -> None)
        queried_fun_defs
    in
    Mstr.iter
      (fun n def ->
        match Mstr.find n qterms with
        | _, _, _ -> ()
        | exception Not_found -> (
            try
              Debug.dprintf debug
                "No term for %s, adding term to env.prover_fun_defs@." n;
              let (t,t_concrete) = interpret_fun_def_to_term ~fmla:false env def in
              env.prover_fun_defs <- Mstr.add n (t,t_concrete) env.prover_fun_defs
            with
            | E str ->
                Debug.dprintf debug "Error while interpreting %s: %s@." n str
            | _ -> Debug.dprintf debug "Error while interpreting %s@." n))
      prover_fun_defs;
    let terms =
      Mstr.mapi_filter
        (fun n def ->
          match Mstr.find n qterms with
          | ls, oloc, attrs -> (
              try
                (* fmla = true if the interpreted term should be a formula (with type = None)
                   and not a term (with type = Some ty) *)
                let fmla = not (Opt.inhabited ls.ls_value) in
                let (t, t_concrete) = interpret_fun_def_to_term ~fmla env def in
                Some ((ls, oloc, attrs), (t, t_concrete))
              with
              | E str ->
                  Debug.dprintf debug "Error while interpreting %s: %s@." n str;
                  None
              | _ ->
                  Debug.dprintf debug "Error while interpreting %s@." n;
                  None)
          | exception Not_found -> None)
        queried_fun_defs
    in
    let debug_terms desc terms =
      Mstr.iter
        (fun n ((ls, oloc, _), (t, t_concrete)) ->
          Debug.dprintf debug
            "[TERMS %s] name = %s, ls = %a, oloc = %a, t = %a, t_concrete = %a@." desc n
            Pretty.print_ls ls
            (Pp.print_option Pretty.print_loc_as_attribute) oloc
            Pretty.print_term t
            print_concrete_term t_concrete)
        terms
    in
    debug_terms "FROM SMT MODEL" terms;
    let terms = eval pinfo env terms in
    debug_terms "AFTER EVALUATION" terms;
    let terms = clean env terms in
    debug_terms "AFTER CLEANUP" terms;
    terms
end

(*
**********************************************************************
**  Registering model parser
**********************************************************************
*)

let () =
  Exn_printer.register (fun fmt exn ->
      match exn with
      | FromStringToSexp.E msg ->
          Format.fprintf fmt
            "Error@ while@ parsing@ SMT@ model@ from@ string@ to@ \
             S-expression:@ %s"
            msg
      | FromSexpToModel.E (sexp, s) ->
          Format.fprintf fmt
            "Error@ while@ parsing@ SMT@ model@ from@ S-expression@ to@ model@ \
             definition:@ cannot@ read@ the@ following@ S-expression@ as@ %s:@ \
             %a"
            s FromSexpToModel.pp_sexp sexp
      | FromModelToTerm.E msg ->
          Format.fprintf fmt
            "Error@ while@ parsing@ SMT@ model@ from@ model@ definition@ to@ \
             term:@ %s"
            msg
      | _ -> raise exn)

let get_model_string input =
  let nr = Re.Str.regexp "^)+" in
  let res = Re.Str.search_backward nr input (String.length input) in
  String.sub input 0 (res + String.length (Re.Str.matched_string input))

let parse pinfo input =
  match get_model_string input with
  | exception Not_found -> []
  | model_string ->
      let sexps = FromStringToSexp.parse_string model_string in
      let sexps = FromSexpToModel.get_and_check_model sexps in
      let fun_defs = FromSexpToModel.get_fun_defs sexps in
      let terms = FromModelToTerm.get_terms pinfo fun_defs in
      List.rev
        (Mstr.values
           (Mstr.mapi
              (fun _ ((ls, oloc, attrs), (t, t_concrete)) ->
                create_model_element ~value:t ~concrete_value:t_concrete
                  ~oloc ~attrs ~lsymbol:ls)
              terms))

let () =
  register_model_parser "smtv2" parse
    ~desc:"Parser@ for@ the@ model@ of@ SMT@ solvers."
