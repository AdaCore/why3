(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2025 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(********************************************************************)

(** This file is organized in 3 main modules:
    - FromStringToSexp, which parses the prover output (as string) to
    S-expressions
    - FromSexpToModel, which converts S-expressions to
    Smtv2_model_defs.fun_def
    - FromModelToTerm, which converts Smtv2_model_defs.fun_def to
    (Term.term, Model_parser.concrete_syntax_term) in order to create
    a list of Model_parser.model_element values *)

open Wstdlib
open Term
open Number
open Smtv2_model_defs
open Model_parser

let debug =
  Debug.register_flag "smtv2_parser"
    ~desc:
      "Print@ debugging@ messages@ about@ parsing@ the@ SMTv2@ model@ for@ \
       counterexamples."

let warn =
  Loc.register_warning "smtv2_parser"
    "Warning@ in@ parsing@ the@ SMTv2@ model@ for@ counterexamples@:"

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
  let atom f = function Atom s -> (try f s with _ -> error (Atom s) "atom") | sexp -> error sexp "atom"

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
        try
          { constant_int_value= int_literal ILitDec ~neg:false s;
            constant_int_verbatim= s }
        with _ -> atom_error s "positive_constant_int")
    | sexp -> error sexp "positive_constant_int"

  let negative_constant_int = function
    | List [ Atom "-"; Atom s ] as sexp -> (
        try
          { constant_int_value= int_literal ILitDec ~neg:true s;
            constant_int_verbatim= "-" ^ s }
        with _ -> error sexp "negative_constant_int")
    | sexp -> error sexp "negative_constant_int"

  let constant_int sexp =
    try positive_constant_int sexp
    with _ -> (
      try negative_constant_int sexp with _ -> error sexp "constant_int")

  let positive_constant_real s =
    try
      Scanf.sscanf s "%[^.].%s"
        (fun s1 s2 -> (s, s1, s2))
    with _ -> atom_error s "positive_constant_real"

  let constant_real = function
    | Atom s ->
      let s', i1, i2 = positive_constant_real s in
      { constant_real_value=
          (try
          real_literal ~radix:10 ~neg:false ~int:i1 ~frac:i2 ~exp:None
          with _ -> atom_error s "constant_real");
        constant_real_verbatim= s'
      }
    | List [ Atom "-"; Atom s ] as sexp ->
      let s', i1, i2 = positive_constant_real s in
      { constant_real_value=
          (try
          real_literal ~radix:10 ~neg:true ~int:i1 ~frac:i2 ~exp:None
          with _ -> error sexp "constant_real");
        constant_real_verbatim= "-" ^ s'
      }
    | sexp -> error sexp "constant_real"

  let constant_fraction ~neg sexp =
    let constant_int_fraction = function
      | Atom s ->
        { constant_real_value=
            real_literal ~radix:10 ~neg:false ~int:s ~frac:"0" ~exp:None;
          constant_real_verbatim= s
        }
      | List [ Atom "-"; Atom s ] ->
        { constant_real_value=
            real_literal ~radix:10 ~neg:true ~int:s ~frac:"0" ~exp:None;
          constant_real_verbatim= "-" ^ s
        }
      | sexp -> error sexp "constant_int_fraction"
    in
    let constant_int_or_real_fraction n =
      try constant_int_fraction n with _ -> constant_real n
    in
    match sexp with
    | List [ Atom "/"; n1; n2 ] ->
        let r1 = constant_int_or_real_fraction n1 in
        let r2 = constant_int_or_real_fraction n2 in
        let r1 =
          if neg then
            { constant_real_value= neg_real r1.constant_real_value;
              constant_real_verbatim= "-" ^ r1.constant_real_verbatim }
          else r1 in
        {
          constant_frac_num= r1;
          constant_frac_den= r2;
          constant_frac_verbatim= r1.constant_real_verbatim ^ "/" ^ r2.constant_real_verbatim
        }
    | _ -> error sexp "constant_fraction"

  let constant_fraction sexp =
    match sexp with
    | List [ Atom "-"; frac ] -> constant_fraction ~neg:true frac
    | _ -> constant_fraction ~neg:false sexp

  let constant_bv_bin = function
    | Atom s -> (
        try
          let s' = Strings.remove_prefix ~prefix:"#b" s in
          let constant_bv_value = BigInt.of_string ("0b" ^ s') in
          let constant_bv_length = String.length s' in
          { constant_bv_value; constant_bv_length; constant_bv_verbatim = s }
        with _ -> atom_error s "constant_bv_bin")
    | sexp -> error sexp "constant_bv_bin"

  let constant_bv_hex = function
    | Atom s -> (
        try
          let s' = Strings.remove_prefix ~prefix:"#x" s in
          let constant_bv_value = BigInt.of_string ("0x" ^ s') in
          let constant_bv_length = String.length s' * 4 in
          { constant_bv_value; constant_bv_length; constant_bv_verbatim = s }
        with _ -> atom_error s "constant_bv_hex")
    | sexp -> error sexp "constant_bv_hex"

  let constant_bv_dec = function
    | List [ Atom "_"; Atom n; l ] as sexp -> (
        try
          let constant_bv_value = BigInt.of_string (Strings.remove_prefix ~prefix:"bv" n) in
          let constant_bv_length = int l in
          { constant_bv_value; constant_bv_length; constant_bv_verbatim = string_of_sexp sexp }
        with _ -> error sexp "constant_bv_dec")
    | sexp -> error sexp "constant_bv_dec"

  let constant_bv sexp =
    try constant_bv_dec sexp
    with _ -> (
      try constant_bv_hex sexp
      with _ -> (
        try constant_bv_bin sexp with _ -> error sexp "constant_bv"))

  let constant_float sexp =
    let const_float e s v =
      {
        const_float_exp_size = e;
        const_float_significand_size = s;
        const_float_val = v
      }
    in
    match sexp with
    | List [ Atom "_"; Atom "+zero"; n1; n2 ] ->
        const_float (int n1) (int n2) Fpluszero
    | List [ Atom "_"; Atom "-zero"; n1; n2 ] ->
        const_float (int n1) (int n2) Fminuszero
    | List [ Atom "_"; Atom "+oo"; n1; n2 ] ->
        const_float (int n1) (int n2) Fplusinfinity
    | List [ Atom "_"; Atom "-oo"; n1; n2 ] ->
        const_float (int n1) (int n2) Fminusinfinity
    | List [ Atom "_"; Atom "NaN"; n1; n2 ] ->
        const_float (int n1) (int n2) Fnan
    | List [ Atom "fp"; sign; exp; mant ] ->
        let constant_float_sign = constant_bv sign in
        let constant_float_exp = constant_bv exp in
        let constant_float_mant = constant_bv mant in
        let v =
          Fnumber
            { constant_float_sign; constant_float_exp; constant_float_mant }
        in
        let exp_size = constant_float_exp.constant_bv_length in
        let significand =
          constant_float_mant.constant_bv_length +
          constant_float_sign.constant_bv_length
        in
        const_float exp_size significand v
    | sexp -> error sexp "constant_float"

  let constant sexp : term =
    let cst =
      try Cint (constant_int sexp)
      with E _ -> (
        try Creal (constant_real sexp)
        with E _ -> (
          try Cfraction (constant_fraction sexp)
          with E _ -> (
            try Cbitvector (constant_bv sexp)
            with E _ -> (
              try Cfloat (constant_float sexp)
              with E _ -> (
                try Cbool (bool sexp)
                with E _ -> (
                  try Cstring (string sexp) with E _ -> error sexp "constant"))))))
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
    (* Avoid a spurious indexed identifier present in Z3's output *)
    | List ( Atom "_" :: s ::  idx)  when not (s = Atom "as-array") ->
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
      if Strings.has_prefix ~prefix:"@" name || Strings.has_prefix ~prefix:"." name then
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
    match FromStringToSexp.parse_string (Option.value ~default:"" opt_name) with
    | [] -> atom_error name "get_type_from_prover_variable"
    | [ sexp ] -> sexp
    | sexps -> List sexps

  let qualified_identifier sexp : qual_identifier =
    match sexp with
    (* An actual qualified identifier *)
    | List [ Atom "as"; id; s ] -> Qannotident (identifier id, sort s)
    (* A non-qualified, possibly indexed, identifier *)
    | sexp -> (
        let id = identifier sexp in
        match id with
        | Isymbol (Sprover n') | Iindexedsymbol (Sprover n', _) ->
          (try
            let ty_sexp = get_type_from_prover_variable n' in
            Qannotident (id, sort ty_sexp)
          with _ -> Qident id)
        | Isymbol _ | Iindexedsymbol _ -> Qident id)

  let arg = function
    | List [ n; s ] -> (symbol n, sort s)
    | sexp -> error sexp "arg"

  let rec term sexp =
    try constant sexp
    with E _ -> (
      try Tvar (qualified_identifier sexp)
    with E _ -> (
      try ite sexp
    with E _ -> (
      try lett sexp
    with E _ -> (
      try forall sexp
    with E _ -> (
      try array sexp
    with E _ -> (
      try application sexp
    with E _ -> Tunparsed (string_of_sexp sexp)))))))

  and ite = function
    | List [ Atom "ite"; t1; t2; t3 ] -> Tite (term t1, term t2, term t3)
    | sexp -> error sexp "ite"

  and lett = function
    | List [ Atom "let"; List bindings; t2 ] ->
        let binding = (function
        | (List [ n; t ]) -> (symbol n, term t)
        | sexp -> error sexp "let binding") in
        Tlet ((List.map binding bindings), (term t2))
    | sexp -> error sexp "let"

  and forall = function
  | List (Atom "forall" :: List bindings :: t :: []) ->
      let binding = (function
      | (List [ n; s ]) -> (symbol n, sort s)
      | sexp -> error sexp "forall binding") in
      Tforall ((List.map binding bindings), (term t))
  | sexp -> error sexp "forall"

  and application = function
    | List (qual_id :: ts) ->
        Tapply (qualified_identifier qual_id, List.map term ts)
    | sexp -> error sexp "application"

  and array sexp =
    match sexp with
    | List [Atom "_"; Atom "as-array"; n] ->
        Tasarray (term n)
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
        let args = list arg args in
        let body = term body in
        Some (n, (args, res, body))
    | _ -> None

  let is_model_decl = function Atom "define-fun" -> true | _ -> false

  let get_and_check_model sexps =
    if sexps = [] then []
    else
      let model, rest =
        match sexps with
        | List (Atom "model" :: model) :: rest -> (model, rest)
        | List [] :: rest -> ([], rest)
        | List model :: rest when List.exists (Sexp.exists is_model_decl) model
          ->
           (model, rest)
        | [] ->
           failwith "Cannot read S-expression as model: empty list"
        | se :: _ ->
           Format.eprintf "se = %a@." pp_sexp se;
           failwith "Cannot read the S-expression above as model."
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
**  Converting Smtv2_model_defs.fun_def to (Term.term,
**  Model_parser.concrete_syntax_term)
**********************************************************************
*)

module FromModelToTerm = struct
  exception E_parsing of string
  exception E_concrete_syntax of string

  exception NoArgConstructor
  exception NoBuiltinSymbol
  exception Float_MinusZero
  exception Float_PlusZero
  exception Float_NaN
  exception Float_Plus_Infinity
  exception Float_Minus_Infinity
  exception Float_Error

  let error fmt =
    Format.kasprintf (fun msg -> raise (E_parsing msg)) fmt
  let _error_concrete_syntax fmt =
    Format.kasprintf (fun msg -> raise (E_concrete_syntax msg)) fmt

  type env = {
    (* Why3 environment, used to retrieve builtin theories. *)
    why3_env : Env.env;
    (* Constructors from [pinfo.Printer.constructors]. *)
    constructors : lsymbol Mstr.t;
    (* Function definitions from the SMT model
       that are not in [pinfo.Printer.queried_terms]. *)
    mutable prover_fun_defs : Term.term Mstr.t;
    (* Sorts defined in the smtv2 file output. *)
    type_sorts : Ty.ty Mstr.t;
    (* Prover variables, may have the same name if the sort is different. *)
    mutable prover_vars : vsymbol Ty.Mty.t Mstr.t;
    (* Bound variables in the body of a function or in a let construction. *)
    mutable bound_vars : vsymbol Mstr.t;
    (* Inferred associations between Why3 types and SMT sorts, coming from lsymbols
       in [pinfo.Printer.queried_terms]. *)
    mutable inferred_types : (sort * Ty.ty) list;
    (* Evaluation of prover variables (using type coercions and fields). *)
    mutable eval_prover_vars : Term.term Mvs.t;
  }

  (* Convert a SMT sort [s] to a Why3 type.
     If [update_ty] is equal to [Some ty], the function updates [env.inferred_types]
     with the association [(s,ty)].
     TODO/FIXME It would be better to find a way to avoid using [env.inferred_types],
     maybe by searching in the theories? *)
  let rec smt_sort_to_ty ?(update_ty = None) env s =
    let optionally_update_sort s =
      match update_ty with
        | None -> error "@[Cannot infer type from sort@ @[%a@]" print_sort s
        | Some ty ->
          Debug.dprintf debug
            "[smt_sort_to_ty] updating inferred_types with s = %a, ty = %a@."
            print_sort s Pretty.print_ty_qualified ty;
          env.inferred_types <- (s, ty) :: env.inferred_types;
          ty
    in
    let find_in_inferred_types not_found s =
      match
        List.find_all (fun (s', _) -> sort_equal s s') env.inferred_types
      with
      | [] -> not_found s
      | [ (_, ty) ] -> ty
      | _ ->
          error "@[Multiple matches in inferred_types for sort @[%a@]@]"
            print_sort s
    in
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
                  Pretty.print_ty_qualified ty print_sort s))
    | Ssimple i | Smultiple (i, _) ->
        let not_found s =
          let sort_name =
            match i with
            | Isymbol (S s | Sprover s) -> s
            | Iindexedsymbol ((S s | Sprover s), _) -> s
          in
          (* Find the corresponding sorts among the ones printed in the
            smtv2 file passed to the prover. *)
          match Mstr.find_opt sort_name env.type_sorts with
          | None -> optionally_update_sort s
          | Some ty -> ty
        in
        find_in_inferred_types not_found s
    | Sbitvec size ->
      let find_builtin_bitvec s =
        (* Find the corresponding sorts among the ones printed in the
          smtv2 file passed to the prover. *)
        let type_name = Format.sprintf "(_ BitVec %d)" size in
        match Mstr.find_opt type_name env.type_sorts with
        | None -> optionally_update_sort s
        | Some ty -> ty
      in
      find_in_inferred_types find_builtin_bitvec s
    | Sfloatingpoint (exp, significand) ->
      let find_builtin_float s =
        (* Currenlty, float types are translated as Float32 or Float64 in smtlib
            drivers. *)
        let type_name = Format.sprintf "Float%d" (exp + significand) in
        match Mstr.find_opt type_name env.type_sorts with
        | None -> optionally_update_sort s
        | Some ty -> ty
      in
      find_in_inferred_types find_builtin_float s
    | Sroundingmode ->
      find_in_inferred_types optionally_update_sort s
    | Sreglan -> optionally_update_sort s

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
                    Pretty.print_ty_qualified vs.vs_ty Pretty.print_vs_qualified vs print_sort s
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
                  Pretty.print_vs_qualified new_vs Pretty.print_ty_qualified vs_ty;
                env.prover_vars <-
                  Mstr.add n (Ty.Mty.add vs_ty new_vs mvs) env.prover_vars;
                new_vs
          with Not_found ->
            Debug.dprintf debug
              "[qual_id_to_term] updating prover_vars with vs = %a / vs_ty = %a@."
              Pretty.print_vs_qualified new_vs Pretty.print_ty_qualified vs_ty;
            env.prover_vars <-
              Mstr.add n (Ty.Mty.add vs_ty new_vs Ty.Mty.empty) env.prover_vars;
            new_vs)
      | _ ->
          error "Could not interpret qualified identifier %a@."
            print_qualified_identifier qid
    in
    t_var vs

  (* Be careful when modifying this code! *)
  let float_of_binary fp =
    let smtv2_model_bv_to_model_parser_bv
        { constant_bv_value; constant_bv_length; constant_bv_verbatim } =
      {
        bv_value= constant_bv_value;
        bv_length= constant_bv_length;
        bv_verbatim= constant_bv_verbatim
      }
    in
    match fp with
    | Fplusinfinity -> raise Float_Plus_Infinity
    | Fminusinfinity -> raise Float_Minus_Infinity
    | Fpluszero -> raise Float_PlusZero
    | Fminuszero -> raise Float_MinusZero
    | Fnan -> raise Float_NaN
    | Fnumber { constant_float_sign; constant_float_exp; constant_float_mant } ->
        let sign = smtv2_model_bv_to_model_parser_bv constant_float_sign in
        let exp = smtv2_model_bv_to_model_parser_bv constant_float_exp in
        let mant = smtv2_model_bv_to_model_parser_bv constant_float_mant in
        let fp_binary = (sign, exp, mant) in
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
          if Strings.has_prefix ~prefix:"#b" mant.bv_verbatim then
            let adjust = 4 - (mant.bv_length mod 4) in
            if adjust = 4 then mant.bv_value (* No adjustment needed *)
            else BigInt.mul (BigInt.pow_int_pos 2 adjust) mant.bv_value
          else mant.bv_value
        in
        let pad_with_zeros width s =
          let filled =
            let len = width - String.length s in
            if len <= 0 then "" else String.make len '0'
          in
          filled ^ s
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
            let fp_hex = Format.asprintf "%t0x0.%sp-%s"
                (fun fmt -> if is_neg then Pp.string fmt "-")
                frac (BigInt.to_string exp) in
            ( is_neg,
              "0",
              frac,
              Some (String.concat "" [ "-"; BigInt.to_string exp ]),
              fp_binary,
              fp_hex )
        else if BigInt.eq exp.bv_value exp_max (* infinities and NaN *) then
          if BigInt.eq mant.bv_value BigInt.zero then
            if is_neg
            then raise Float_Minus_Infinity
            else raise Float_Plus_Infinity
          else raise Float_NaN
        else
          let exp = BigInt.sub exp.bv_value exp_bias in
          let fp_hex = Format.asprintf "%t0x1.%sp%s"
              (fun fmt -> if is_neg then Pp.string fmt "-")
              frac (BigInt.to_string exp) in
          (is_neg, "1", frac, Some (BigInt.to_string exp), fp_binary, fp_hex)

  let constant_to_term env c =
    match c with
    | Cint {constant_int_value= int_value; constant_int_verbatim= _int_verbatim} ->
      t_const (Constant.ConstInt int_value) Ty.ty_int
    | Creal { constant_real_value= real_value; constant_real_verbatim= _real_verbatim } ->
      t_const (Constant.ConstReal real_value) Ty.ty_real
    | Cfraction { constant_frac_num; constant_frac_den; constant_frac_verbatim = _ } -> (
        try
          let t = t_const (Constant.ConstReal constant_frac_num.constant_real_value) Ty.ty_real in
          let t' = t_const (Constant.ConstReal constant_frac_den.constant_real_value) Ty.ty_real in
          let th = Env.read_theory env.why3_env [ "real" ] "Real" in
          let div_ls =
            Theory.ns_find_ls th.Theory.th_export [ Ident.op_infix "/" ]
          in
          t_app_infer div_ls [ t; t' ]
        with _ ->
          error "Could not interpret constant %a as a fraction@." print_constant
            c)
    | Cbitvector { constant_bv_value; constant_bv_length; constant_bv_verbatim = _ } ->
        let ty = smt_sort_to_ty env (Sbitvec constant_bv_length) in
        t_const (Constant.int_const constant_bv_value) ty
    | Cfloat fp -> (
        let exp_size = fp.const_float_exp_size in
        let significand_size = fp.const_float_significand_size in
        let sort = Sfloatingpoint (exp_size, significand_size) in
        let ty = smt_sort_to_ty env sort in
        let float_lib = "Float" ^ string_of_int (exp_size + significand_size) in
        try
          (* general case *)
          let neg, s1, s2, exp, (_bv_sign,_bv_exp,_bv_mant), _hex =
            float_of_binary fp.const_float_val
          in
            t_const
              (Constant.real_const_from_string ~radix:16 ~neg ~int:s1 ~frac:s2
                ~exp)
              ty
        with
        (* cases for special float values *)
        | Float_MinusZero ->
            t_const
              (Constant.real_const_from_string ~radix:10 ~neg:true ~int:"0"
                 ~frac:"0" ~exp:None) ty
        | Float_PlusZero ->
            t_const
              (Constant.real_const_from_string ~radix:10 ~neg:false ~int:"0"
                 ~frac:"0" ~exp:None) ty
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
            t_eps_close x f
        | Float_Plus_Infinity ->
            let is_plus_infinite_ls =
              try
                let th =
                  Env.read_theory env.why3_env [ "ieee_float" ] float_lib
                in
                Theory.ns_find_ls th.Theory.th_export [ "is_plus_infinity" ]
              with _ -> error "No lsymbol found in theory for is_plus_infinity@."
            in
            let x = create_vsymbol (Ident.id_fresh "x") ty in
            let f = t_app is_plus_infinite_ls [ t_var x ] None in
            t_eps_close x f
        | Float_Minus_Infinity ->
            let is_plus_infinite_ls =
              try
                let th =
                  Env.read_theory env.why3_env [ "ieee_float" ] float_lib
                in
                Theory.ns_find_ls th.Theory.th_export [ "is_minus_infinity" ]
              with _ ->
                error "No lsymbol found in theory for is_minus_infinity@."
            in
            let x = create_vsymbol (Ident.id_fresh "x") ty in
            let f = t_app is_plus_infinite_ls [ t_var x ] None in
            t_eps_close x f
        | Float_Error ->
            error "Error while interpreting float constant %a@." print_constant
              c)
    | Cbool b ->
        (* boolean constants from SMT model are interpreted by default to Why3 terms
           (with type Some ty_bool) and not to formulas: later on in the functions
           apply_to_term and smt_term_to_term we convert Why3 terms to formulas using
           Term.to_prop when needed *)
        if b then t_bool_true else t_bool_false
    | Cstring str -> t_const (Constant.string_const str) Ty.ty_str

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

  let rec term_to_term env ty_s t =
    match t with
    | Tconst c -> constant_to_term env c
    | Tvar qid -> (
        try qual_id_to_term env qid
        with NoArgConstructor -> apply_to_term env ty_s qid [])
    | Tite (b, t1, t2) ->
        let b' = term_to_term env None b in
        let t1' = term_to_term env ty_s t1 in
        let t2' = term_to_term env ty_s t2 in
        t_if b' t1' t2'
    | Tapply (qid, ts) -> apply_to_term env ty_s qid ts
    | Tarray (s1, s2, a) -> array_to_term env s1 s2 a
    | Tasarray t -> asarray_to_term env ty_s t
    | Tlet (bindings, t) -> let_to_term env ty_s bindings t
    | Tforall (bindings, t) -> forall_to_term env ty_s bindings t
    | Tunparsed _ -> error "Could not interpret term %a@." print_term t

  and apply_to_term env ty_s qid ts =
    let maybe_prover_fun_def env n ts' =
      try
        (* search if [n] is the name of a prover function definition *)
        let t = Mstr.find n env.prover_fun_defs in
        let vs_args, _, t' = t_open_lambda t in
        begin match vs_args, ts' with
        (* special case for constants, we just substitute by the prover constant *)
        | [],[] -> Some t
        (* general case *)
        | vs_args,ts' ->
          let subst = Mvs.of_list (List.combine vs_args ts') in
            Some (t_subst subst t')
        end
      with _ -> None
    in
    let maybe_known_ls_or_new ~opt_sort env n ts' =
      (* search for [n] in constructors and in builtin symbols *)
      let ls =
        try Mstr.find n env.constructors
        with _ ->
          begin try find_builtin_lsymbol env n ts'
          with NoBuiltinSymbol ->
            begin match opt_sort with
            | None ->
              (* no sort is associated to Qident, so we cannot infer the type of the
                  lsymbol to create and fails instead *)
              error "No lsymbol found for qualified identifier %a@."
                print_qualified_identifier qid
            | Some s ->
              let ts'_ty =
                try List.map (fun t -> Option.get t.t_ty) ts'
                with _ ->
                  error "Arguments of %a should have a type@."
                    print_qualified_identifier qid
              in
              (* for Qannotident, we can infer the type and create a fresh lsymbol *)
              create_lsymbol (Ident.id_fresh n) ts'_ty
                (Some (smt_sort_to_ty env s))
            end
          end
      in
      try t_app ls ts' ty_s
      with _ ->
        try t_app_infer ls ts'
        with e ->
        error "@[Cannot apply lsymbol@ @[%a@] to terms@ @[(%a)@]:@ @[%a@]" Pretty.print_ls_qualified ls
          (Pp.print_list Pp.comma Pretty.print_term)
          ts' Exn_printer.exn_printer e
    in
    match (qid, ts) with
    | Qident (Isymbol (S "=")), [ t1; t2 ] ->
        let t1' = term_to_term env ty_s t1 in
        let t2' = term_to_term env ty_s t2 in
        t_equ t1' t2'
    | Qident (Isymbol (S "or")), hd :: tl ->
        let hd = term_to_term env None hd in
        List.fold_left
          (fun t t' ->
            let t' = term_to_term env None t' in
            ( t_binary Term.Tor t (Term.to_prop t')))
          (Term.to_prop hd)
          tl
    | Qident (Isymbol (S "and")), hd :: tl ->
        let hd = term_to_term env None hd in
        List.fold_left
          (fun t t' ->
            let t' = term_to_term env None t' in
            ( t_binary Term.Tand t (Term.to_prop t')))
          (Term.to_prop hd)
          tl
    | Qident (Isymbol (S "not")), [ t ] ->
        let t = term_to_term env None t in
        t_not (Term.to_prop t)
    (*  In the general case, we first search if [n] corresponds to a known
        prover definition (in which case we apply a substitution), or a known
        symbol (constructor, builtin).
        Otherwise, we can create a fresh lsymbol only for Qannotident cases, since
        Qident are not associated to an SMT sort. *)
    | Qident (Isymbol (S n)), ts | Qident (Isymbol (Sprover n)), ts ->
        let ts' = List.map (term_to_term env None) ts in
        begin match maybe_prover_fun_def env n ts' with
        | Some t -> t
        | None -> maybe_known_ls_or_new ~opt_sort:None env n ts'
        end
    | Qannotident (Isymbol (S n), s), ts
    | Qannotident (Isymbol (Sprover n), s), ts ->
      let ty_s = smt_sort_to_ty env s in
      let ts' = List.map (term_to_term env (Some ty_s)) ts in
      begin match maybe_prover_fun_def env n ts' with
      | Some t -> t
      | None -> maybe_known_ls_or_new ~opt_sort:(Some s) env n ts'
      end
    | _ -> error "Could not interpret %a@." print_qualified_identifier qid

  and array_to_term env s1 s2 elts =
    (* arrays are translated using a function of type [ty1] -> [ty2] *)
    let ty1 = smt_sort_to_ty env s1 in
    let ty2 = smt_sort_to_ty env s2 in
    let vs_arg = create_vsymbol (Ident.id_fresh "x") ty1 in
    let mk_case key value t =
      let key = term_to_term env (Some ty1) key in
      let value = term_to_term env (Some ty2) value in
      if Ty.oty_equal key.t_ty (Some ty1) && Ty.oty_equal value.t_ty (Some ty2)
      then
         t_if (t_equ (t_var vs_arg) key) value t
      else
        error
          "Type %a for sort %a of array keys and/or type %a for sort %a of \
           array values do not match@."
          (Pp.print_option_or_default "None" Pretty.print_ty_qualified)
          key.t_ty print_sort s1
          (Pp.print_option_or_default "None" Pretty.print_ty_qualified)
          value.t_ty print_sort s2
    in
    let t_others = term_to_term env (Some ty2) elts.array_others in
    let a =
      List.fold_left
        (fun acc (key, value) -> mk_case key value acc)
        t_others
        elts.array_indices
    in
    Pretty.forget_var vs_arg;
    t_lambda [ vs_arg ] [] a

  and asarray_to_term env _ty_s elt =
    match elt with
    | Tvar (Qident (Isymbol (S n)) | Qident (Isymbol (Sprover n))) -> begin
      match Mstr.find_opt n env.prover_fun_defs with
      | Some t -> t
      | _ -> error "The function %s cannot be converted into an array type@." n
    end
    | _ -> error "Cannot interpret the 'as-array' term"

  and let_to_term env ty_s bindings t =
    (* TODO the syntax in of Smtv2_model_defs_terms should be updated to keep track
       of the type of the let-introduced term *)
    match bindings with
    | [] -> term_to_term env ty_s t
    | (sym,tt)::bindings ->
      let body = term_to_term env ty_s tt in
      match sym with | S str | Sprover str ->
      let vs = create_vsymbol (Ident.id_fresh str) (Option.get body.t_ty)
      in
      env.bound_vars <- Mstr.add str vs env.bound_vars;
      let t = let_to_term env None bindings t in
      t_let t (t_close_bound vs body)
  and forall_to_term env ty_s bindings t =
    match bindings with
    | [] -> term_to_term env ty_s t
    | (sym,sort)::bindings ->
      match sym with | S str | Sprover str ->
      let vs = create_vsymbol (Ident.id_fresh str) (smt_sort_to_ty env sort)
      in
      env.bound_vars <- Mstr.add str vs env.bound_vars;
      let t = forall_to_term env ty_s bindings t
      in
      t_forall_close [vs] [] t

  (*  Interpreting function definitions from the SMT model to [t',t'_concrete].
      - [t'] is a Term.term
      - [t'_concrete] is a Model_parser.concrete_syntax_term
      We go recursively into the function definition [t], while keeping the
      invariant "t' and t'_concrete must have the same shape". *)
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
    let t' = term_to_term env ty_s t in
    (* convert t' to a formula if the expected type of the result is None (fmla=true) *)
    let t' = if fmla then Term.to_prop t' else t' in
    if Option.equal Ty.ty_equal ty_s t'.t_ty then (
      Debug.dprintf debug "[smt_term_to_term] t' = %a, t'.t_ty = %a@."
        Pretty.print_term t'
        (Pp.print_option_or_default "None" Pretty.print_ty_qualified)
        t'.t_ty;
      t')
    else
      error "Type %a for sort %a and type %a for term %a do not match@."
        (Pp.print_option_or_default "None" Pretty.print_ty_qualified)
        ty_s print_sort s
        (Pp.print_option_or_default "None" Pretty.print_ty_qualified)
        t'.t_ty print_term t

  (* Check that the definiton of a function in the SMT model matches the type
     of the corresponding lsymbol in [env.queried_terms]. *)
  let check_fun_def_type env ls (args, res, body) =
    Debug.dprintf debug "-----------------------------@.";
    Debug.dprintf debug "[check_fun_def_type] fun_def = %a@." print_function_def
      (args, res, body);
    Debug.dprintf debug "[check_fun_def_type] ls = %a@." Pretty.print_ls_qualified ls;
    Debug.dprintf debug "[check_fun_def_type] ls.ls_value = %a@."
      (Pp.print_option_or_default "None" Pretty.print_ty_qualified)
      ls.ls_value;
    if (Debug.test_flag debug) then
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
          print_function_def (args, res, body) Pretty.print_ls_qualified ls
    with Invalid_argument _ ->
      error "@[Function arity mismatch when interpreting@ @[%a@]@ with lsymbol@ @[%a@]@]"
        print_function_def (args, res, body) Pretty.print_ls_qualified ls

  (* Interpretation of function definitions in the model to terms. *)
  let interpret_fun_def_to_term ~fmla env (args, res, body) =
    Debug.dprintf debug "-----------------------------@.";
    Debug.dprintf debug "[interpret_fun_def_to_term] fun_def = %a@."
      print_function_def (args, res, body);
      (* env.bound_vars <- Mstr.empty;
      List.iter (fun (symbol, sort) -> *)
    let bound_vars = List.fold_left (fun bound_vars (symbol, sort) ->
        match symbol with
        | S str | Sprover str ->
            let fresh_str = Ident.id_fresh str in
            let vs = create_vsymbol fresh_str (smt_sort_to_ty env sort) in
            Mstr.add str vs bound_vars)
            (* env.bound_vars <- Mstr.add str vs env.bound_vars) *)
      Mstr.empty (* I don't know why this is an empty map and not env.bound_vars, but it was like this before *)
      (* env.bound_vars *)
      args
    in
    env.bound_vars <- bound_vars;
    if (Debug.test_flag debug) then
      Mstr.iter
        (fun key vs ->
          Debug.dprintf debug "[interpret_fun_def_to_term] bound_var = (%s, %a)@."
            key Pretty.print_vs_qualified vs)
        env.bound_vars;
    let t_body = smt_term_to_term ~fmla env body res in
    let t =
      if List.length (Mstr.values env.bound_vars) = 0 then
        t_body
      else
        t_lambda (Mstr.values env.bound_vars) [] t_body
    in
    (* List.iter
      Pretty.forget_var
      (Mstr.values env.bound_vars); *)
    Debug.dprintf debug "[interpret_fun_def_to_term] t = %a@."
      Pretty.print_term t;
    Debug.dprintf debug "-----------------------------@.";
    t

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
     We also perform some trivial evaluation by e.g. simplifying if then else terms when
     the condition can be evaluated to true/false, etc.
     We also have to make sure that we apply the same modifications in [t] and in [t_concrete].
  *)

  (* [eval_prover_var] is set to false when we create the epsilon term (which
     may contain other prover variables)
     [seen_prover_vars] records already seen prover variables when evaluating
     a term to avoid unbounded recursion *)
  let rec eval_term env ?(eval_prover_var = true) seen_prover_vars terms t =
    match t.t_node with
    | Term.Tvar vs -> (
        match Mvs.find_opt vs env.eval_prover_vars with
        | Some t_vs ->
            (* vs is a prover variable *)
            if eval_prover_var then
              if List.mem vs seen_prover_vars then t_vs
              else
                eval_term env ~eval_prover_var (vs :: seen_prover_vars) terms t_vs
            else t
        | None -> t (* vs is not a prover variable *))
    | Term.Tapp (ls, [ t1; t2 ]) when ls_equal ls ps_equ -> (
        match (t1.t_node, t2.t_node) with
        | Term.Tvar v1, Term.Tvar v2
          when is_vs_in_prover_vars v1 env.prover_vars
               && is_vs_in_prover_vars v2 env.prover_vars ->
            (* distinct prover variables are not equal *)
            if vs_equal v1 v2 then t_true else t_false
        | _ ->
            (* general case *)
            let t1' = eval_term env ~eval_prover_var seen_prover_vars terms t1
            in
            let t2' = eval_term env ~eval_prover_var seen_prover_vars terms t2
            in
            if t_equal t1' t2' then t_true
            else  t_app ls [ t1'; t2' ] t.t_ty)
    | Term.Tapp (ls, ts) ->
        let ts =
          List.map
            (eval_term env ~eval_prover_var seen_prover_vars terms) ts
        in
        t_app ls ts t.t_ty
    | Term.Tif (b, t1, t2) ->
        let b' = eval_term env ~eval_prover_var seen_prover_vars terms b in
        if is_true env b' then
          eval_term env ~eval_prover_var seen_prover_vars terms t1
        else if is_false env b' then
          eval_term env ~eval_prover_var seen_prover_vars terms t2
        else
          let t1' =
            eval_term env ~eval_prover_var seen_prover_vars terms t1 in
          let t2' =
            eval_term env ~eval_prover_var seen_prover_vars terms t2 in
          t_if b' t1' t2'
    | Term.Teps tb -> (
        match Term.t_open_lambda t with
        | [], _, _ ->
            let vs, t' = Term.t_open_bound tb in
            let t'_eval = eval_term env ~eval_prover_var seen_prover_vars terms t' in
            t_eps_close vs t'_eval
          (* some float constants are represented using epsilon terms *)
        | vsl, trig, t' ->
            let t'_eval =
              eval_term env ~eval_prover_var seen_prover_vars terms t' in
            t_lambda vsl trig t'_eval)
    | Term.Tquant (q, tq) ->
        let vsl, trig, t' = t_open_quant tq in
        let t' = eval_term env ~eval_prover_var seen_prover_vars terms t' in
        t_quant q (t_close_quant vsl trig t')
    | Term.Tbinop (Term.Tor, t1, t2) ->
        let t1 =
          eval_term env ~eval_prover_var seen_prover_vars terms t1 in
        let t2 =
          eval_term env ~eval_prover_var seen_prover_vars terms t2 in
        if is_true env t1 || is_true env t2 then t_true
        else if is_false env t1 || is_false env t2 then t_false
        else t_binary Term.Tor t1 t2
    | Term.Tbinop (Term.Tand, t1, t2) ->
        let t1 =
          eval_term env ~eval_prover_var seen_prover_vars terms t1 in
        let t2 =
          eval_term env ~eval_prover_var seen_prover_vars terms t2 in
        if is_true env t1 && is_true env t2 then t_true
        else if is_false env t1 && is_false env t2 then t_true
        else if is_true env t1 && is_false env t2 then t_false
        else if is_false env t1 && is_true env t2 then t_false
        else t_binary Term.Tand t1 t2
    | Term.Tbinop (op, t1, t2) ->
        let t1 = eval_term env ~eval_prover_var seen_prover_vars terms t1 in
        let t2 = eval_term env ~eval_prover_var seen_prover_vars terms t2 in
        (t_binary op t1 t2)
    | Term.Tnot t' ->
        let t' = eval_term env ~eval_prover_var seen_prover_vars terms t' in
        if is_true env t' then t_false
        else if is_false env t' then t_true
        else t_not t'
    | _ -> t

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
                      (fun _ ((ls', _, _), t) ->
                        if ls_equal ls ls' then Some (ls, t) else None)
                      terms))
               (Sls.elements sls)))
        pinfo.Printer.type_coercions
    in
    if (Debug.test_flag debug) then
      Ty.Mty.iter
        (fun key elt ->
          List.iter
            (fun (str, (ls, t)) ->
              Debug.dprintf debug
                "[ty_coercions] ty = %a, str=%s, ls = %a, t=%a@."
                Pretty.print_ty_qualified
                key str Pretty.print_ls_qualified ls Pretty.print_term t)
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
                      (fun _ ((ls', _, _), t) ->
                        if ls_equal ls ls' then Some (ls, t) else None)
                      terms))
               lls))
        pinfo.Printer.type_fields
    in
    if (Debug.test_flag debug) then
      Ty.Mty.iter
        (fun key elt ->
          List.iter
            (fun (str, (ls, t)) ->
              Debug.dprintf debug "[ty_fields] ty = %a, str=%s, ls = %a, t=%a@."
                Pretty.print_ty_qualified key str Pretty.print_ls_qualified ls
                Pretty.print_term t)
            elt)
        ty_fields;
    (* for each prover variable, we create an epsilon term using type coercions
       or record type fields for the type of the prover variable *)
    Mstr.iter
      (fun key value ->
        Ty.Mty.iter
          (fun ty vs ->
            let create_epsilon_term ty l =
              (* create a fresh vsymbol for the variable bound by the epsilon term *)
              let x = create_vsymbol (Ident.id_fresh "x") ty in
              let aux (_, (ls', t')) =
                let vs_list', _, t' = t_open_lambda t' in
                let vs' =
                  match vs_list' with
                  | [ vs' ] -> vs'
                  | _ ->
                      error
                        "Only one variable expected when opening lambda-term %a"
                        Pretty.print_term t'
                in
                let t' =
                  eval_term env ~eval_prover_var:false [] terms
                    (t_subst_single vs' (t_var vs) t')
                in
                (* substitute [vs] by this new variable in the body [t'] of the function
                    defining the type coercion *)
                let t' = t_subst_single vs' (t_var x) t' in
                (* construct the formula to be used in the epsilon term *)
                t_equ (t_app_infer ls' [ t_var x ]) t'
              in
              let l'= List.map aux l in
              let f = t_and_l l' in
              Pretty.forget_var x;
              (* replace [t] by [eps x. f] *)
              t_eps_close x f
            in
            let eval_var =
              (* first search if [ty] is a record type associated to some fields *)
              match Ty.Mty.find_def [] ty ty_fields with
              | [] -> (
                  (* if no fields, search if there exists some type coercions for [ty] *)
                  match Ty.Mty.find_def [] ty ty_coercions with
                  | [] -> t_var vs
                  | coercions -> create_epsilon_term ty coercions)
              | fields -> create_epsilon_term ty fields
            in
            Debug.dprintf debug
              "[eval] prover_var = %s, vs = %a, eval_var = %a@."
              key
              Pretty.print_term (t_var vs)
              Pretty.print_term eval_var;
            env.eval_prover_vars <-
              Mvs.add vs eval_var env.eval_prover_vars;
            Pretty.forget_var vs )
          value)
      env.prover_vars;
    (* we now call [eval_term] on each [(t,t_concrete)] in [terms] in order
       to replace each prover variable by the corresponding epsilon term *)
    Mstr.mapi
      (fun _ ((ls, oloc, attrs), t) ->
        let t' = eval_term env [] terms t in
        Debug.dprintf debug "[eval] t = %a ==> t' = %a@." Pretty.print_term t
          Pretty.print_term t';
        (ls, oloc, attrs), t')
      terms

  let clean env terms =
    Mstr.map_filter
      (fun ((ls, oloc, attr), t) ->
        (* if some prover variables remain after evaluation, remove the terms
        containing those prover variables *)
        if Term.t_v_any (fun vs -> is_vs_in_prover_vars vs env.prover_vars) t
        then None
        else
          Some ((ls, oloc, attr), t))
      terms

  let get_terms (pinfo : Printer.printing_info)
      (fun_defs : Smtv2_model_defs.function_def Mstr.t) =
    let qterms = pinfo.Printer.queried_terms in
    if (Debug.test_flag debug) then begin
      Mstr.iter
        (fun key _ -> Debug.dprintf debug "[fun_defs] name = %s@." key)
        fun_defs;
      Mstr.iter
        (fun key (ls, _, _) ->
          Debug.dprintf debug "[queried_terms] name = %s, ls = %a@." key
            Pretty.print_ls_qualified ls)
        qterms;
      Mstr.iter
        (fun key ls ->
          Debug.dprintf debug "[constructors] name = %s, ls = %a/%d@." key
            Pretty.print_ls_qualified ls (List.length ls.ls_args))
        pinfo.Printer.constructors;
      Mstr.iter
        (fun key ty ->
          Debug.dprintf debug "[types] name = %s, ty = %a@." key
            Pretty.print_ty_qualified ty)
        pinfo.Printer.type_sorts
      end;
    let env =
      {
        why3_env = pinfo.Printer.why3_env;
        prover_vars = Mstr.empty;
        bound_vars = Mstr.empty;
        constructors = pinfo.Printer.constructors;
        type_sorts = pinfo.Printer.type_sorts;
        inferred_types = [];
        eval_prover_vars = Mvs.empty;
        prover_fun_defs = Mstr.empty;
      }
    in
    (*  Function definitons in the prover output may contain:
        - functions corresponding to a lsymbol in queried terms,
        for which we expect a definiton in the model that respects
        the type of the lsymbol;
        - other functions, for which we cannot check that the type
        respects an expected lsymbol type.
        This is why we split the analysis. *)
    let queried_fun_defs, prover_fun_defs =
      Mstr.partition (fun n _ -> Mstr.mem n qterms) fun_defs
    in
    (*  We first check that function definitions in [queried_fun_defs]
        respects the type of the associated lsymbol.
        Doing this pre-analysis is used to update [env.inferred_types]
        with pairs of (SMT type, Why3 type) when the SMT type cannot be
        easily mapped to a Why3 type. *)
    let queried_fun_defs =
      Mstr.mapi_filter
        (fun n def ->
          match Mstr.find n qterms with
          | ls, _, _ -> (
              try
                check_fun_def_type env ls def;
                Some def
              with
              | E_parsing str | E_concrete_syntax str ->
                    Loc.warning warn
                    "@[Error while checking function definition type@ @[%s@]:@ @[%s@]@]" n str;
                  None
              | _ ->
                  Loc.warning warn
                    "@[Error while checking function definition type@ @[%s@]" n;
                  None)
          | exception Not_found -> None)
        queried_fun_defs
    in
    (*  Enriching [env] with prover function definitions. *)
    Mstr.iter
      (fun n def ->
        match Mstr.find n qterms with
        | _, _, _ -> ()
        | exception Not_found -> (
            try
              Debug.dprintf debug
                "No term for %s, adding term to env.prover_fun_defs@." n;
              let t = interpret_fun_def_to_term ~fmla:false env def in
              env.prover_fun_defs <- Mstr.add n t env.prover_fun_defs
            with
            | E_parsing str | E_concrete_syntax str ->
                Loc.warning warn "@[Error while interpreting@ @[%s@]:@ @[%s@]" n str
            | _ -> Loc.warning warn "@[Error while interpreting @[%s@]@]" n))
      prover_fun_defs;
    (*  Interpretation of queried function definitions. *)
    let terms =
      Mstr.mapi_filter
        (fun n def ->
          match Mstr.find n qterms with
          | ls, oloc, attrs -> (
              try
                (* fmla = true if the interpreted term should be a formula (with type = None)
                   and not a term (with type = Some ty) *)
                let fmla = not (Option.is_some ls.ls_value) in
                let t = interpret_fun_def_to_term ~fmla env def in
                Some ((ls, oloc, attrs), t)
              with
              | E_parsing str | E_concrete_syntax str ->
                  Loc.warning warn "@[Error while interpreting@ @[%s@]:@ @[%s@]" n str;
                  None
              | _ ->
                  Loc.warning warn "@[Error while interpreting @[%s@]@]" n;
                  None)
          | exception Not_found -> None)
        queried_fun_defs
    in
    let debug_terms desc terms =
      if (Debug.test_flag debug) then
        Mstr.iter
          (fun n ((ls, oloc, _), t) ->
            Debug.dprintf debug
              "[TERMS %s] name = %s, ls = %a, oloc = %a, t = %a@." desc n
              Pretty.print_ls_qualified ls
              (Pp.print_option Pretty.print_loc_as_attribute) oloc
              Pretty.print_term t)
          terms
    in
    (* 1st pass = interpret function definitions to terms *)
    debug_terms "FROM SMT MODEL" terms;
    (* 2nd pass = evaluate prover variables using type coercions and
       fields for record types *)
    let terms = eval pinfo env terms in
    debug_terms "AFTER EVALUATION" terms;
    (* 3rd pass = cleanup (remove not evaluated prover variables,
       convert concrete epsilon terms to records / integers for
       projections of integer range types) *)
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
      | FromModelToTerm.E_parsing msg ->
          Format.fprintf fmt
            "Error@ while@ parsing@ SMT@ model@ from@ model@ definition@ to@ \
             term:@ %s"
            msg
      | FromModelToTerm.E_concrete_syntax msg ->
          Format.fprintf fmt
            "Mismatch@ error@ between@ term@ and@ concrete@ syntax:@ %s"
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
              (fun n ((ls, oloc, attrs), t) ->
                (* the printer may add/update attributes *)
                let attrs =
                  Ident.Sattr.union attrs
                    (Mstr.find_def Ident.Sattr.empty n pinfo.Printer.set_str) in
                    (* Concrete terms are computed in check_ce.ml *)
                create_model_element ~value:t ~concrete_value:concrete_undefined
                  ~oloc ~attrs ~lsymbol:ls)
              terms))

let () =
  register_model_parser "smtv2" parse
    ~desc:"Parser@ for@ the@ model@ of@ SMT@ solvers."
