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

let debug =
  Debug.register_flag "smtv2_parser"
    ~desc:
      "Print@ debugging@ messages@ about@ parsing@ the@ SMTv2@ model@ for@ \
       counterexamples."

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

module FromSexpToModel = struct
  open Sexp

  exception E of sexp * string

  let error sexp s = raise (E (sexp, s))
  let atom_error a s = raise (E (Atom a, s))

  let is_simple_symbol str =
    String.length str > 0 && (match str.[0] with
    | '_' | 'a' .. 'z' | 'A' .. 'Z' | '#' | '$' -> true
    | _ -> false)

  let is_prover_symbol str =
    (* as defined in SMT-LIB Standard *)
    ( String.length str > 0 && (str.[0] == '@' || str.[0] == '.') )
    ||
    (* special cases with Z3 prover *)
    ( match String.split_on_char '!' str with
      | [_;"val";_] -> true
      | _ -> false )

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
      try negative_constant_int sexp
      with _ -> error sexp "constant_int")

  let constant_dec s =
    try Scanf.sscanf s "%[^.].%s" (fun s1 s2 -> (s1,s2))
    with _ -> atom_error s "constant_dec"

  let constant_dec = function
    | Atom s ->
      let s1,s2 = constant_dec s in
      (false, s1, s2)
    | List [ Atom "-"; Atom s] ->
      let s1,s2 = constant_dec s in
      (true, s1, s2)
    | sexp -> error sexp "constant_dec"

  let constant_fraction ~neg sexp =
    let positive_constant_int_fraction = function
      | Atom s -> (
          try (false, BigInt.of_string s) with _ -> atom_error s "constant_int")
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
      let (neg,c) =
        try positive_constant_int_fraction sexp
        with _ -> (
          try negative_constant_int_fraction sexp
          with _ -> error sexp "constant_int_fraction")
      in (neg, BigInt.to_string c, zero)
    in
    let constant_int_or_dec_fraction n =
      try constant_int_fraction n
      with _ -> constant_dec n
    in
    let neg_constant_real (neg,s1,s2) = (not neg, s1, s2) in
    match sexp with
    | List [ Atom "/"; n1; n2 ] ->
      let r1 = constant_int_or_dec_fraction n1 in
      let r2 = constant_int_or_dec_fraction n2 in
      if neg then Cfraction (neg_constant_real r1, r2)
      else Cfraction (r1, r2)
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
                  try Cstring (string sexp)
                  with _ -> error sexp "constant"))))))
    in
    Tconst cst

  let symbol : sexp -> symbol = function
    | Atom s when is_prover_symbol s -> Sprover s
    | Atom s when is_simple_symbol s -> S s
    | Atom s when is_quoted s ->
        let s' = get_quoted s in
        if is_prover_symbol s' then
          Sprover s'
        else
          S s'
    | sexp -> error sexp "symbol"

  let index sexp : index =
    try Idxnumeral (bigint sexp)
    with _ -> (try Idxsymbol (symbol sexp) with _ -> error sexp "index")

  let identifier sexp : identifier =
    let builtins = [ "="; "*"; "+"; "<="; ">="; "<"; ">"; ] in
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
    let opt_name =
      if Strings.has_prefix "@" name || Strings.has_prefix "." name then
        try
          let left = String.index name '_' + 1 in
          let right = String.rindex name '_' in
          Some (String.sub name left (right - left))
        with _ -> None
      else
        begin match String.split_on_char '!' name with
        | [ty;_;_] -> Some ty
        | _ -> None
        end
    in
    match FromStringToSexp.parse_string (Opt.get_def  "" opt_name) with
    | [] -> atom_error name "get_type_from_prover_variable"
    | [sexp] -> sexp
    | sexps -> List sexps

  let qualified_identifier sexp : qual_identifier =
    match sexp with
    | Atom _ -> (
      let id = identifier sexp in
      match id with
      | Isymbol (Sprover n') | Iindexedsymbol (Sprover n', _) ->
        let ty_sexp = get_type_from_prover_variable n' in
        Qannotident (id, sort ty_sexp)
      | Isymbol _ | Iindexedsymbol _ -> Qident (id)
    )
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
          try let_term sexp
          with _ -> (
            try array sexp
            with _ -> (
              try application sexp with _ -> Tunparsed (string_of_sexp sexp))))))

  and ite = function
    | List [ Atom "ite"; t1; t2; t3 ] -> Tite (term t1, term t2, term t3)
    | sexp -> error sexp "ite"

  and let_term = function
    | List [ Atom "let"; List bs; t ] -> Tlet (List.map var_binding bs, term t)
    | sexp -> error sexp "let_term"

  and var_binding = function
    | List [ Atom s; t ] -> (symbol (Atom s), term t)
    | sexp -> error sexp "var_binding"

  and application = function
    | List (qual_id :: ts) ->
        Tapply (qualified_identifier qual_id, List.map term ts)
    | sexp -> error sexp "application"

  and array sexp = match sexp with
      (* "_ as-array" not supported because not associated to sorts for indices/values*)
    | List [ List [ Atom "as"; Atom "const"; List [ Atom "Array"; s1; s2] ]; t ] ->
        Tarray (sort s1, sort s2, {
          array_indices = [];
          array_others = term t;
        })
    | List [ Atom "store"; x; t1; t2 ] ->
        let a = try array x with _ -> error sexp "array" in
        begin match a with
        | Tarray (s1, s2, elts) -> Tarray (s1, s2, {
          array_indices = (term t1, term t2) :: elts.array_indices;
          array_others = elts.array_others
        })
        | _ -> error sexp "array"
        end
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

module FromModelToTerm = struct
  exception E of string
  exception NoArgConstructor
  exception UnknownType
  exception NoBuiltinSymbol

  let error fmt =
    Format.kasprintf (fun msg -> raise (E (msg))) fmt

  type env = {
    (* Why3 environment, used to retrieve builtin lsymbols *)
    why3_env : Env.env;
    (* Variables, useful for evaluation. *)
    mutable vars : string Mvs.t;
    (* Prover variables, may have the same name if the sort is different. *)
    mutable prover_vars : (vsymbol Ty.Mty.t) Mstr.t;
    (* Bound variables in the body of a function definiton. *)
    mutable bound_vars : vsymbol Mstr.t;
    (* Constructors from [pinfo.Printer.constructors]. *)
    constructors : lsymbol Mstr.t;
    (* Inferred types from lsymbols in [pinfo.Printer.queried_terms]. *)
    mutable inferred_types : (sort * Ty.ty) list;
    (* Queried terms [pinfo.Printer.queried_terms]. *)
    queried_terms : lsymbol Mstr.t;
    mutable cached_prover_vars : Term.term Mvs.t;
    mutable cached_consts : Term.term Mvs.t;
  }

  let get_opt_type oty = match oty with None -> Ty.ty_bool | Some ty -> ty

  let is_no_arg_constructor n constructors =
    match Mstr.find_opt n constructors with
    | Some ls -> ls.ls_args == []
    | None -> false

  let rec smt_sort_to_ty ?(update=false) env s =
    Debug.dprintf debug "[smt_sort_to_ty] update = %b / s = %a@." update print_sort s;
    let matching_sort f =
      match List.find_all (fun (s',_) -> f s') env.inferred_types with
      | [] ->
        if update then raise UnknownType
        else error "No match in inferred_types for sort %a@." print_sort s
      | [(_,ty)] -> ty
      | _ -> error "Multiple matched in inferred_types for sort %a@." print_sort s
    in
    match s with
    | Sstring -> Ty.ty_str
    | Sint -> Ty.ty_int
    | Sreal -> Ty.ty_real
    | Sbool -> Ty.ty_bool
    | Sarray (s1, s2) ->
      begin match List.find_all (fun (s',_) -> sort_equal s s') env.inferred_types with
      | [] ->
        if update then raise UnknownType
        else Ty.ty_app Ty.ts_func [ smt_sort_to_ty env s1; smt_sort_to_ty env s2 ]
      | [(_,ty)] -> ty
      | _ -> error "No match in inferred_types for array sort %a@." print_sort s
      end
    | Sroundingmode | Sfloatingpoint _
    | Sbitvec _ | Ssimple _ | Smultiple _ -> matching_sort (sort_equal s)
    | _ -> error "Multiple matched in inferred_types for array sort %a@." print_sort s

  let qual_id_to_term env qid =
    Debug.dprintf debug "[qual_id_to_term] qid = %a@."
      print_qualified_identifier qid;
    match qid with
    | Qident (Isymbol (S n)) ->
        if is_no_arg_constructor n env.constructors then
          raise NoArgConstructor
        else
          let vs =
            try Mstr.find n env.bound_vars
            with Not_found ->
              error "No variable in bound_vars matching qualified identifier %a@."
                print_qualified_identifier qid
          in
          t_var vs
    | Qident (Isymbol (Sprover n)) ->
        begin match Ty.Mty.values (Mstr.find n env.prover_vars) with
        | [] | exception Not_found ->
          error "No variable in prover_vars matching qualified identifier %a@."
            print_qualified_identifier qid
        | [vs] -> t_var vs
        | _::_::_ ->
          error "Multiple variables in prover_vars matching qualified identifier %a@."
            print_qualified_identifier qid
        end
    | Qannotident (Isymbol (S n), s) ->
        if is_no_arg_constructor n env.constructors then
          raise NoArgConstructor
        else
          let vs_ty = smt_sort_to_ty env s in
          let vs =
            try
              let vs = Mstr.find n env.bound_vars in
              if Ty.ty_equal vs.vs_ty vs_ty then vs
              else
                error "Type %a of variable %a does not match sort %a@."
                  Pretty.print_ty vs.vs_ty
                  Pretty.print_vs vs
                  print_sort s
            with Not_found ->
              let vs = create_vsymbol (Ident.id_fresh n) vs_ty in
              env.vars <- Mvs.add vs n env.vars;
              vs
          in
          t_var vs
    | Qannotident (Isymbol (Sprover n), s) ->
        let vs_ty = smt_sort_to_ty env s in
        let new_vs = create_vsymbol (Ident.id_fresh n) vs_ty in
        begin try
          let mvs = Mstr.find n env.prover_vars in
          begin
            match Ty.Mty.find vs_ty mvs with
            | vs -> t_var vs
            | exception Not_found ->
              Debug.dprintf debug "[updating prover_vars] new_vs = %a / vs_ty = %a@."
                Pretty.print_vs new_vs Pretty.print_ty vs_ty;
              env.prover_vars <- Mstr.add n (Ty.Mty.add vs_ty new_vs mvs) env.prover_vars;
              t_var new_vs
          end
        with Not_found ->
          Debug.dprintf debug "[updating prover_vars] new_vs = %a / vs_ty = %a@."
            Pretty.print_vs new_vs Pretty.print_ty vs_ty;
          env.prover_vars <- Mstr.add n (Ty.Mty.add vs_ty new_vs Ty.Mty.empty) env.prover_vars;
          t_var new_vs
        end
    | _ ->
      error "Could not interpret qualified identifier %a@."
        print_qualified_identifier qid

  exception Float_MinusZero
  exception Float_PlusZero
  exception Float_NaN
  exception Float_Infinity
  exception Float_Error

  let pad_with_zeros width s =
    let filled =
      let len = width - String.length s in
      if len <= 0 then "" else String.make len '0' in
    filled ^ s
    
  let float_of_binary fp =
    match fp with
    | Fplusinfinity | Fminusinfinity -> raise Float_Infinity
    | Fpluszero -> raise Float_PlusZero
    | Fminuszero -> raise Float_MinusZero
    | Fnan -> raise Float_NaN
    | Fnumber {sign; exp; mant} ->
      let exp_bias = BigInt.pred (BigInt.pow_int_pos 2 (exp.bv_length - 1)) in
      let exp_max = BigInt.pred (BigInt.pow_int_pos 2 exp.bv_length) in
      let frac_len = (* Length of the hexadecimal representation (after the ".") *)
        if mant.bv_length mod 4 = 0
        then mant.bv_length / 4
        else (mant.bv_length / 4) + 1 in
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
          if adjust = 4 then
            mant.bv_value (* No adjustment needed *)
          else
            BigInt.mul (BigInt.pow_int_pos 2 adjust) mant.bv_value
        else
          mant.bv_value in
      let frac = pad_with_zeros frac_len (Format.sprintf "%x" (BigInt.to_int frac)) in
      if BigInt.eq exp.bv_value BigInt.zero then (* subnormals and zero *)
        (* Case for zero *)
        if BigInt.eq mant.bv_value BigInt.zero then
          if is_neg then raise Float_MinusZero else raise Float_PlusZero
        else
          (* Subnormals *)
          let exp = (BigInt.pred exp_bias) in
          let hex = Format.asprintf "%t0x0.%sp-%s"
              (fun fmt -> if is_neg then Pp.string fmt "-")
              frac (BigInt.to_string exp) in
          Debug.dprintf debug "[float_of_binary] %a --> %s@."
            print_constant (Cfloat fp)
            hex;
          (is_neg, "0", frac, Some (String.concat "" ["-";BigInt.to_string exp]))
      else if BigInt.eq exp.bv_value exp_max (* infinities and NaN *) then
        if BigInt.eq mant.bv_value BigInt.zero then
          raise Float_Infinity
        else raise Float_NaN
      else
        let exp = BigInt.sub exp.bv_value exp_bias in
        let hex = Format.asprintf "%t0x1.%sp%s"
            (fun fmt -> if is_neg then Pp.string fmt "-")
            frac (BigInt.to_string exp) in
        Debug.dprintf debug "[float_of_binary] %a --> %s@."
          print_constant (Cfloat fp)
          hex;
        (is_neg, "1", frac, Some (BigInt.to_string exp))

  let constant_to_term env c =
    Debug.dprintf debug "[constant_to_term] c = %a@." print_constant c;
    match c with
    | Cint bigint -> t_const (Constant.int_const bigint) Ty.ty_int
    | Cdecimal (neg,s1,s2) ->
      t_const (Constant.real_const_from_string ~radix:10 ~neg:neg ~int:s1 ~frac:s2 ~exp:None) Ty.ty_real
    | Cfraction ((neg,s1,s2),(neg',s1',s2')) ->
      begin try
        let t = t_const (Constant.real_const_from_string ~radix:10 ~neg:neg ~int:s1 ~frac:s2 ~exp:None) Ty.ty_real in
        let t' = t_const (Constant.real_const_from_string ~radix:10 ~neg:neg' ~int:s1' ~frac:s2' ~exp:None) Ty.ty_real in
        let th = Env.read_theory env.why3_env ["real"] "Real" in
        let div_ls = Theory.ns_find_ls th.Theory.th_export [Ident.op_infix "/"] in
        t_app div_ls [t;t'] div_ls.ls_value
      with _ ->
        error "Could not interpret constant %a as a fraction@." print_constant c
      end
    | Cbitvector { bv_value=bigint; bv_length=n; _ } ->
      begin try
        let _,ty =
          List.find
            (function | (Sbitvec n',_) when n=n' -> true | _ -> false)
            env.inferred_types
        in
        t_const (Constant.int_const bigint) ty
      with Not_found ->
        error "No matching type found in inferred_type for bitvector constant %a@."
          print_constant c
      end
    | Cfloat fp ->
      begin try
        let sort,ty =
          List.find
            (function | (Sfloatingpoint _,_) -> true | _ -> false)
            env.inferred_types
        in
        let float_lib = match sort with
        | Sfloatingpoint (a,b) -> "Float" ^ (string_of_int (a+b))
        | _ -> assert false
        in
        begin try
          let (neg,s1,s2,exp) = float_of_binary fp in
          t_const (Constant.real_const_from_string ~radix:16 ~neg ~int:s1 ~frac:s2 ~exp) ty
        with
          | Float_MinusZero ->
            t_const (Constant.real_const_from_string ~radix:10 ~neg:true ~int:"0" ~frac:"0" ~exp:None) ty
          | Float_PlusZero ->
            t_const (Constant.real_const_from_string ~radix:10 ~neg:false ~int:"0" ~frac:"0" ~exp:None) ty
          | Float_NaN ->
            let is_nan_ls =
              try
                let th = Env.read_theory env.why3_env ["ieee_float"] float_lib in
                Theory.ns_find_ls th.Theory.th_export ["is_nan"]
              with _ -> error "No lsymbol found in theory for is_nan@."
            in
            let x = create_vsymbol (Ident.id_fresh "x") ty in
            let f = t_app is_nan_ls [t_var x] None in
            t_eps_close x f
          | Float_Infinity ->
            let is_infinite_ls =
              try
                let th = Env.read_theory env.why3_env ["ieee_float"] float_lib in
                Theory.ns_find_ls th.Theory.th_export ["is_infinite"]
              with _ -> error "No lsymbol found in theory for is_infinite@."
            in
            let x = create_vsymbol (Ident.id_fresh "x") ty in
            let f = t_app is_infinite_ls [t_var x] None in
            t_eps_close x f
          | Float_Error ->
            error "Error while interpreting float constant %a@."
              print_constant c
        end
      with Not_found ->
        error "No matching type found in inferred_type for float constant %a@."
          print_constant c
      end
    | Cbool b -> if b then t_true_bool else t_false_bool
    | Cstring str -> t_const (Constant.string_const str) Ty.ty_str

  let find_builtin_lsymbol env n ts =
    let (path, theory, ident) =
      match ts with
      | [t1;t2] ->
        begin match t1.t_ty, t2.t_ty with
        | Some ty1, Some ty2
            when Ty.ty_equal ty1 Ty.ty_int && Ty.ty_equal ty2 Ty.ty_int ->
          begin match n with
          | "+" -> ("int", "Int", Ident.op_infix "+")
          | "-" -> ("int", "Int", Ident.op_infix "-")
          | "*" -> ("int", "Int", Ident.op_infix "*")
          | "<" -> ("int", "Int", Ident.op_infix "<")
          | ">" -> ("int", "Int", Ident.op_infix ">")
          | "<=" -> ("int", "Int", Ident.op_infix "<=")
          | ">=" -> ("int", "Int", Ident.op_infix ">=")
          | _ -> raise NoBuiltinSymbol
          end
        | Some ty1, Some ty2
            when Ty.ty_equal ty1 Ty.ty_real && Ty.ty_equal ty2 Ty.ty_real ->
          begin match n with
          | "+" -> ("real", "Real", Ident.op_infix "+")
          | "-" -> ("real", "Real", Ident.op_infix "-")
          | "*" -> ("real", "Real", Ident.op_infix "*")
          | "/" -> ("real", "Real", Ident.op_infix "/")
          | "<" -> ("real", "Real", Ident.op_infix "<")
          | ">" -> ("real", "Real", Ident.op_infix ">")
          | "<=" -> ("real", "Real", Ident.op_infix "<=")
          | ">=" -> ("real", "Real", Ident.op_infix ">=")
          | _ -> raise NoBuiltinSymbol
          end
        | _ -> raise NoBuiltinSymbol
        end
      | _ -> raise NoBuiltinSymbol
    in
    let th = Env.read_theory env.why3_env [path] theory in
    let ls = Theory.ns_find_ls th.Theory.th_export [ident] in
    Debug.dprintf debug "ls = %a@." Pretty.print_ls ls;
    ls

  let rec term_to_term env t =
    Debug.dprintf debug "[term_to_term] t = %a@." print_term t;
    match t with
    | Tconst c -> constant_to_term env c
    | Tvar qid ->
        begin try
          qual_id_to_term env qid
        with
        | NoArgConstructor -> apply_to_term env qid []
        end
    | Tite (b, t1, t2) ->
        t_if (term_to_term env b) (term_to_term env t1) (term_to_term env t2)
    | Tapply (qid, ts) -> apply_to_term env qid ts
    | Tarray (s1, s2, a) -> array_to_term env s1 s2 a
    | _ -> error "Could not interpret term %a@." print_term t

  and apply_to_term env qid ts =
    Debug.dprintf debug "[apply_to_term] qid = %a@ ts = %a@."
      print_qualified_identifier qid
      Pp.(print_list space print_term)
      ts;
    match (qid, ts) with
    | Qident (Isymbol (S "=")), [ t1; t2 ] ->
        let t1' = term_to_term env t1 in
        let t2' = term_to_term env t2 in
        t_equ t1' t2'
    | Qident (Isymbol (S "or")), hd::tl ->
        List.fold_left
          (fun t t' -> t_binary_bool Term.Tor t (term_to_term env t'))
          (term_to_term env hd)
          tl
    | Qident (Isymbol (S "and")), hd::tl ->
        List.fold_left
          (fun t t' -> t_binary_bool Term.Tand t (term_to_term env t'))
          (term_to_term env hd)
          tl
    | Qident (Isymbol (S "not")), [ t ] -> t_not_bool (term_to_term env t)
    | Qident (Isymbol (S n)), ts | Qident (Isymbol (Sprover n)), ts ->
        let ts' = List.map (term_to_term env) ts in
        let ls =
          try Mstr.find n env.constructors
          with _ -> (
            try find_builtin_lsymbol env n ts'
            with NoBuiltinSymbol ->
              error "No lsymbol found for qualified identifier %a@."
                print_qualified_identifier qid
          )
        in
        begin
          try t_app ls ts' ls.ls_value
          with _ ->
            error "Cannot apply lsymbol %a to terms (%a)@."
              Pretty.print_ls ls
              (Pp.print_list Pp.comma Pretty.print_term) ts'
        end
    | Qannotident (Isymbol (S n), s), ts | Qannotident (Isymbol (Sprover n), s), ts ->
        let ts' = List.map (term_to_term env) ts in
        let ts'_ty =
          try List.map (fun t -> Opt.get t.t_ty) ts'
          with _ ->
            error "Arguments of %a should have a type@." print_qualified_identifier qid
        in
        let ls =
          create_lsymbol (Ident.id_fresh n) ts'_ty
            (Some (smt_sort_to_ty env s))
        in
        begin
          try t_app ls ts' ls.ls_value
          with _ ->
            error "Cannot apply lsymbol %a to terms (%a)@."
              Pretty.print_ls ls
              (Pp.print_list Pp.comma Pretty.print_term) ts'
        end
    | _ -> error "Could not interpret %a@." print_qualified_identifier qid

  and array_to_term env s1 s2 elts =
    Debug.dprintf debug "[array_to_term] a = %a@." print_array elts;
    let ty1 = smt_sort_to_ty env s1 in
    let ty2 = smt_sort_to_ty env s2 in
    let vs_arg = create_vsymbol (Ident.id_fresh "x") ty1 in
    let mk_case key value t =
      let key = term_to_term env key in
      let value = term_to_term env value in
      if Ty.oty_equal key.t_ty (Some ty1) && Ty.oty_equal value.t_ty (Some ty2)
      then
        t_if (t_equ (t_var vs_arg) key) value t
      else
        error "Type %a for sort %a of array keys and/or type %a for sort %a of array values do not match@."
          (Pp.print_option Pretty.print_ty) key.t_ty print_sort s1
          (Pp.print_option Pretty.print_ty) value.t_ty print_sort s2
    in
    let a = List.fold_left
      (fun t (key,value) -> mk_case key value t)
      (term_to_term env elts.array_others)
      elts.array_indices
    in
    t_lambda [ vs_arg ] [] a

  let smt_term_to_term env t s =
    Debug.dprintf debug "[smt_term_to_term] s = %a, t = %a@."
      print_sort s print_term t;
    let t' = term_to_term env t in
    let s' = smt_sort_to_ty env s in
    Debug.dprintf debug "[smt_term_to_term] s' = %a, t' = %a, t'.t_ty = %a@."
      Pretty.print_ty s'
      Pretty.print_term t'
      (Pp.print_option Pretty.print_ty) t'.t_ty;
    if Ty.ty_equal s' (get_opt_type t'.t_ty) then t'
    else
      error "Type %a for sort %a and type %a for term %a do not match@."
        Pretty.print_ty s' print_sort s
        Pretty.print_ty (get_opt_type t'.t_ty) print_term t

  let interpret_fun_def_to_term env ls (args,res,body) =
    Debug.dprintf debug "-----------------------------@.";
    Debug.dprintf debug "[interpret_fun_def_to_term] fun_def = %a@."
      print_function_def (args,res,body);
    Debug.dprintf debug "[interpret_fun_def_to_term] ls = %a@."
      Pretty.print_ls ls;
    Debug.dprintf debug "[interpret_fun_def_to_term] ls.ls_value = %a@."
      (Pp.print_option Pretty.print_ty)
      ls.ls_value;
    List.iter
      (Debug.dprintf debug "[interpret_fun_def_to_term] ls.ls_args = %a@."
         Pretty.print_ty)
      ls.ls_args;
    env.bound_vars <- Mstr.empty;
    let check_or_update_inferred_types s ty =
      try Ty.ty_equal ty (smt_sort_to_ty ~update:true env s)
      with UnknownType -> (
        Debug.dprintf debug "[updating inferred_types] s = %a, ty = %a@."
          print_sort s
          Pretty.print_ty ty;
        env.inferred_types <- (s,ty) :: env.inferred_types;
        true)
    in
    let t =
      try
        if
          check_or_update_inferred_types res (get_opt_type ls.ls_value) &&
            List.fold_left2
              (fun acc (_,arg) ls_arg ->
                acc && check_or_update_inferred_types arg ls_arg)
              true args ls.ls_args
        then  (
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
          t_lambda (Mstr.values env.bound_vars) [] (smt_term_to_term env body res))
        else
          error "Type mismatch when interpreting %a with lsymbol %a@."
            print_function_def (args,res,body)
            Pretty.print_ls ls
      with Invalid_argument _ ->
        error "Function arity mismatch when interpreting %a with lsymbol %a@."
          print_function_def (args,res,body)
          Pretty.print_ls ls
    in
    Debug.dprintf debug "[interpret_fun_def_to_term] t = %a@." Pretty.print_term
      t;
    Debug.dprintf debug "-----------------------------@.";
    t

  let is_vs_in_prover_vars vs prover_vars =
    match
      List.find_all
        (fun mvs ->
          Ty.Mty.exists
            (fun ty vs' -> Ty.ty_equal ty vs.vs_ty && Term.vs_equal vs' vs) mvs)
        (Mstr.values prover_vars)
    with
    | [] -> false
    | [_] -> true
    | _ ->
      error "More than one matching vsymbol in prover_vars for %a@."
        Pretty.print_vs vs


  let rec eval_term env seen_prover_vars ty_coercions ty_fields terms t =
    match t.t_node with
    | Term.Tvar vs when List.mem vs seen_prover_vars ->
      Debug.dprintf debug "[eval_term] vs = %a in seen_prover_vars@."
        Pretty.print_vs vs;
      begin match Mvs.find_opt vs env.cached_prover_vars with
      | Some t_vs -> t_vs
      | None -> t
      end
    | Term.Tvar vs ->
      begin match Mvs.find_opt vs env.vars with
      | Some n ->
        Debug.dprintf debug "[eval_term] vs = %a in env.vars@."
          Pretty.print_vs vs;
        begin match Mvs.find_opt vs env.cached_consts with
        | Some t_vs -> t_vs
        | None ->
          begin match Mstr.find_opt n terms with
          | Some (_,t_vs) ->
            if Ty.ty_equal vs.vs_ty (get_opt_type t_vs.t_ty) then (
              env.cached_consts <- Mvs.add vs t_vs env.cached_consts;
              t_vs)
            else
              eval_term env seen_prover_vars ty_coercions ty_fields terms t_vs
          | None -> t
          end
        end
      | None ->
        if is_vs_in_prover_vars vs env.prover_vars
        then (
          Debug.dprintf debug "[eval_term] vs = %a in env.prover_vars@."
            Pretty.print_vs vs;
          let seen_prover_vars = vs :: seen_prover_vars in
          let create_epsilon_term ty l =
            (* create a fresh vsymbol for the variable bound by the epsilon term *)
            let x = create_vsymbol (Ident.id_fresh "x") ty in
            let aux (_, (ls',t')) =
              let vs_list', _, t' = t_open_lambda t' in
              let vs' = match vs_list' with
                | [vs'] -> vs'
                | _ ->
                  error "Only one variable expected when opening lambda-term %a"
                    Pretty.print_term t' in
              let t' =  eval_term env seen_prover_vars ty_fields ty_coercions terms (t_subst_single vs' (t_var vs) t') in
              (* substitute [vs] by this new variable in the body [t'] of the function
                  defining the type coercion *)
              let t' = t_subst_single vs' (t_var x) t' in
              (* construct the formula to be used in the epsilon term *)
              t_equ (t_app ls' [t_var x] ls'.ls_value) t'
            in
            let f = t_and_l (List.map aux l) in
            (* replace [t] by [eps x. f] *)
            t_eps_close x f
          in
          let res =
            match t.t_ty with
            | Some ty -> (
              (* first search if there exists some type coercions for [ty] *)
              match Ty.Mty.find_def [] ty ty_coercions with
              | [] -> (
                  (* if no coercions, search if [ty] is associated to some fields *)
                  match Ty.Mty.find_def [] ty ty_fields with
                  | [] -> t
                  | fields -> create_epsilon_term ty fields)
              | coercions -> create_epsilon_term ty coercions)
            | _ -> t
          in
          env.cached_prover_vars <- Mvs.add vs res env.cached_prover_vars;
          res)
        else t
      end
    | Term.Tapp (ls, [t1;t2])
        when String.equal ls.ls_name.Ident.id_string (Ident.op_infix "=") ->
      (* TODO_WIP fix builtin lsymbol for equality *)
      if
        t_equal
          (eval_term env seen_prover_vars ty_coercions ty_fields terms t1)
          (eval_term env seen_prover_vars ty_coercions ty_fields terms t2)
      then
        t_true_bool
      else (
        match t1.t_node,t2.t_node with
        | Term.Tvar v1, Term.Tvar v2
            when is_vs_in_prover_vars v1 env.prover_vars &&
            is_vs_in_prover_vars v2 env.prover_vars ->
          (* distinct prover variables are not equal *)
          if vs_equal v1 v2 then t_true_bool else t_false_bool
        | _ ->
          let ts = List.map (eval_term env seen_prover_vars ty_coercions ty_fields terms) [t1;t2] in
          t_app ls ts ls.ls_value)
    | Term.Tapp (ls, ts) ->
      let ts = List.map (eval_term env seen_prover_vars ty_coercions ty_fields terms) ts in
      t_app ls ts ls.ls_value
    | Term.Tif (b,t1,t2) -> (
      match (eval_term env seen_prover_vars ty_coercions ty_fields terms b).t_node with
      | Term.Ttrue -> eval_term env seen_prover_vars ty_coercions ty_fields terms t1
      | Term.Tfalse -> eval_term env seen_prover_vars ty_coercions ty_fields terms t2
      | _ ->
        let t1 = eval_term env seen_prover_vars ty_coercions ty_fields terms t1 in
        let t2 = eval_term env seen_prover_vars ty_coercions ty_fields terms t2 in
        t_if b t1 t2
    )
    | Term.Tlet _ -> t
    | Term.Tcase _ -> t
    | Term.Teps tb ->
      begin match Term.t_open_lambda t with
      | ([], _, _) ->
        let vs, t' = Term.t_open_bound tb in
        t_eps_close vs (eval_term env seen_prover_vars ty_coercions ty_fields terms t')
      | (vsl, trig, t') ->
        t_lambda vsl trig (eval_term env seen_prover_vars ty_coercions ty_fields terms t')
      end
    | Term.Tquant (q,tq) ->
      let vsl,trig,t' = t_open_quant tq in
      let t' = eval_term env seen_prover_vars ty_coercions ty_fields terms t' in
      t_quant q (t_close_quant vsl trig t')
    | Term.Tbinop (op,t1,t2) ->
      let t1 = eval_term env seen_prover_vars ty_coercions ty_fields terms t1 in
      let t2 = eval_term env seen_prover_vars ty_coercions ty_fields terms t2 in
      t_binary_bool op t1 t2
    | Term.Tnot t' -> (
      let t' = eval_term env seen_prover_vars ty_coercions ty_fields terms t' in
      match t'.t_node with
      | Term.Ttrue -> t_bool_false
      | Term.Tfalse -> t_bool_true
      | _ -> t_not_bool t')
    | _ -> t

  let eval (pinfo : Printer.printing_info) env terms =
    Mstr.iter
      (fun key value -> Debug.dprintf debug "[eval] prover_var = %s, vs = %a@."
        key (Pp.print_list Pp.space Pretty.print_vs) (Ty.Mty.values value))
      env.prover_vars;
    let ty_coercions =
      Ty.Mty.map (* for each set [sls] of lsymbols associated to a type *)
        (fun sls ->
          (* we construct a list of elements [(str,(ls,t))] retrieved
             from [terms] such that [ls] is in [sls]:
             for a given type [ty], it corresponds to all type coercions
             that can be applied to an object of type [ty] *)
          List.concat (List.map
            (fun ls -> Mstr.bindings (
              Mstr.mapi_filter
                (fun _ ((ls',_,_), t) ->
                  if ls_equal ls ls' then Some (ls,t) else None)
                terms))
            (Sls.elements sls))
        )
      pinfo.Printer.type_coercions in
    Ty.Mty.iter
      (fun key elt ->
        List.iter
          (fun (str,(ls,t)) ->
            Debug.dprintf debug "[ty_coercions] ty = %a, str=%s, ls = %a, t=%a@."
              Pretty.print_ty key
              str
              Pretty.print_ls ls
              Pretty.print_term t)
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
          List.concat (List.map
            (fun ls -> Mstr.bindings (
              Mstr.mapi_filter
                (fun _ ((ls',_,_), t) ->
                  if ls_equal ls ls' then Some (ls,t) else None)
                terms))
            lls)
        )
      pinfo.Printer.type_fields in
    Ty.Mty.iter
      (fun key elt ->
        List.iter
          (fun (str,(ls,t)) ->
            Debug.dprintf debug "[ty_fields] ty = %a, str=%s, ls = %a, t=%a@."
              Pretty.print_ty key
              str
              Pretty.print_ls ls
              Pretty.print_term t)
          elt)
      ty_fields;
    Mstr.mapi (* for each element in [terms], we try to evaluate [t]:
       - by applying type coercions for variables, when possible *)
      (fun _ ((ls,oloc,attrs),t) ->
        let t' = eval_term env [] ty_coercions ty_fields terms t in
        Debug.dprintf debug "[eval_term] t = %a / t' = %a@." Pretty.print_term t Pretty.print_term t';
        ((ls,oloc,attrs), t'))
      terms

  let clean env terms =
    Mstr.map_filter
      (fun ((ls,oloc,attr), t) ->
        Debug.dprintf debug "[clean] t = %a@." Pretty.print_term t;
        if Term.t_v_any
            (fun vs ->
              Debug.dprintf debug "[t_v_any] vs = %a@." Pretty.print_vs vs;
              is_vs_in_prover_vars vs env.prover_vars)
            t
        then None
        else Some ((ls,oloc,attr),t))
      terms

  let get_terms (pinfo : Printer.printing_info)
      (fun_defs : Smtv2_model_defs.function_def Mstr.t) =
    let qterms = pinfo.Printer.queried_terms in
    Mstr.iter
      (fun key (ls, _, attrs) ->
        Debug.dprintf debug "[queried_terms] key = %s, ls = %a, ls.ls_value = %a@." key
          Pretty.print_ls ls
          (Pp.print_option Pretty.print_ty) ls.ls_value;
        Debug.dprintf debug "[queried_terms] key = %s, attr = %a@." key
          Pretty.print_attrs attrs)
      qterms;
    let records = pinfo.Printer.list_records in
    Mstr.iter
      (fun key l ->
        List.iter
          (fun finfo ->
            Debug.dprintf debug "[list_records] key = %s, field_info_name = %s, field_info_trace = %s, field_info_ident = %a@."
              key
              finfo.Printer.field_name
              finfo.Printer.field_trace
              (Pp.print_option Pretty.print_id_attrs) finfo.Printer.field_ident)
          l)
      records;
    let records =
      let select finfo =
        if finfo.Printer.field_trace <> "" then finfo.Printer.field_trace else
          match finfo.Printer.field_ident with
          | Some id -> id.Ident.id_string
          | None -> finfo.Printer.field_name in
      Mstr.mapi (fun _ -> List.map select) pinfo.Printer.list_records in
    Mstr.iter
      (fun key l ->
        List.iter
          (fun elem ->
            Debug.dprintf debug "[list_records] key = %s, field = %s@."
              key elem)
          l)
      records;
    let fields = pinfo.Printer.list_fields in
    Mstr.iter
      (fun key f ->
        Debug.dprintf debug "[list_fields] key = %s, field = %s@."
          key f.Ident.id_string)
      fields;
    let projections = pinfo.Printer.list_projections in
    Mstr.iter
      (fun key f ->
        Debug.dprintf debug "[list_projections] key = %s, projection = %s@."
          key f.Ident.id_string)
      projections;
    let constructors = pinfo.Printer.constructors in
    Mstr.iter
      (fun key ls ->
        Debug.dprintf debug "[constructors] key = %s, ls = %a/%d@."
          key
          Pretty.print_ls ls
          (List.length ls.ls_args))
      constructors;
    let env = {
      why3_env = pinfo.Printer.why3_env;
      vars = Mvs.empty;
      prover_vars = Mstr.empty;
      bound_vars = Mstr.empty;
      constructors = constructors;
      inferred_types = [];
      queried_terms = Mstr.map (fun (ls,_,_) -> ls) qterms;
      cached_prover_vars = Mvs.empty;
      cached_consts = Mvs.empty;
    } in
    let terms =
      Mstr.mapi_filter
        (fun n def ->
          match Mstr.find n qterms with
          | (ls, oloc, attrs) ->
            begin try
              Some ((ls,oloc,attrs), interpret_fun_def_to_term env ls def)
            with
            | E str ->
              Debug.dprintf debug "Error while interpreting %s: %s@." n str;
              None
            | _ ->
              Debug.dprintf debug "Error while interpreting %s@." n;
              None
            end
          | exception Not_found -> (
            Debug.dprintf debug "No term for %s@." n; None))
        fun_defs
    in
    Mstr.iter
      (fun n ((ls,oloc,_), t) ->
        Debug.dprintf debug
          "[TERMS FROM SMT MODEL] n = %s, ls = %a, oloc = %a, t = %a@.t.t_ty = %a@."
          n
          Pretty.print_ls ls
          (Pp.print_option Pretty.print_loc_as_attribute) oloc
          Pretty.print_term t
          (Pp.print_option Pretty.print_ty) t.t_ty )
      terms;
    let terms = eval pinfo env terms in
    Mstr.iter
      (fun n ((ls,oloc,_), t) ->
        Debug.dprintf debug
          "[TERMS AFTER EVALUATION] n = %s, ls = %a, oloc = %a, t = %a@.t.t_ty = %a@."
          n
          Pretty.print_ls ls
          (Pp.print_option Pretty.print_loc_as_attribute) oloc
          Pretty.print_term t
          (Pp.print_option Pretty.print_ty) t.t_ty )
      terms;
    let terms = clean env terms in
    Mstr.iter
      (fun n ((ls,oloc,_), t) ->
        Debug.dprintf debug
          "[TERMS AFTER CLEANUP] n = %s, ls = %a, oloc = %a, t = %a@.t.t_ty = %a@."
          n
          Pretty.print_ls ls
          (Pp.print_option Pretty.print_loc_as_attribute) oloc
          Pretty.print_term t
          (Pp.print_option Pretty.print_ty) t.t_ty )
      terms;
    terms
end

(*
****************************************************************
**   Parser
****************************************************************
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
            (fun _ ((ls,oloc,attrs),t) ->
              let name = Ident.get_model_trace_string ~name:(ls.ls_name.Ident.id_string) ~attrs in
              Model_parser.create_model_element
                ~name ~value:t ~oloc ~lsymbol:ls ~attrs)
            terms))

let () =
  Model_parser.register_model_parser "smtv2" parse
    ~desc:"Parser@ for@ the@ model@ of@ SMT@ solvers."
