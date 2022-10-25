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
    String.length str > 0 && (str.[0] == '@' || str.[0] == '.')

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

  let constant_int = function
    | Atom s -> (
        try BigInt.of_string s with _ -> atom_error s "constant_int")
    | sexp -> error sexp "constant_int"

  let minus_constant_int = function
    | List [ Atom "-"; i ] as sexp -> (
        try BigInt.minus (atom BigInt.of_string i)
        with _ -> error sexp "minus_constant_int")
    | sexp -> error sexp "minus_constant_int"

  let constant_int sexp =
    try constant_int sexp
    with _ -> (
      try minus_constant_int sexp with _ -> error sexp "constant_int")

  let constant_dec =
    atom @@ fun s ->
    try
      Scanf.sscanf s "%[^.].%s" (fun s1 s2 ->
          let i1 = BigInt.of_string s1 and i2 = BigInt.of_string s2 in
          (i1, i2))
    with _ -> atom_error s "constant_dec"

  let minus_constant_dec = function
    | List [ Atom "-"; d ] ->
        let d1, d2 = constant_dec d in
        (BigInt.minus d1, d2)
    | sexp -> error sexp "minus_constant_dec"

  let constant_dec sexp =
    try constant_dec sexp
    with _ -> (
      try minus_constant_dec sexp with _ -> error sexp "constant_dec")

  let constant_fraction = function
    | List [ Atom "/"; n1; n2 ] ->
        let n1, n2 =
          try (constant_int n1, constant_int n2)
          with _ ->
            let d11, d12 = constant_dec n1 and d21, d22 = constant_dec n2 in
            assert (BigInt.(eq d12 zero && eq d22 zero));
            (d11, d21)
        in
        (n1, n2)
    | sexp -> error sexp "constant_fraction"

  let constant_bv_bin = function
    | Atom s -> (
        try
          let s' = Strings.remove_prefix "#b" s in
          let v = BigInt.of_string ("0b" ^ s') in
          let l = String.length s' in
          (v, l)
        with _ -> atom_error s "constant_bv_bin")
    | sexp -> error sexp "constant_bv_bin"

  let constant_bv_hex = function
    | Atom s -> (
        try
          let s' = Strings.remove_prefix "#x" s in
          let v = BigInt.of_string ("0x" ^ s') in
          let l = String.length s' * 4 in
          (v, l)
        with _ -> atom_error s "constant_bv_hex")
    | sexp -> error sexp "constant_bv_hex"

  let constant_bv_dec = function
    | List [ Atom "_"; Atom n; l ] as sexp -> (
        try (BigInt.of_string (Strings.remove_prefix "bv" n), int l)
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
          try Cfraction (constant_fraction sexp)
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
    match sexp with
    | Atom "=" -> Isymbol (S "=")
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

  let get_type_from_var_name name =
    (* we try to infer the type from [name], for example:
        - infer the type int32 from the name @uc_int32_1
        - infer the type ref int32 from the name |@uc_(ref int32)_0|ref!val!1
        - infer the type ref from the name ref!val!0 *)
    let name = if is_quoted name then get_quoted name else name in
    let opt_name =
      if Strings.has_prefix "@" name then
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
    | [] -> None
    | [sexp] -> Some sexp
    | sexps -> Some (List sexps)

  let qualified_identifier sexp : qual_identifier =
    match sexp with
    | Atom n -> (
        match get_type_from_var_name n with
        | None -> Qident (identifier sexp)
        | Some ty_sexp -> Qannotident (identifier sexp, sort ty_sexp))
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
    | List [ List [ Atom "as"; Atom "const"; List [ Atom "Array"; s1; s2] ]; t ] ->
        Tarray (sort s1, sort s2, {
          array_indices = [];
          array_others = term t;
        })
    (* TODO_WIP *)
    (*| List [ Atom "_"; Atom "as-array"; n ] ->
        Tvar (Qannotident (identifier n, Sarray))*)
    | List [ Atom "store"; x; t1; t2 ] ->
        let a = try array x with _ -> error sexp "array" (*Tvar (Qannotident (identifier x, Sarray))*) in
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

  let error s = raise (E s)

  type env = {
    (* Prover variables. *)
    mutable prover_vars : vsymbol Mstr.t;
    (* Bound variables in the body of a function definiton. *)
    mutable bound_vars : vsymbol Mstr.t;
    (* Constructors from [pinfo.constructors]. *)
    mutable constructors : lsymbol Mstr.t;
    (* Known types from lsymbols in [pinfo.queried_terms]. *)
    mutable known_types : Ty.ty list;
    (* Known types from lsymbols in [pinfo.queried_terms]. *)
    mutable inferred_types : (sort * Ty.ty) list;
    (* Queried terms [pinfo.queried_terms]. *)
    queried_terms : lsymbol Mstr.t;
  }

  let get_opt_type oty = match oty with None -> Ty.ty_bool | Some ty -> ty
  let is_type_matching_string ty n =
    match n with
    | S str | Sprover str -> (
      match ty.Ty.ty_node with
      | Ty.Tyvar tv -> String.equal str tv.Ty.tv_name.id_string
      | Ty.Tyapp (ts,ts_args) ->
          (* TODO_WIP also check ts_args *)
          String.equal str ts.Ty.ts_name.id_string)
  let is_no_arg_constructor n constructors =
    match Mstr.find_opt n constructors with
    | Some ls -> ls.ls_args == []
    | None -> false

  let rec smt_sort_to_ty env s =
    Debug.dprintf debug "[smt_sort_to_ty] s = %a@." print_sort s;
    match s with
    | Sstring -> Ty.ty_str
    | Sint -> Ty.ty_int
    | Sreal -> Ty.ty_real
    | Sbool -> Ty.ty_bool
    | Sbitvec n ->
      begin try
        let s,ty =
          List.find
            (function | (Sbitvec n',_) when n=n' -> true | _ -> false)
            env.inferred_types
        in
        ty
      with Not_found -> raise UnknownType
      end
    | Sarray (s1, s2) ->
        Ty.ty_app Ty.ts_func [ smt_sort_to_ty env s1; smt_sort_to_ty env s2 ]
    | Ssimple (Isymbol n) ->
      begin try
        List.find (fun x -> is_type_matching_string x n) env.known_types
      with Not_found -> error "TODO_WIP smt_sort_to_ty unknown Ssimple symbol"
      end
    | Smultiple (Isymbol n, sorts) ->
      begin try
        List.find (fun x -> is_type_matching_string x n) env.known_types
      with Not_found -> error "TODO_WIP smt_sort_to_ty unknown Smultiple symbol"
      end
    | _ -> error "TODO_WIP smt_sort_to_ty"

  (* TODO_WIP refactoring *)
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
            with Not_found -> error "TODO_WIP cannot infer the type of the variable"
          in
          t_var vs
    | Qident (Isymbol (Sprover n)) ->
        let vs =
          try Mstr.find n env.prover_vars
          with Not_found -> error "TODO_WIP cannot infer the type of the prover variable"
        in
        t_var vs
    | Qannotident (Isymbol (S n), s) ->
        if is_no_arg_constructor n env.constructors then
          raise NoArgConstructor
        else
          let vs =
            try
              let vs = Mstr.find n env.bound_vars in
              if Ty.ty_equal vs.vs_ty (smt_sort_to_ty env s) then vs
              else error "TODO_WIP type mismatch"
            with Not_found ->
              create_vsymbol (Ident.id_fresh n) (smt_sort_to_ty env s)
          in
          t_var vs
    | Qannotident (Isymbol (Sprover n), s) ->
        let vs_ty = smt_sort_to_ty env s in
        let vs =
          try
            let vs = Mstr.find n env.prover_vars in
            if Ty.ty_equal vs.vs_ty vs_ty then vs
            else error "TODO_WIP type mismatch for prover variable"
          with Not_found -> (
            let vs = create_vsymbol (Ident.id_fresh n) vs_ty in
            env.prover_vars <- Mstr.add n vs env.prover_vars;
            vs)
        in
        t_var vs
    | _ -> error "TODO_WIP_qual_id_to_vsymbol"

  let constant_to_term env c =
    Debug.dprintf debug "[constant_to_term] c = %a@." print_constant c;
    match c with
    | Cint bigint -> t_const (Constant.int_const bigint) Ty.ty_int
    | Cdecimal (d1,d2) -> error "TODO_WIP Cdecimal"
    | Cfraction _ -> error "TODO_WIP Cfraction"
    | Cbitvector (bigint, n) ->
      begin try
        let _,ty =
          List.find
            (function | (Sbitvec n',_) when n=n' -> true | _ -> false)
            env.inferred_types
        in
        t_const (Constant.int_const bigint) ty
      with Not_found -> error "TODO_WIP Cbitvector"
      end
    | Cfloat _ -> error "TODO_WIP Cfloat"
    | Cbool b -> if b then t_true_bool else t_true_bool
    | Cstring str -> t_const (Constant.string_const str) Ty.ty_str

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
    | Tlet (vs, t) -> error "TODO_WIP Tlet"
    | Tarray (s1, s2, a) -> array_to_term env s1 s2 a
    | Tunparsed s -> error "TODO_WIP Tunparsed"

  (* TODO_WIP refactoring *)
  and apply_to_term env qid ts =
    Debug.dprintf debug "[apply_to_term] qid = %a@ ts = %a@."
      print_qualified_identifier qid
      Pp.(print_list space print_term)
      ts;
    match (qid, ts) with
    | Qident (Isymbol (S "=")), [ t1; t2 ] ->
        let t1' = term_to_term env t1 in
        let t2' = term_to_term env t2 in
        let t' = (* TODO_WIP to be fixed *)
          t_app
            (create_lsymbol
              (Ident.id_fresh "=")
              [get_opt_type t1'.t_ty; get_opt_type t2'.t_ty]
              (Some Ty.ty_bool))
            [t1'; t2']
            (Some Ty.ty_bool)
        in
        t'
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
    | Qident (Isymbol (S "not")), [ t ] -> t_bool_not (term_to_term env t)
    | Qident (Isymbol (S n)), ts | Qident (Isymbol (Sprover n)), ts ->
        let ts' = List.map (term_to_term env) ts in
        let ts'_ty =
          try List.map (fun t -> Opt.get t.t_ty) ts'
          with _ ->
            error "TODO_WIP apply_to_term error with types of arguments"
        in
        let ls =
          try Mstr.find n env.constructors
          with Not_found -> error "TODO_WIP unknown lsymbol"
        in
        t_app ls ts' ls.ls_value
        (* TODO_WIP check that types are consistent *)
    | Qannotident (Isymbol (S n), s), ts | Qannotident (Isymbol (Sprover n), s), ts ->
        let ts' = List.map (term_to_term env) ts in
        let ts'_ty =
          try List.map (fun t -> Opt.get t.t_ty) ts'
          with _ ->
            error "TODO_WIP apply_to_term error with types of arguments"
        in
        let ls =
          create_lsymbol (Ident.id_fresh n) ts'_ty
            (Some (smt_sort_to_ty env s))
        in
        t_app ls ts' ls.ls_value
        (* TODO_WIP check that types are consistent *)
    | _ -> error "TODO_WIP apply_to_term"

  and array_to_term env s1 s2 elts =
    Debug.dprintf debug "[array_to_term] a = %a@." print_array elts;
    let vs_arg =
      create_vsymbol (Ident.id_fresh "x") (smt_sort_to_ty env s1)
    in
    let mk_case key value t =
      let key = term_to_term env key in
      let value = term_to_term env value in
      t_if (t_equ (t_var vs_arg) key) value t
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
    else error "TODO_WIP type error"

  let interpret_fun_def_to_term env ls oloc attrs (args,res,body) =
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
    Debug.dprintf debug "[interpret_fun_def_to_term] attrs = %a@."
      Pretty.print_attrs
      attrs;
    env.bound_vars <- Mstr.empty;
    let check_sort_type s ty =
      match smt_sort_to_ty env s with
      | s_ty ->
        Debug.dprintf debug "[check_sort_type] s = %a, ty = %a, s_ty = %a@."
          print_sort s
          Pretty.print_ty ty
          Pretty.print_ty s_ty;
        Ty.ty_equal ty s_ty
      | exception UnknownType ->
        env.inferred_types <- (s,ty) :: env.inferred_types;
        true
    in
    let t =
      try
        if
          check_sort_type res (get_opt_type ls.ls_value) &&
            List.fold_left2
              (fun acc (_,arg) ls_arg -> check_sort_type arg ls_arg)
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
        else error "TODO_WIP type mismatch"
      with Invalid_argument _ -> error "TODO_WIP function arity mismatch"
    in
    Debug.dprintf debug "[interpret_fun_def_to_term] t = %a@." Pretty.print_term
      t;
    Debug.dprintf debug "-----------------------------@.";
    t

  (* [eval_var] is false if variables should not be evaluated *)
  let rec eval_term env eval_var ty_coercions ty_fields t =
    Debug.dprintf debug "[eval_term] eval_var = %b, t = %a@."
      eval_var
      Pretty.print_term t;
    match t.t_node with
    | Tvar vs when eval_var && (List.mem vs (Mstr.values env.prover_vars)) -> (
        match t.t_ty with
        | Some ty -> (
          (* first search if there exists some type coercions for [ty] *)
          match Ty.Mty.find_def [] ty ty_coercions with
          | [] -> (
              (* if no coercions, search if [ty] is associated to some fields *)
              match Ty.Mty.find_def [] ty ty_fields with
              | [] -> t
              | fields ->
                  let term_of_field (_, (ls',t')) =
                    let vs_list', _, t' = t_open_lambda t' in
                    let vs' = match vs_list' with
                      | [vs'] -> vs'
                      | _ -> error "TODO_WIP field with not exactly one argument" in
                    (* TODO_WIP if t' is again a prover variable, we should recurse on that *)
                    eval_term env false ty_fields ty_fields (t_subst_single vs' (t_var vs) t') in
                  let ty_of_field (_, (ls',t')) =
                    let vs_list', _, t' = t_open_lambda t' in
                    match vs_list' with
                    | [vs'] -> Opt.get t'.t_ty
                    | _ -> error "TODO_WIP field with not exactly one argument" in
                  let ls_array = (* TODO_WIP temporary lsymbol when no constructor *)
                    create_lsymbol
                      (Ident.id_fresh "arraymk")
                      (List.map ty_of_field fields)
                      (Some ty) in
                  t_app ls_array (List.map term_of_field fields) (Some ty))
          | coercions ->
            (* create a fresh vsymbol for the variable bound by the epsilon term *)
            let x = create_vsymbol (Ident.id_fresh "x") ty in
            let term_of_coercion (str',(ls',t')) =
              let vs_list', _, t' = t_open_lambda t' in
              let vs' = match vs_list' with
                | [vs'] -> vs'
                | _ ->
                    error "TODO_WIP type coercion with not exactly one argument"
              in
              (* TODO_WIP if t' is again a prover variable, we should recurse on that *)
              let t' = eval_term env false ty_coercions ty_fields (t_subst_single vs' (t_var vs) t') in
              (* substitute [vs] by this new variable in the body [t'] of the function
                  defining the type coercion *)
              let t' = t_subst_single vs' (t_var x) t' in
              (* construct the formula to be used in the epsilon term *)
              t_equ (t_app ls' [t_var x] ls'.ls_value) t'
            in
            let f = t_and_l (List.map term_of_coercion coercions) in
            (* replace [t] by [eps x. f] *)
            t_eps_close x f)
        | _ -> t)
    | Tapp (ls, [t1;t2]) when (ls.ls_name.id_string.[0] == '=') -> (* TODO_WIP fix builtin lsymbol for equality *)
      if
        t_equal
          (eval_term env eval_var ty_coercions ty_fields t1)
          (eval_term env eval_var ty_coercions ty_fields t2)
      then
        t_true_bool
      else (
        match t1.t_node,t2.t_node with
        | Tvar v1, Tvar v2
            when List.mem v1 (Mstr.values env.prover_vars) &&
                 List.mem v2 (Mstr.values env.prover_vars) ->
          (* Distinct prover variables are not equal *)
          if vs_equal v1 v2 then t_true_bool else t_false_bool
        | _ ->
          let ts = List.map (eval_term env eval_var ty_coercions ty_fields) [t1;t2] in
          t_app ls ts ls.ls_value)
    | Tapp (ls, ts) ->
      let ts = List.map (eval_term env eval_var ty_coercions ty_fields) ts in
      t_app ls ts ls.ls_value
    | Tif (b,t1,t2) -> (
      match (eval_term env eval_var ty_coercions ty_fields b).t_node with
      | Ttrue -> eval_term env eval_var ty_coercions ty_fields t1
      | Tfalse -> eval_term env eval_var ty_coercions ty_fields t2
      | _ ->
        let t1 = eval_term env eval_var ty_coercions ty_fields t1 in
        let t2 = eval_term env eval_var ty_coercions ty_fields t2 in
        t_if b t1 t2
    )
    | Tlet _ -> t
    | Tcase _ -> t
    | Teps tb ->
      let vs,t = Term.t_open_bound tb in
      t_eps_close vs (eval_term env eval_var ty_coercions ty_fields t)
    | Tquant (q,tq) ->
      let vsl,trig,t' = t_open_quant tq in
      let t' = eval_term env eval_var ty_coercions ty_fields t' in
      t_quant q (t_close_quant vsl trig t')
    | Tbinop (op,t1,t2) ->
      let t1 = eval_term env eval_var ty_coercions ty_fields t1 in
      let t2 = eval_term env eval_var ty_coercions ty_fields t2 in
      t_binary_bool op t1 t2
    | Tnot t' -> (
      let t' = eval_term env eval_var ty_coercions ty_fields t' in
      match t'.t_node with (* TODO_WIP is it really the place to do such simplifications? *)
      | Ttrue -> t_bool_false
      | Tfalse -> t_bool_true
      | _ -> t_bool_not t')
    | _ -> t

  let eval (pinfo : Printer.printing_info) env terms =
    Mstr.iter
      (fun key value -> Debug.dprintf debug "[eval] prover_var = %s, vs = %a@."
        key Pretty.print_vs value)
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
                (fun str ((ls',_,_), t) ->
                  if ls_equal ls ls' then Some (ls,t) else None)
                terms))
            (Sls.elements sls))
        )
      pinfo.type_coercions in
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
                (fun str ((ls',_,_), t) ->
                  if ls_equal ls ls' then Some (ls,t) else None)
                terms))
            lls)
        )
      pinfo.type_fields in
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
      (fun str ((ls,oloc,attrs),t) -> ((ls,oloc,attrs), eval_term env true ty_coercions ty_fields t))
      terms


  let get_terms (pinfo : Printer.printing_info)
      (fun_defs : Smtv2_model_defs.function_def Mstr.t) =
    let qterms = pinfo.queried_terms in
    Mstr.iter
      (fun key (ls, _, attrs) ->
        Debug.dprintf debug "[queried_terms] key = %s, ls = %a, ls.ls_value = %a@." key
          Pretty.print_ls ls
          (Pp.print_option Pretty.print_ty) ls.ls_value;
        Debug.dprintf debug "[queried_terms] key = %s, attr = %a@." key
          Pretty.print_attrs attrs)
      qterms;
    let records = pinfo.list_records in
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
      Mstr.mapi (fun _ -> List.map select) pinfo.list_records in
    Mstr.iter
      (fun key l ->
        List.iter
          (fun elem ->
            Debug.dprintf debug "[list_records] key = %s, field = %s@."
              key elem)
          l)
      records;
    let fields = pinfo.list_fields in
    Mstr.iter
      (fun key f ->
        Debug.dprintf debug "[list_fields] key = %s, field = %s@."
          key f.Ident.id_string)
      fields;
    let projections = pinfo.list_projections in
    Mstr.iter
      (fun key f ->
        Debug.dprintf debug "[list_projections] key = %s, field = %s@."
          key f.Ident.id_string)
      projections;
    let constructors = pinfo.constructors in
    Mstr.iter
      (fun key ls ->
        Debug.dprintf debug "[constructors] key = %s, ls = %a/%d@."
          key
          Pretty.print_ls ls
          (List.length ls.ls_args))
      constructors;
    let env = {
      prover_vars = Mstr.empty;
      bound_vars = Mstr.empty;
      constructors = constructors;
      known_types = [];
      inferred_types = [];
      queried_terms = Mstr.map (fun (ls,_,_) -> ls) qterms;
    } in
    (* Compute known types from lsymbols in [qterms] *)
    let types_from_qterms =
      List.flatten (
        List.map
          (fun (ls,_,_) ->
            match ls.ls_value with
            | None -> ls.ls_args
            | Some ty -> ty :: ls.ls_args)
          (Mstr.values qterms))
    in
    (* Initialize the environment with [types_from_qterms] while avoiding duplicates *)
    env.known_types <-
      List.fold_left
        (fun acc ty ->
          match List.find_opt (fun ty' -> Ty.ty_equal ty ty') acc with
          | None -> ty::acc
          | Some _ -> acc)
        [] types_from_qterms;
    Debug.dprintf debug "[known_types] ty = %a"
      (Pp.print_list Pp.comma Pretty.print_ty) env.known_types;
    let terms =
      Mstr.mapi_filter
        (fun n def ->
          match Mstr.find n qterms with
          | (ls, oloc, attrs) ->
            Some ((ls,oloc,attrs), interpret_fun_def_to_term env ls oloc attrs def)
          | exception Not_found -> (
            Debug.dprintf debug "No term for %s@." n; None))
        fun_defs
    in
    Mstr.iter
      (fun n ((ls,_,_), t) ->
        Debug.dprintf debug
          "[get_terms] n = %s, ls = %a, t = %a@.t.t_ty = %a@.t.t_attrs = %a@.t.t_loc = \
           %a@."
          n
          Pretty.print_ls ls Pretty.print_term t
          (Pp.print_option Pretty.print_ty)
          t.t_ty Pretty.print_attrs t.t_attrs
          (Pp.print_option Pretty.print_loc_as_attribute)
          t.t_loc)
      terms;
    eval pinfo env terms
end

(*
****************************************************************
**   Parser
****************************************************************
*)

let () =
  Exn_printer.register (* TODO_WIP more info in messages *) (fun fmt exn ->
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
            (fun n ((ls,oloc,attrs),t) ->
              let name = Ident.get_model_trace_string ~name:(ls.ls_name.id_string) ~attrs in
              Model_parser.create_model_element
                ~name ~value:t ~oloc ~lsymbol:ls ~attrs)
            terms))

let () =
  Model_parser.register_model_parser "smtv2" parse
    ~desc:"Parser@ for@ the@ model@ of@ SMT@ solvers."
