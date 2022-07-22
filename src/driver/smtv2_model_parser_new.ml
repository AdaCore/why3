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
open Smtv2_model_defs_new

let debug = Debug.register_flag "model_parser_new"
  ~desc:"Print@ debugging@ messages@ about@ parsing@ \
         the@ SMTv2@ model@ for@ counterexamples."

module FromSexp = struct

  open Sexp

  let is_name_start = function
    | '_' | 'a'..'z' | 'A'..'Z'
    | '@' | '#' | '$' -> true
    | _ -> false

  let is_quoted s = String.length s > 2 && s.[0] = '|' && s.[String.length s-1] = '|'
  let get_quoted s = String.sub s 1 (String.length s-2)

  let is_string s = String.length s >= 2 && s.[0] = '"' && s.[String.length s-1] = '"'
  let get_string s = String.sub s 1 (String.length s-2)

  let rec pp_sexp fmt = function
    | Atom s -> Format.pp_print_string fmt s
    | List l -> Format.fprintf fmt "@[@[<hv2>(%a@])@]" Pp.(print_list space pp_sexp) l

  let string_of_sexp = Format.asprintf "%a" pp_sexp

  exception E of sexp * string

  let error sexp s = raise (E (sexp, s))
  let atom_error a s = raise (E (Atom a, s))

  let atom f = function
    | Atom s -> f s
    | sexp -> error sexp "atom"

  let list f = function
    | List l -> List.map f l
    | Atom _ as sexp -> error sexp "list"

  let string = function
    | Atom s when is_string s -> get_string s
    | sexp -> error sexp "string"

  let bool = atom bool_of_string

  let int = atom int_of_string

  let bigint = atom BigInt.of_string

  let constant_int = atom @@ fun s ->
    try BigInt.of_string ("0b"^Strings.remove_prefix "#b" s) with _ ->
    try BigInt.of_string ("0x"^Strings.remove_prefix "#x" s) with _ ->
    try BigInt.of_string s with _ ->
      atom_error s "constant_int"

  let minus_constant_int = function
    | List [Atom "-"; i] as sexp -> (
        try
          let i' = atom BigInt.of_string i in
          BigInt.minus i'
        with _ -> error sexp "minus_constant_int" )
    | sexp -> error sexp "minus_constant_int"

  let constant_int sexp =
    try constant_int sexp with _ ->
    try minus_constant_int sexp with _ ->
      error sexp "constant_int"

  let constant_dec = atom @@ fun s ->
    try
      Scanf.sscanf s "%[^.].%s"
        (fun s1 s2 ->
           let i1 = BigInt.of_string s1 and i2 = BigInt.of_string s2 in
           (i1, i2))
    with _ -> atom_error s "constant_dec"

  let minus_constant_dec = function
    | List [Atom "-"; d] ->
        let d1, d2 = constant_dec d in
        (BigInt.minus d1, d2)
    | sexp -> error sexp "minus_constant_dec"

  let constant_dec sexp =
    try constant_dec sexp with _ ->
    try minus_constant_dec sexp with _ ->
      error sexp "constant_dec"

  let constant_fraction = function
    | List [Atom "/"; n1; n2] ->
        let n1, n2 =
          try
            constant_int n1, constant_int n2
          with _ ->
            let d11, d12 = constant_dec n1 and d21, d22 = constant_dec n2 in
            assert BigInt.(eq d12 zero && eq d22 zero);
            d11, d21 in
        (n1, n2)
    | sexp -> error sexp "constant_fraction"

  let bv_int = atom @@ fun s ->
    try BigInt.of_string (Strings.remove_prefix "bv" s) with _ ->
      atom_error s "bv_int"

  let constant_bv_bin = function
    | Atom s -> (
        try
          let s' = Strings.remove_prefix "#b" s in
          let v = BigInt.of_string ("0b"^s') in
          let l = String.length s' in
          (v, l)
        with _ -> atom_error s "constant_bv_bin" )
    | sexp -> error sexp "constant_bv_bin"

  let constant_bv_hex = function
    | Atom s -> (
        try
          let s' = Strings.remove_prefix "#x" s in
          let v = BigInt.of_string ("0x"^s') in
          let l = String.length s' * 4 in
          (v, l)
        with _ -> atom_error s "constant_bv_hex" )
    | sexp -> error sexp "constant_bv_hex"

  let constant_bv_dec = function
    | List [Atom "_"; n; l] ->
        (bv_int n, int l)
    | sexp -> error sexp "constant_bv_dec"

  let constant_bv sexp =
    try constant_bv_dec sexp with _ ->
    try constant_bv_hex sexp with _ ->
    try constant_bv_bin sexp with _ ->
      error sexp "constant_bv"

(*
  let constant_float = function
    | List [Atom "_"; Atom "+zero"; n1; n2] ->
        ignore (bigint n1, bigint n2); Plus_zero
    | List [Atom "_"; Atom "-zero"; n1; n2] ->
        ignore (bigint n1, bigint n2); Minus_zero
    | List [Atom "_"; Atom "+oo"; n1; n2] ->
        ignore (bigint n1, bigint n2); Plus_infinity
    | List [Atom "_"; Atom "-oo"; n1; n2] ->
        ignore (bigint n1, bigint n2); Minus_infinity
    | List [Atom "_"; Atom "NaN"; n1; n2] ->
        ignore (bigint n1, bigint n2); Not_a_number
    | List [Atom "fp"; sign; exp; mant] ->
        let sign = constant_bv sign and exp = constant_bv exp and mant = constant_bv mant in
        float_of_binary {sign; exp; mant}
    | sexp -> error sexp "constant_float"
  *)

  let constant sexp : constant =
    try Cint (constant_int sexp) with _ ->
    try Cdecimal (constant_dec sexp) with _ ->
    try Cfraction (constant_fraction sexp) with _ ->
    try Cbitvector (constant_bv sexp) with _ ->
    (*try Cfloat (constant_float sexp) with _ ->*) (* TODO_WIP *)
    try Cbool (bool sexp) with _ ->
    try Cstring (string sexp) with _ ->
      error sexp "constant"
  
  let symbol sexp : symbol = string_of_sexp sexp (* TODO_WIP *)

  let index sexp : index = error sexp "index"
  
  let identifier sexp : identifier = match sexp with
    | Atom _ -> Isymbol (symbol sexp)
    | List [Atom "_"; s; List idx] ->
        Iindexedsymbol (symbol s, List.map index idx)
    | sexp -> error sexp "identifier"

  let sort : sexp -> sort = function (* TODO_WIP *)
    | Atom "String" -> Sstring
    | Atom "Int" -> Sint
    | Atom "Real" -> Sreal
    | Atom "Bool" -> Sbool
    | sexp -> error sexp "sort"
  
  let qualified_identifier sexp : qual_identifier = match sexp with
    | Atom _ -> Qident (identifier sexp)
    | List [Atom "as"; id; s] ->
        Qannotident (identifier id, sort s)
    | sexp -> error sexp "qualified_identifier"

  let arg = function
    | List [n; s] -> symbol n, sort s
    | sexp -> error sexp "arg"

  let rec term sexp =
    try Tconst (constant sexp) with _ ->
    try application sexp with _ ->
    (*try Tarray (array sexp) with _ ->*) (* TODO_WIP *)
    try ite sexp with _ ->
    try let_term sexp with _ ->
      Tunparsed (string_of_sexp sexp)

  and ite = function
    | List [Atom "ite"; t1; t2; t3] ->
        Tite (term t1, term t2, term t3)
    | sexp -> error sexp "ite"

  and let_term = function
    | List [Atom "let"; List bs; t] ->
        Tlet (List.map var_binding bs, term t)
    | sexp -> error sexp "let_term"

  and var_binding = function
    | List [Atom s; t] -> symbol (Atom s), term t
    | sexp -> error sexp "var_binding"

  and application = function
    | List (qual_id :: ts) ->
        Tapply (qualified_identifier qual_id, List.map term ts)
    | sexp -> error sexp "application"

  let decl = function
    | List [Atom "define-fun"; Atom n; args; res; body] ->
        let res = sort res in
        let args = list arg args and body = term body in
        Some (n, Dfunction (args, res, body))
    | _ -> None

  let is_model_decl = function Atom "define-fun" -> true | _ -> false

  let model sexp =
    if sexp = [] then None else
    let decls, rest = match sexp with
      | List (Atom "model" :: decls) :: rest -> decls, rest
      | List decls :: rest when List.exists (Sexp.exists is_model_decl) decls ->
          decls, rest
      | _ -> failwith "Cannot read S-expression as model: model not first" in
    if List.exists (Sexp.exists is_model_decl) rest then
      failwith
        "Cannot read S-expression as model: next model not separated \
         (missing separator in driver?)";
    Some (Mstr.of_list (Lists.map_filter decl decls))
end

(*
****************************************************************
**   Parser
****************************************************************
*)

exception Smtv2_model_parsing_error of string

let () =
  Exn_printer.register
    (fun fmt exn -> match exn with
        | Smtv2_model_parsing_error msg ->
            Format.fprintf fmt "Error@ while@ reading@ SMT@ model:@ %s" msg
        | _ -> raise exn)

let get_model_string input =
  let nr = Re.Str.regexp "^)+" in
  let res = Re.Str.search_backward nr input (String.length input) in
  String.sub input 0 (res + String.length (Re.Str.matched_string input))

let fix_CVC18_bug_on_float_constants =
  let r = Re.Str.regexp "\\((fp #b[01] #b[01]+ #b[01]+\\)" in
  fun s -> Re.Str.global_replace r "\\1)" s

let parse_sexps str =
  Debug.dprintf debug "[parse_sexps] model_string = %s@." str;
  let lexbuf = Lexing.from_string str in
  try
    Sexp.read_list lexbuf
  with Sexp.Error ->
    let msg = Format.sprintf "Cannot parse as S-expression at character %d"
                (Lexing.lexeme_start lexbuf) in
    (* workaround for CVC4 1.8 bug in printing float constants *)
    let str = fix_CVC18_bug_on_float_constants str in
    let lexbuf = Lexing.from_string str in
    try
      Sexp.read_list lexbuf
    with Sexp.Error ->
      raise (Smtv2_model_parsing_error msg)

let model_of_sexps sexps =
  try
    Opt.get_def Mstr.empty (FromSexp.model sexps)
  with FromSexp.E (sexp', s) ->
    let msg = Format.asprintf "Cannot read the following S-expression as %s: %a"
        s FromSexp.pp_sexp sexp' in
    raise (Smtv2_model_parsing_error msg)

let smt_type_to_ty = function
  | Sstring -> Ty.ty_str
  | Sint -> Ty.ty_int
  | Sreal -> Ty.ty_real
  | Sbool -> Ty.ty_bool
  | _ -> Ty.ty_str (* TODO_WIP *)

let rec smt_term_to_term = function
  | Tconst (Cint bigint) ->
      t_const (Constant.int_const bigint) Ty.ty_int
  | Tite (b,t1,t2) ->
      t_if (smt_term_to_term b) (smt_term_to_term t1) (smt_term_to_term t2)
  | _ -> t_bool_true

let interpret_def_to_term ls oloc attrs def =
  match def with
  | Dfunction (args, res, body) ->
      let vslist =
        List.map
          (fun (symbol, sort) ->
            let name = Ident.id_fresh symbol in
            create_vsymbol name (smt_type_to_ty sort))
          args in
      let t = smt_term_to_term body in
      t_lambda vslist [] t
  | _ -> t_bool_true

let terms_of_defs (* TODO_WIP *)
    (pinfo: Printer.printing_info)
    (defs: Smtv2_model_defs_new.definition Mstr.t) =
  let qterms = pinfo.queried_terms in
  let _ = Mstr.iter
    (fun key (ls,_,_) ->
      Debug.dprintf debug "[queried_terms] key = %s, ls = %a@."
        key Pretty.print_ls ls)
    qterms in
  let terms =
    Mstr.fold
      (fun n def acc ->
        try
          let (ls,oloc,attrs) = Mstr.find n qterms in
          (ls, interpret_def_to_term ls oloc attrs def) :: acc
        with Not_found -> acc)
      defs
      [] in
  List.iter
    (fun (ls,t) ->
      Debug.dprintf debug "[terms_of_defs] ls = %a, t = %a@."
        Pretty.print_ls ls Pretty.print_term t)
    terms
  (* Mls.of_list terms *)

let parse pinfo input =
  match get_model_string input with
  | exception Not_found -> []
  | model_string ->
      let sexps = parse_sexps model_string in
      let defs = model_of_sexps sexps in
      let _ = terms_of_defs pinfo defs in (* TODO_WIP *)
      []

let () = Model_parser.register_model_parser "smtv2new" parse (* TODO_WIP *)
    ~desc:"Parser@ for@ the@ model@ of@ SMT@ solvers."
