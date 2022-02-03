(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Wstdlib

module FromSexp = struct

  open Model_parser
  open Sexp
  open Smtv2_model_defs

  let is_name_start = function
    | '_' | 'a'..'z' | 'A'..'Z'
    | '@' | '#' | '$' -> true
    | _ -> false


  (* Quoted symbols and strings retain delimiter (| and ') in Sexp parser *)

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

  let model_int = atom @@ fun s ->
    let v =
      try BigInt.of_string ("0b"^Strings.remove_prefix "#b" s) with _ ->
      try BigInt.of_string ("0x"^Strings.remove_prefix "#x" s) with _ ->
      try BigInt.of_string s with _ ->
        atom_error s "model_int" in
    { int_value= v; int_verbatim= s }

  let minus_model_int = function
    | List [Atom "-"; i] as sexp -> (
        try
          let i' = atom BigInt.of_string i in
          {int_value= BigInt.minus i'; int_verbatim= "-"^string_of_sexp i}
        with _ -> error sexp "minus_model_int" )
    | sexp -> error sexp "minus_model_int"

  let model_int sexp =
    try model_int sexp with _ ->
    try minus_model_int sexp with _ ->
      error sexp "model_int"

  let model_dec = atom @@ fun s ->
    try
      Scanf.sscanf s "%[^.].%s"
        (fun s1 s2 ->
           let i1 = BigInt.of_string s1 and i2 = BigInt.of_string s2 in
           {dec_int= i1; dec_frac= i2; dec_verbatim= s})
    with _ -> atom_error s "model_dec"

  let minus_model_dec = function
    | List [Atom "-"; d] ->
        let d = model_dec d in
        {dec_int= BigInt.minus d.dec_int; dec_frac= d.dec_frac; dec_verbatim= "-"^d.dec_verbatim}
    | sexp -> error sexp "minus_model_dec"

  let model_dec sexp =
    try model_dec sexp with _ ->
    try minus_model_dec sexp with _ ->
      error sexp "model_dec"

  let model_fraction = function
    | List [Atom "/"; n1; n2] as sexp ->
        let n1, n2 =
          try
            let n1 = model_int n1 and n2 = model_int n2 in
            n1.int_value, n2.int_value
          with _ ->
            let d1 = model_dec n1 and d2 = model_dec n2 in
            assert BigInt.(eq d1.dec_frac zero && eq d2.dec_frac zero);
            d1.dec_int, d2.dec_int in
        { frac_nom= n1; frac_den= n2; frac_verbatim= string_of_sexp sexp }
    | sexp -> error sexp "model_fraction"

  let bv_int = atom @@ fun s ->
    try BigInt.of_string (Strings.remove_prefix "bv" s) with _ ->
      atom_error s "bv_int"

  let model_bv_bin = function
    | Atom s -> (
        try
          let s' = Strings.remove_prefix "#b" s in
          let v = BigInt.of_string ("0b"^s') in
          let l = String.length s' in
          { bv_value= v; bv_length= l; bv_verbatim= s }
        with _ -> atom_error s "model_bv_bin" )
    | sexp -> error sexp "model_bv_bin"

  let model_bv_hex = function
    | Atom s -> (
        try
          let s' = Strings.remove_prefix "#x" s in
          let v = BigInt.of_string ("0x"^s') in
          let l = String.length s' * 4 in
          { bv_value= v; bv_length= l; bv_verbatim= s }
        with _ -> atom_error s "model_bv_hex" )
    | sexp -> error sexp "model_bv_hex"

  let model_bv_dec = function
    | List [Atom "_"; n; l] as sexp ->
        { bv_value= bv_int n; bv_length= int l; bv_verbatim= string_of_sexp sexp }
    | sexp -> error sexp "model_bv_dec"

  let model_bv sexp =
    try model_bv_dec sexp with _ ->
    try model_bv_hex sexp with _ ->
    try model_bv_bin sexp with _ ->
      error sexp "model_bv"

  let model_float = function
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
        let sign = model_bv sign and exp = model_bv exp and mant = model_bv mant in
        float_of_binary {sign; exp; mant}
    | sexp -> error sexp "model_float"

  let name = function
    | Atom s when s = "" || is_name_start s.[0] -> s
    | Atom s when is_quoted s -> get_quoted s
    | List [Atom "_"; Atom "BitVec"; _]
    | List [Atom "_"; Atom "extract"; _; _]
    | List [Atom "_"; Atom "FloatingPoint"; _; _] ->
        (* Cases adopted from parse_smtv2_model_parser.mly. TODO check *)
        ""
    | sexp -> error sexp "name"

  let var_name = function
    | Atom s | List [Atom "as"; Atom s; _] as sexp ->
        if s = "" || is_name_start s.[0] then s else
        if is_quoted s then get_quoted s else
          error sexp "var"
    | sexp -> error sexp "var"

  let ireturn_type sexp =
    try Some (name sexp) with _ ->
      None

  let arg = function
    | List [n; iret] -> name n, ireturn_type iret
    | sexp -> error sexp "arg"

  let prover_name name =
    if Strings.has_prefix "@" name then
      let left = String.index name '_' + 1 in
      let right = String.rindex name '_' in
      let ty = String.sub name left (right - left) in
      Some (try Strings.(remove_prefix "(" (remove_suffix ")" ty)) with _ -> ty)
    else match String.split_on_char '!' name with
      | [ty;_;_] -> Some ty
      | _ -> None

  let var name =
    match prover_name name with
    | Some ty -> Tprover_var (ty, name)
    | None -> Tvar name

  let rec term sexp =
    try Tconst (value sexp) with _ ->
    try var (var_name sexp) with _ ->
    try Tarray (array sexp) with _ ->
    try ite sexp with _ ->
    try let_term sexp with _ ->
    try as_array sexp with _ ->
    try Tapply (application sexp) with _ ->
      error sexp "term"

  and value sexp =
    try Integer (model_int sexp) with _ ->
    try Decimal (model_dec sexp) with _ ->
    try Fraction (model_fraction sexp) with _ ->
    try Bitvector (model_bv sexp) with _ ->
    try Boolean (bool sexp) with _ ->
    (* try ignore (boolean_expression sexp); Unparsed "boolean_expression" with _ -> *)
    try String (string sexp) with _ ->
    try Float (model_float sexp) with _ ->
      error sexp "value"

  and ite = function
    | List [Atom "ite"; t1; t2; t3] ->
        Tite (term t1, term t2, term t3)
    | sexp -> error sexp "ite"

  and let_term = function
    | List [Atom "let"; List bs; t] ->
        let aux = function
          | List [Atom s; t] -> s, term t
          | sexp -> error sexp "binding" in
        Tlet (List.map aux bs, term t)
    | sexp -> error sexp "let_term"

  and as_array = function
    | List [Atom "_"; Atom "as-array"; n] ->
        Tto_array (Tvar (name n))
    | sexp -> error sexp "as_array"

  and application = function
    | List (Atom n :: ts) ->
        n, List.map term ts
    | List (List _ as l :: ts) ->
        string_of_sexp l, List.map term ts
    | sexp -> error sexp "application"

  and array = function
    | List [List [Atom "as"; Atom "const"; iret]; t] ->
        ignore (ireturn_type iret);
        Aconst (term t)
    | List [Atom "store"; x; t1; t2] ->
        let a = try array x with _ -> Avar (name x) in
        Astore (a, term t1, term t2)
    | List [Atom "ARRAY_LAMBDA"; List [Atom "LAMBDA"; al; t]] ->
        ignore (list arg al);
        Aconst (term t) (* case not used *)
    | sexp -> error sexp "array"

  let decl = function
    | List [Atom "define-fun"; Atom n; al; iret; t] ->
        let iret = ireturn_type iret in
        let al = list arg al and t = term t in
        Some (n, Dfunction (al, iret, t))
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

(* Parses the model returned by CVC4 and Z3. *)

(*
***************************************************************
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
  (*    let r = Re.Str.regexp "unknown\\|sat\\|\\(I don't know.*\\)" in
        ignore (Re.Str.search_forward r input 0);
        let match_end = Re.Str.match_end () in*)
  let nr = Re.Str.regexp "^)+" in
  let res = Re.Str.search_backward nr input (String.length input) in
  String.sub input 0 (res + String.length (Re.Str.matched_string input))

let parse_sexps str =
  let lexbuf = Lexing.from_string str in
  try
    Sexp.read_list lexbuf
  with Sexp.Error ->
    let msg = Format.sprintf "Cannot parse as S-expression at character %d"
        (Lexing.lexeme_start lexbuf) in
    raise (Smtv2_model_parsing_error msg)

let model_of_sexps sexps =
  try
    Opt.get_def Mstr.empty (FromSexp.model sexps)
  with FromSexp.E (sexp', s) ->
    let msg = Format.asprintf "Cannot read the following S-expression as %s: %a"
        s FromSexp.pp_sexp sexp' in
    raise (Smtv2_model_parsing_error msg)

(* Parses the model returned by CVC4, Z3 or Alt-ergo.
   Returns the list of pairs term - value *)
(* For Alt-ergo the output is not the same and we
   match on "I don't know". But we also need to begin
   parsing on a fresh new line ".*" ensures it *)
let parse pm input =
  match get_model_string input with
  | exception Not_found -> []
  | model_string ->
      let sexps = parse_sexps model_string in
      let defs = model_of_sexps sexps in
      let mvs = Collect_data_model.create_list pm defs in
      List.rev
        (Mstr.values
           (Mstr.mapi (fun name value ->
                let attrs = Mstr.find_def Ident.Sattr.empty name pm.Printer.set_str in
                Model_parser.create_model_element ~name ~value ~attrs) mvs))

let () = Model_parser.register_model_parser "smtv2" parse
    ~desc:"Parser@ for@ the@ model@ of@ cv4@ and@ z3."
