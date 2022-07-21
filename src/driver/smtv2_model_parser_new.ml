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

module FromSexp = struct

  open Sexp
  open Smtv2_model_defs_new

  let rec pp_sexp fmt = function
    | Atom s -> Format.pp_print_string fmt s
    | List l -> Format.fprintf fmt "@[@[<hv2>(%a@])@]" Pp.(print_list space pp_sexp) l

  let string_of_sexp = Format.asprintf "%a" pp_sexp

  exception E of sexp * string

  let error sexp s = raise (E (sexp, s))

  let list f = function
    | List l -> List.map f l
    | Atom _ as sexp -> error sexp "list"
  
  let symbol sexp : symbol = string_of_sexp sexp (* TODO_WIP *)

  let index sexp : index = Idxsymbol (string_of_sexp sexp) (* TODO_WIP *)
  
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
    | List [n; iret] -> symbol n, sort iret
    | sexp -> error sexp "arg"

  let numeral_constant s = Cnumeral s (* TODO_WIP *)
  let decimal_constant s = Cdecimal (s, s) (* TODO_WIP *)
  let hexadecimal_constant s = Chexadecimal s (* TODO_WIP *)
  let binary_constant s = Cbinary s (* TODO_WIP *)
  let string_constant s = Cstring s (* TODO_WIP *)

  let constant sexp : spec_constant = match sexp with
    | Atom s ->
      begin
        try numeral_constant s with _  ->
        try decimal_constant s with _  ->
        try hexadecimal_constant s with _  ->
        try binary_constant s with _  ->
        try string_constant s with _  ->
          error sexp "constant"
      end
    | _ -> error sexp "constant"

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
    | List [Atom "define-fun"; Atom n; al; iret; t] ->
        let iret = sort iret in
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

let parse pm input =
  match get_model_string input with
  | exception Not_found -> []
  | model_string ->
      let sexps = parse_sexps model_string in
      let defs = model_of_sexps sexps in
      [] (* TODO_WIP *)

let () = Model_parser.register_model_parser "smtv2new" parse (* TODO_WIP *)
    ~desc:"Parser@ for@ the@ model@ of@ SMT@ solvers."
