(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

module LatexInd (Conf: sig val prefix: string val flatten_applies : bool val comment_macros : bool end) = struct

  open Format
  open Why3
  open Ptree
  open Ident

  open Conf

  let sanitize =
    let my_char_to_alpha = function
      | '_' -> ""
      | c -> char_to_alpha c
    in
    sanitizer my_char_to_alpha my_char_to_alpha

  let sanitize_op = function
    | "<>" -> "\\neq"
    | "^" -> "\\string^"
    | "++" -> "\\mathbin{+\\mkern-10mu+}"
    | "<=" -> "\\le"
    | ">=" -> "\\ge"
    | s -> s

  (** Optionally extract trailing numbers and quotes, after an optional single or double
      underscore *)
  let split_base_suffixes str =
    try
      let re = Re.Str.regexp "_?_?\\([0-9]*\\)\\('*\\)$" in
      let n = Re.Str.search_forward re str 0 in
      let base = String.sub str 0 n in
      let numbers =
        match Re.Str.matched_group 1 str with
        | "" -> None
        | s -> Some s
      in
      let quotes =
        match Re.Str.matched_group 2 str with
        | "" -> None
        | s -> Some s
      in
      Some (base, numbers, quotes)
    with Not_found ->
      None

  (** Requirements *)

  type command_shape = {name: string; name': string; arity: int}

  module Requirements = Set.Make (struct type t = command_shape let compare = compare end)

  let requirements = ref Requirements.empty

  let record_command_shape name name' arity =
    requirements := Requirements.add {name; name'; arity} !requirements

  (** {2 Printers} *)
  let pp_command' ~suffix fmt base =
    fprintf fmt "\\%s%s%s" prefix (sanitize base) suffix

  (** Print a string as a LaTeX command *)
  let pp_command ~arity ~is_field fmt name =
    if match sn_decode name with | SNword _ -> false | _ -> true then
      failwith ("pp_command: argument not word: "^name);
    let name, name', suffix =
      if arity = 0 then
        if is_field then
          name^"field", name, ""
        else
          match split_base_suffixes name with
          | Some (base, numbers, quotes) ->
              let numbers =
                match numbers with
                | Some s -> sprintf "_{%s}" s
                | None -> "" in
              let quotes =
                match quotes with
                | Some s -> s
                | None -> "" in
              base, base, numbers^quotes
          | _ -> name, name, ""
      else
        (assert (not is_field);
         name^string_of_int arity, name, "") in
    record_command_shape name name' arity;
    pp_command' ~suffix fmt name

  let pp_var' ~arity fmt s =
    pp_command ~arity ~is_field:false fmt s

  let pp_var ~arity fmt id =
    pp_var' ~arity fmt id.id_str

  let pp_field fmt id =
    pp_command ~arity:0 ~is_field:true fmt id.id_str

  let pp_str str fmt () =
    fprintf fmt str

  let pp_command_shape ~comment_macros fmt {name; name'; arity} =
    let rec mk_args acc = function
      | 0 -> acc
      | n -> mk_args (sprintf "#%d" n::acc) (pred n) in
    let pp_args fmt n =
      if n = 0 then
        ()
      else
        let args = mk_args [] n in
        fprintf fmt "(%a)" (pp_print_list ~pp_sep:(pp_str ", ") pp_print_string) args in
    fprintf fmt "%s\\newcommand{%a}[%d]{\\mathsf{%s}%a}@."
      (if comment_macros then "% " else "")
      (pp_command' ~suffix:"") name arity (sanitize name') pp_args arity

  (** {2 Pretty-print inductive definition to latex }*)

  let latex_rule_name fmt s =
    let f = function
      | '_' -> pp_print_char fmt '-'
      | c -> pp_print_char fmt c
    in
    String.iter f s

  let id_of_qualid = function
    | Qident id
    | Qdot (_, id) -> id

  let rec str_of_qualid = function
    | Qident id -> id.id_str
    | Qdot (qid, id) -> str_of_qualid qid^"."^id.id_str

  let pp_arg pp fmt =
    fprintf fmt "{%a}" pp

  let pp_field pp fmt (qid, x) =
    fprintf fmt "%a\\texttt{=}%a"
      pp_field (id_of_qualid qid)
      pp x

  let rec pp_type fmt = function
    | PTtyvar id ->
        pp_var ~arity:0 fmt id
    | PTtyapp (qid, ts) ->
        let arity = List.length ts in
        fprintf fmt "%a%a" (pp_var ~arity) (id_of_qualid qid)
          (pp_print_list ~pp_sep:(pp_str "") (pp_arg pp_type)) ts
    | PTtuple ts ->
        fprintf fmt "(%a)"
          (pp_print_list ~pp_sep:(pp_str "") pp_type) ts
    | PTarrow (ty1, ty2) ->
        fprintf fmt "%a \\rightarrow %a"
          pp_type ty1 pp_type ty2
    | PTscope (_, ty) ->
        pp_type fmt ty
    | PTparen ty ->
        fprintf fmt "(%a)" pp_type ty
    | PTpure ty ->
        fprintf fmt "\\texttt{\\{}%a\\texttt{\\}}" pp_type ty
    | PTref _ -> failwith "pp_type: ref"

  let rec pp_pattern fmt p =
    match p.pat_desc with
    | Pwild ->
        fprintf fmt "\\texttt{anything}"
    | Pvar id ->
        fprintf fmt "%a" (pp_var ~arity:0) id
    | Papp (qid, ps) ->
        let arity = List.length ps in
        fprintf fmt "%a%a" (pp_var ~arity) (id_of_qualid qid)
          (pp_print_list ~pp_sep:(pp_str "") (pp_arg pp_pattern)) ps
    | Prec fs ->
        fprintf fmt "\\texttt{\\{}%a\\texttt{\\}}"
          (pp_print_list ~pp_sep:(pp_str "\\texttt{;} ") (pp_field pp_pattern)) fs
    | Ptuple ps ->
        fprintf fmt "(%a)" (pp_print_list ~pp_sep:(pp_str ", ") pp_pattern) ps
    | Pas (p, id, _) ->
        fprintf fmt "%a \\texttt{as} %a" pp_pattern p (pp_var ~arity:0) id
    | Por (p1, p2) ->
        fprintf fmt "%a \\texttt{|} %a" pp_pattern p1 pp_pattern p2
    | Pcast (p, ty) ->
        fprintf fmt "%a : %a" pp_pattern p pp_type ty
    | Pscope (_, p) ->
        pp_pattern fmt p
    | Pparen p ->
        fprintf fmt "(%a)" pp_pattern p
    | Pghost p ->
        pp_pattern fmt p

  let rec flatten_apply t =
    match t.term_desc with
    | Tapply ({term_desc=Tident qid}, t) -> Some (qid, [t])
    | Tapply (t1, t2) ->
        (match flatten_apply t1 with
         | Some (qid, ts) -> Some (qid, ts@[t2])
         | None -> None)
    | _ -> None

  let rec pp_term fmt t =
    match t.term_desc with
    | Ttrue ->
        fprintf fmt "\\top"
    | Tfalse ->
        fprintf fmt "\\bot"
    | Tconst n ->
        Constant.print_def fmt n
    | Tident qid ->
        let id = id_of_qualid qid in
        (match sn_decode id.id_str with
         | SNword _ -> pp_var ~arity:0 fmt id
         | _ -> fprintf fmt "(%s)" id.id_str)
    | Tinnfix (t1, id, t2)
    | Tinfix (t1, id, t2) ->
        let op =
          match sn_decode id.id_str with
          | SNinfix s -> sanitize_op s
          | _ -> failwith ("pp_term: op not infix: |"^id.id_str^"|") in
        fprintf fmt "%a %s %a" pp_term t1 op pp_term t2
    | Tbinop (t1, op, t2)
    | Tbinnop (t1, op, t2) ->
        let str =
          let open Dterm in
          match op with
          | DTimplies -> "\\rightarrow"
          | DTiff -> "\\leftrightarrow"
          | DTand -> "\\wedge"
          | DTand_asym -> "\\bar\\wedge"
          | DTor -> "\\vee"
          | DTor_asym -> "\\bar\\vee"
          | DTby -> "\\texttt{by}"
          | DTso -> "\\texttt{so}" in
        fprintf fmt "%a %s %a" pp_term t1 str pp_term t2
    | Tidapp (qid, ts) ->
        let id = id_of_qualid qid in
        (match sn_decode id.id_str, ts with
         | SNword s, ts ->
             let arity = List.length ts in
             let pp_args = pp_print_list ~pp_sep:(pp_str "") (pp_arg pp_term) in
             fprintf fmt "%a%a" (pp_var' ~arity) s pp_args ts
         | SNinfix s, [t1; t2] ->
             fprintf fmt "%a %s %a" pp_term t1 (sanitize_op s) pp_term t2
         | SNprefix s, [t]
         | SNtight s, [t] ->
             fprintf fmt "%s %a" s pp_term t
         | SNget s, [t1; t2] ->
             fprintf fmt "%a[%a]%s" pp_term t1 pp_term t2 s
         | SNset s, [t1; t2; t3] ->
             fprintf fmt "%a[%a]%s \\leftarrow %a" pp_term t1 pp_term t2 s pp_term t3
         | SNupdate s, [t1; t2; t3] ->
             fprintf fmt "%a[%a \\leftarrow %a]%s" pp_term t1 pp_term t2 pp_term t3 s
         | SNcut s, [t] ->
             fprintf fmt "%a[\\ldots]%s" pp_term t s
         | SNlcut s, [t1; t2] ->
             fprintf fmt "%a[\\ldots %a]%s" pp_term t1 pp_term t2 s
         | SNrcut s, [t1; t2] ->
             fprintf fmt "%a[%a \\ldots]%s" pp_term t1 pp_term t2 s
         | _ -> failwith (sprintf "pp_term Tidapp %s %d" id.id_str (List.length ts)))
    | Tapply (t1, t2) ->
        (match
           if flatten_applies
           then flatten_apply t
           else None
         with
         | Some (qid, ts) ->
             let arity = List.length ts in
             fprintf fmt "%a%a" (pp_var ~arity) (id_of_qualid qid)
               (pp_print_list ~pp_sep:(pp_str "") (pp_arg pp_term)) ts
         | None ->
             fprintf fmt "%a %a" pp_term t1 pp_term t2)
    | Tnot {term_desc=Tinfix (t1, op, t2)} when
        sn_decode op.id_str = SNinfix "=" ->
        fprintf fmt "%a \\neq %a" pp_term t1 pp_term t2
    | Tnot t ->
        fprintf fmt "\\neg %a" pp_term t
    | Tif (t1, t2, t3) ->
        fprintf fmt "\\texttt{if}~%a~\\texttt{then}~%a~\\texttt{else}~%a"
          pp_term t1 pp_term t2 pp_term t3
    | Tlet (id, t1, t2) ->
        fprintf fmt "\\textbf{let}~%a = %a~\\textbf{in}~%a" (pp_var ~arity:0) id
          pp_term t1 pp_term t2
    | Tquant (_, _, _, t) ->
        pp_term fmt t
    | Tcase (t, bs) ->
        let pp_sep = pp_str " \\texttt{|} " in
        let pp_branch fmt (p, t') = fprintf fmt "%a \\rightarrow %a" pp_pattern p pp_term t' in
        fprintf fmt "\\texttt{match}~%a~\\texttt{with}~%a" pp_term t
          (pp_print_list ~pp_sep pp_branch) bs
    | Tcast (t, ty) ->
        fprintf fmt "%a \\texttt{:} %a" pp_term t pp_type ty
    | Ttuple ts ->
        fprintf fmt "(%a)" (pp_print_list ~pp_sep:(pp_str ", ") pp_term) ts
    | Trecord fs ->
        let pp = pp_print_list ~pp_sep:(pp_str "\\texttt{;} ") (pp_field pp_term) in
        fprintf fmt "\\{%a\\}" pp fs
    | Tupdate (t, fs) ->
        let pp_fs = pp_print_list ~pp_sep:(pp_str "\\texttt{;} ") (pp_field pp_term) in
        fprintf fmt "\\{%a~\\texttt{with}~%a\\}" pp_term t pp_fs fs
    | Tscope (_, t) ->
        pp_term fmt t
    | Tattr _ -> failwith "pp_term: attr"
    | Tat _ -> failwith "pp_term: at"
    | Tasref _ -> failwith "pp_term: asref"

  let pp_rule fmt (id, terms) : unit =
    match List.rev terms with
    | [] -> invalid_arg "latex_rule: empty rule"
    | concl :: precs ->
        fprintf fmt "  \\inferrule[%a]@.    {%s%a}@.    {%a} \\\\@."
          latex_rule_name id.id_str
          (if precs = [] then "~" else "")
          (pp_print_list ~pp_sep:(pp_str "@ \\\\@ ") pp_term) (List.rev precs)
          pp_term concl

  let pp_rules fmt path defs =
    fprintf fmt "\\begin{mathparpagebreakable} %% %s@." (String.concat "." path);
    List.iter (pp_rule fmt) defs;
    fprintf fmt "\\end{mathparpagebreakable}@."

  exception Found of ind_decl

  (** Search an inductive type in mlw file by path (module.Theory.type or module.type) *)
  let search_inductive (path: string list) (mlw_file: mlw_file) : ind_decl =
    let name, decls =
      match path, mlw_file with
      | [name], Decls decls -> name, decls
      | [module_name; name], Modules modules ->
          let aux (id, _) = String.compare id.id_str module_name = 0 in
          name, snd (List.find aux modules)
      | _ -> raise Not_found in
    try
      let aux = function
        | Dind (Decl.Ind, ind_decls) ->
            let aux decl =
              if String.compare decl.in_ident.id_str name = 0 then
                raise (Found decl) in
            List.iter aux ind_decls
        | _ -> () in
      List.iter aux decls;
      raise Not_found
    with Found decl -> decl

  (** Flatten toplevel implies, let bindings, and universal quantifications *)
  let rec flatten_implies (t: term) : term list =
    match t.term_desc with
    | Tbinop (t1, Dterm.DTimplies, t2) ->
        t1 :: flatten_implies t2
    | Tquant (Dterm.DTforall, _, _, t) ->
        flatten_implies t
    | Tlet (id, t1, t2) ->
        let equality = (* id = t2 *)
          let id_term = {term_loc=Loc.dummy_position; term_desc=Tident (Qident id)} in
          let op = {Ptree.id_str=op_infix "="; Ptree.id_loc=Loc.dummy_position; id_ats=[]} in
          Tinfix (id_term, op, t1) in
        {term_loc=Loc.dummy_position; term_desc=equality} ::
        flatten_implies t2
    | _ -> [t]

  let main fmt mlw_file paths =
    let buf = Buffer.create 42 in
    let fmt' = formatter_of_buffer buf in
    let for_path path =
      try
        let decl = search_inductive path mlw_file in
        let defs = List.map (fun (_, id, t) -> id, flatten_implies t) decl.in_def in
        pp_rules fmt' path defs
      with Not_found ->
        eprintf "Could not find %s" (Strings.join "." path) in
    List.iter for_path paths;
    Requirements.iter (pp_command_shape ~comment_macros fmt) !requirements;
    pp_print_string fmt (Buffer.contents buf)
end

(** {2 Command line interface} *)

open Format
open Why3

let filename = ref None

let paths = Queue.create ()

let add_filename_then_path p =
  if !filename = None then
    filename := Some p
  else
    Queue.add (Strings.split '.' p) paths

type kind = Inductive

let kind = ref None

let set_kind = function
  | "inductive" -> kind := Some Inductive
  | _ -> assert false

type output = Latex | Mlw | Sexp | Dep

let output = ref Mlw

let set_output = function
  | "latex" -> output := Latex
  | "mlw" -> output := Mlw
  | "sexp" -> output := Sexp
  | "dep" -> output := Dep
  | _ -> assert false

let prefix = ref "WHY"

let usage_msg = sprintf
  "Usage: %s [options] [--output=latex|mlw|sexp|dep] [--kind=inductive] [--prefix=<prefix>] <filename> [<Module>.]<type> ...\n"
  (Filename.basename Sys.argv.(0))

let spec =
  let open Why3.Getopt in
  [ KLong "output", Hnd1 (ASymbol ["latex"; "mlw"; "sexp"; "dep"], set_output),
    "<output> select output format (default: \"mlw\")";
    KLong "kind", Hnd1 (ASymbol ["inductive"], set_kind),
    "<category> select syntactic category to be printed (only\n\
     \"inductive\" for --output=latex)";
    KLong "prefix", Hnd1 (AString, (:=) prefix),
    "<prefix> set prefix for LaTeX macros (default: \"WHY\")";
  ]

let parse_mlw_file filename =
  let c = if filename = "-" then stdin else open_in filename in
  let lexbuf = Lexing.from_channel c in
  let mlw_file = Lexer.parse_mlw_file lexbuf in
  if filename <> "-" then
    close_in c;
  mlw_file

let pident fmt i = fprintf fmt "%s" i.Ptree.id_str

let rec pqualid fmt q =
  Ptree.(match q with
  | Qident id -> fprintf fmt "%a" pident id
  | Qdot(q,id) -> fprintf fmt "%a.%a" pqualid q pident id)

let deps_use fmt filename (modname:string) (q:Ptree.qualid) =
  Ptree.(match q with
  | Qident id ->
     fprintf fmt "\"%s\" -> \"%s.%a\" ;@." modname filename pident id
  | Qdot _ ->
     fprintf fmt "\"%s\" -> \"%a\" ;@." modname pqualid q)

let deps_decl fmt filename modname d =
  Ptree.(match d with
  | Dtype _ | Dlogic _ | Dind _ | Dprop _ | Dlet _ | Drec _ | Dexn _ | Dmeta _ -> ()
  | Dcloneexport(q,_) | Duseexport q | Dcloneimport(_,_,q,_,_) ->
     deps_use fmt filename modname q
  | Duseimport(_,_, mods) ->
     List.iter (fun (q,_) -> deps_use fmt filename modname q) mods
  | Dimport _ -> ()
  | Dscope _ -> ())

let deps_module fmt filename modname dl =
  List.iter (deps_decl fmt filename modname) dl

let deps_file fmt header filename f =
  if header then fprintf fmt "digraph G {\
                              rankdir=RL;\
                              nodesep=0.4;\
                              ranksep=0.6;\
                              node [shape=box,margin=0.05]@.";
  begin
    Ptree.(match f with
  | Modules ml ->
     List.iter (fun (n,dl) -> deps_module fmt filename (filename ^ "." ^ n.id_str) dl) ml
    (** a list of modules containing lists of declarations *)
  | Decls dl -> deps_module fmt filename (filename ^ ".Top") dl)
  end;
  if header then fprintf fmt "}@."


let _, _, _ =
  Whyconf.Args.initialize spec add_filename_then_path usage_msg

let () =
    match !filename with
    | Some filename ->
        let mlw_file = parse_mlw_file filename in
        (match !output, !kind, Queue.length paths with
         | Latex, Some Inductive, _ ->
             let paths = List.rev (Queue.fold (fun l x -> x :: l) [] paths) in
             let module Conf = struct let prefix = !prefix let flatten_applies = true let comment_macros = true end in
             let module M = LatexInd(Conf) in
             M.main std_formatter mlw_file paths
         | Mlw, None, 0 ->
            Mlw_printer.pp_mlw_file std_formatter mlw_file
         | Dep, None, _ ->
            let f = Filename.(chop_extension (basename filename)) in
            deps_file std_formatter true f mlw_file
         | Sexp, None, 0 ->
             Ptree.sexp_of_mlw_file mlw_file |>
             Sexplib.Sexp.output_hum_indent 2 stdout
         | _, _, _ ->
             Getopt.handle_exn Sys.argv "invalid arguments"
        )
    | None ->
        Getopt.handle_exn Sys.argv "missing filename"
