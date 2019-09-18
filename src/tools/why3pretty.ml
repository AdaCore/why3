open Format
open Why3
open Ptree

(** {2 Pretty print simplified AST}*)

let sanitize =
  let my_char_to_alpha = function
    (* | '_' | '.' -> "" *)
    | c -> Ident.char_to_alpha c
  in
  Ident.sanitizer my_char_to_alpha my_char_to_alpha

let split_word str =
  try
    let re = Str.regexp "_?_?\\([0-9]*\\)\\('*\\)$" in
    let n = Str.search_forward re str 0 in
    let base = String.sub str 0 n in
    if base = "Tuple" then
      None
    else
      let numbers =
        match Str.matched_group 1 str with
        | "" -> None
        | s -> Some s
      in
      let quotes =
        match Str.matched_group 2 str with
        | "" -> None
        | s -> Some s
      in
      Some (base, numbers, quotes)
  with Not_found ->
    None

(** Requirements *)

type command_shape = {name: string; arity: int}

module Requirements = Set.Make (struct type t = command_shape let compare = compare end)

let requirements = ref Requirements.empty

let record_requirement name arity =
  let name =
    match split_word name with
    | None -> name
    | Some (base, _, _) -> base
  in
  requirements := Requirements.add {name; arity} !requirements

(** {2 Printers} *)

(** Print a string suitable as a LaTeX command name *)
let pp_command' ~prefix fmt str =
  let open Ident in
  pp_print_string fmt prefix;
  match sn_decode str with
  | SNword str ->
    begin match split_word str with
    | None ->
      pp_print_string fmt (sanitize str)
    | Some (base, numbers, quotes) ->
      pp_print_string fmt (sanitize base);
      begin match numbers with
        | Some str ->
          if String.length str = 1 then
            fprintf fmt "_%s" str
          else
            fprintf fmt "_{%s}" str
        | None -> ()
      end;
      begin match quotes with
        | Some str ->
          pp_print_string fmt str
        | None ->()
      end
    end
  | SNinfix str -> fprintf fmt "infix%s" (sanitize str)
  | SNtight str -> fprintf fmt "tight%s" (sanitize str)
  | SNprefix str -> fprintf fmt "prefix%s" (sanitize str)
  | SNget str -> fprintf fmt "get%s" (sanitize str)
  | SNset str -> fprintf fmt "set%s" (sanitize str)
  | SNupdate str -> fprintf fmt "update%s" (sanitize str)
  | SNcut str -> fprintf fmt "cut%s" (sanitize str)
  | SNlcut str -> fprintf fmt "lcut%s" (sanitize str)
  | SNrcut str -> fprintf fmt "rcut%s" (sanitize str)

(** Print a string as a LaTeX command *)
let pp_command ~prefix ~arity fmt str =
  record_requirement str arity;
  let str =
    let suffix =
      if arity = 0 then
        ""
      else
        Ident.sanitizer Ident.char_to_alpha Ident.char_to_alpha
          (string_of_int arity) in
    str^suffix in
  fprintf fmt "\\%a" (pp_command' ~prefix) str

let pp_str str fmt () = fprintf fmt str

let pp_requirement ~prefix ~comment_macros fmt {name; arity} =
  let rec mk_args acc = function
    | 0 -> acc
    | n -> mk_args (sprintf "#%d" n::acc) (pred n) in
  let pp_args fmt n =
    if n = 0 then
      ()
    else
      let args = mk_args [] n in
      fprintf fmt "(%a)" (pp_print_list ~pp_sep:(pp_str ", ") pp_print_string) args in
  fprintf fmt "%s\\newcommand{%a}[%d]{\\texttt{%s}%a}@."
    (if comment_macros then "%% " else "")
    (pp_command ~prefix ~arity) name arity name pp_args arity

(** {2 Pretty-print inductive definition to latex }*)

let latex_rule_name fmt s =
  let f = function
    | '_' -> pp_print_char fmt '-'
    | c -> pp_print_char fmt c
  in
  String.iter f s

let rec str_of_qualid = function
  | Qident id -> id.id_str
  | Qdot (qid, id) -> str_of_qualid qid^"."^id.id_str

let pp_arg pp fmt =
  fprintf fmt "{%a}" pp

let pp_field ~prefix pp fmt (qid, x) =
  let str = str_of_qualid qid in
  fprintf fmt "%a\\texttt{=}%a" (pp_command ~prefix ~arity:0) str (pp ~prefix) x

let rec pp_type ~prefix fmt = function
  | PTtyvar id ->
      pp_command ~prefix ~arity:0 fmt id.id_str
  | PTtyapp (qid, ts) ->
      let str = str_of_qualid qid in
      let arity = List.length ts in
      fprintf fmt "%a%a" (pp_command ~prefix ~arity) str
        (pp_print_list ~pp_sep:(pp_str "") (pp_arg (pp_type ~prefix))) ts
  | PTtuple ts ->
      fprintf fmt "(%a)"
        (pp_print_list ~pp_sep:(pp_str "") (pp_type ~prefix)) ts
  | PTarrow (ty1, ty2) ->
      fprintf fmt "%a \\rightarrow %a"
        (pp_type ~prefix) ty1 (pp_type ~prefix) ty2
  | PTscope (qid, ty) ->
      let str = str_of_qualid qid in
      fprintf fmt "%a.\\texttt{(}%a\\texttt{)}" (pp_command ~prefix ~arity:0) str (pp_type ~prefix) ty
  | PTparen ty ->
      fprintf fmt "(%a)" (pp_type ~prefix) ty
  | PTpure ty ->
      fprintf fmt "\\texttt{\\{}%a\\texttt{\\}}" (pp_type ~prefix) ty
  | PTref _ -> failwith "pp_type: ref"

let rec pp_pattern ~prefix fmt p =
  match p.pat_desc with
  | Pwild ->
      fprintf fmt "\\texttt{anything}"
  | Pvar id ->
      fprintf fmt "%a" (pp_command ~prefix ~arity:0) id.id_str
  | Papp (qid, ps) ->
      let str = str_of_qualid qid in
      let arity = List.length ps in
      fprintf fmt "%a%a" (pp_command ~prefix ~arity) str
        (pp_print_list ~pp_sep:(pp_str "") (pp_arg (pp_pattern ~prefix))) ps
  | Prec fs ->
      fprintf fmt "\\texttt{\\{}%a\texttt{\\}}"
        (pp_print_list ~pp_sep:(pp_str "\\texttt{;} ") (pp_field ~prefix pp_pattern)) fs
  | Ptuple ps ->
      fprintf fmt "(%a)" (pp_print_list ~pp_sep:(pp_str ", ") (pp_pattern ~prefix)) ps
  | Pas (p, id, _) ->
      fprintf fmt "%a \texttt{as} %a" (pp_pattern ~prefix) p (pp_command ~prefix ~arity:0) id.id_str
  | Por (p1, p2) ->
      fprintf fmt "%a \texttt{|} %a" (pp_pattern ~prefix) p1 (pp_pattern ~prefix) p2
  | Pcast (p, ty) ->
      fprintf fmt "%a : %a" (pp_pattern ~prefix) p (pp_type ~prefix) ty
  | Pscope (qid, p) ->
      let str = str_of_qualid qid in
      fprintf fmt "%a.\\texttt{(}%a\\texttt{)}" (pp_command ~prefix ~arity:0) str (pp_pattern ~prefix) p
  | Pparen p ->
      fprintf fmt "(%a)" (pp_pattern ~prefix) p
  | Pghost p ->
      pp_pattern ~prefix fmt p

let rec pp_term ~prefix fmt t =
  match t.term_desc with
  | Ttrue ->
      fprintf fmt "\\top"
  | Tfalse ->
      fprintf fmt "\\bot"
  | Tconst n ->
      Number.print_constant fmt n
  | Tident qid ->
      let str = str_of_qualid qid in
      pp_command ~prefix ~arity:0 fmt str
  | Tidapp (qid, ts) ->
      let str = str_of_qualid qid in
      let arity = List.length ts in
      fprintf fmt "%a%a" (pp_command ~prefix ~arity) str (pp_print_list ~pp_sep:(pp_str "") (pp_term ~prefix)) ts
  | Tinnfix (t1, id, t2)
  | Tinfix (t1, id, t2) ->
      fprintf fmt "%a %s %a" (pp_term ~prefix) t1 id.id_str (pp_term ~prefix) t2
      (* (match Ident.sn_decode id.id_str with
       *  | Ident.SNinfix s ->
       *  | _ ->
       *      failwith ("pp_term infix: "^id.id_str)) *)
  | Tapply (t1, t2) ->
      fprintf fmt "%a %a" (pp_term ~prefix) t1 (pp_term ~prefix) t2
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
      fprintf fmt "%a %s %a" (pp_term ~prefix) t1 str (pp_term ~prefix) t2
  | Tnot {term_desc=Tinfix (t1, op, t2)} when
      Ident.sn_decode op.id_str = Ident.SNinfix "=" ->
      fprintf fmt "%a \\neq %a" (pp_term ~prefix) t1 (pp_term ~prefix) t2
  | Tnot t ->
      fprintf fmt "\\neg %a" (pp_term ~prefix) t
  | Tif (t1, t2, t3) ->
      fprintf fmt "\\texttt{if}~%a~\\texttt{then}~%a~\\texttt{else}~%a"
        (pp_term ~prefix) t1 (pp_term ~prefix) t2 (pp_term ~prefix) t3
  | Tlet (id, t1, t2) ->
      fprintf fmt "\\textbf{let}~%a = %a~\\textbf{in}~%a" (pp_command ~prefix ~arity:0) id.id_str
        (pp_term ~prefix) t1 (pp_term ~prefix) t2
  | Tquant (_, _, _, t) ->
      pp_term ~prefix fmt t
  | Tcase (t, bs) ->
      let pp_sep = pp_str " \\texttt{|} " in
      let pp_branch fmt (p, t') = fprintf fmt "%a \\rightarrow %a" (pp_pattern ~prefix) p (pp_term ~prefix) t' in
      fprintf fmt "\\texttt{match}~%a~\\texttt{with}~%a" (pp_term ~prefix) t
        (pp_print_list ~pp_sep pp_branch) bs
  | Tcast (t, ty) ->
      fprintf fmt "%a \texttt{:} %a" (pp_term ~prefix) t (pp_type ~prefix) ty
  | Ttuple ts ->
      fprintf fmt "(%a)" (pp_print_list ~pp_sep:(pp_str ", ") (pp_term ~prefix)) ts
  | Trecord fs ->
      let pp = pp_print_list ~pp_sep:(pp_str "\\texttt{;} ") (pp_field ~prefix pp_term) in
      fprintf fmt "\\{%a\\}" pp fs
  | Tupdate (t, fs) ->
      let pp_fs = pp_print_list ~pp_sep:(pp_str "\\texttt{;} ") (pp_field ~prefix pp_term) in
      fprintf fmt "\\{%a \\texttt{with} %a\\}" (pp_term ~prefix) t pp_fs fs
  | Tscope (qid, t) ->
      let str = str_of_qualid qid in
      fprintf fmt "%a.\\texttt{(}%a\\texttt{)}"
        (pp_command ~prefix ~arity:0) str (pp_term ~prefix) t
  | Tattr _ -> failwith "pp_term: attr"
  | Tat _ -> failwith "pp_term: at"
  | Tasref _ -> failwith "pp_term: asref"

let pp_rule ~prefix fmt (id, terms) : unit =
  match List.rev terms with
  | [] -> invalid_arg "latex_rule: empty rule"
  | concl :: precs ->
      fprintf fmt "  \\inferrule[%a]@.    {%s%a}@.    {%a} \\\\@."
        latex_rule_name id.id_str
        (if precs = [] then "~" else "")
        (pp_print_list ~pp_sep:(pp_str "@ \\\\@ ") (pp_term ~prefix)) (List.rev precs)
        (pp_term ~prefix) concl

let pp_rules ~prefix fmt path defs =
  fprintf fmt "\\begin{mathparpagebreakable} %% %s@." (String.concat "." path);
  List.iter (pp_rule ~prefix fmt) defs;
  fprintf fmt "\\end{mathparpagebreakable}@."

(** Search an inductive type in mlw file by path (module.Theory.type or module.type) *)
let search_inductive (path: string list) (mlw_file: mlw_file) : ind_decl =
  let name, decls =
    match path, mlw_file with
    | [name], Decls decls -> name, decls
    | [module_name; name], Modules modules ->
        let aux (id, _) = String.equal id.id_str module_name in
        name, snd (List.find aux modules)
    | _ -> raise Not_found in
  let exception Found of ind_decl in
  try
    let aux = function
      | Dind (Decl.Ind, ind_decls) ->
          let aux decl =
            if String.equal decl.in_ident.id_str name then
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
        let op = {id_str=Ident.op_infix ""; id_loc=Loc.dummy_position; id_ats=[]} in
        Tinfix (id_term, op, t1) in
      {term_loc=Loc.dummy_position; term_desc=equality} ::
      flatten_implies t2
  | _ -> [t]

let main_latex_ind fmt ~prefix mlw_file paths =
    let buf = Buffer.create 42 in
    let fmt' = formatter_of_buffer buf in
    let for_path path =
      try
        let decl = search_inductive path mlw_file in
        let defs = List.map (fun (_, id, t) -> id, flatten_implies t) decl.in_def in
        pp_rules ~prefix fmt' path defs
      with Not_found ->
        eprintf "Could not find %s" (Strings.join "." path) in
    List.iter for_path paths;
    Requirements.iter (pp_requirement ~prefix ~comment_macros:true fmt) !requirements;
    pp_print_string fmt (Buffer.contents buf)

(** {2 Command line interface} *)

let filename = ref None

let paths = Queue.create ()

let add_filename_then_path p =
  if !filename = None then
    filename := Some p
  else
    Queue.add (Strings.split '.' p) paths

let prefix = ref "IND"

type kind = Inductive

let kind = ref Inductive

let set_kind = function
  | "inductive" -> kind := Inductive
  | str -> ksprintf invalid_arg "kind: %s" str

type output = Latex (* | Mlw *)

let output = ref Latex

let set_output = function
  | "latex" -> output := Latex
  | str -> ksprintf invalid_arg "output: %s" str

let usage =
  "Pretty print Why3 declarations (currently only inductive types in LaTeX using mathpartir).\n\
   why3 pretty [--output=latex] [--kind=inductive] [--prefix <prefix>] <filename> [<Module>.]<type> ..."

let options = [
  "--output", Arg.String set_output,    "<output> Output format (only: latex)";
  "--kind",   Arg.String set_kind,      "<category> Syntactic category to be printed (only: inductive)";
  "--prefix", Arg.String ((:=) prefix), "<prefix> Prefix for LaTeX commands (default for output latex: IND)";
]

let parse_mlw_file filename =
  let c = open_in filename in
  let lexbuf = Lexing.from_channel c in
  let mlw_file = Why3.Lexer.parse_mlw_file lexbuf in
  close_in c;
  mlw_file

let () =
  Arg.parse options add_filename_then_path usage;
  try
    match !filename with
    | Some filename ->
        let mlw_file = parse_mlw_file filename in
        (match !output, !kind with
         | Latex, Inductive ->
             let paths = List.rev (Queue.fold (fun l x -> x :: l) [] paths) in
             main_latex_ind std_formatter ~prefix:!prefix mlw_file paths)
    | None -> invalid_arg "no filename given"
  with Invalid_argument msg ->
    eprintf "Error: %s@." msg;
    exit 1
