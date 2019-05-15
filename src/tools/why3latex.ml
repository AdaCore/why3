open Format
open Why3
open Wstdlib
open Pmodule

let paths = Queue.create ()

let add_path p = Queue.add p paths

let prefix = ref "IND"

let records = Hashtbl.create 5

let add_record str =
  let split sep = Str.split (Str.regexp_string sep) in
  match split ":" str with
  | [name; fields_str] ->
      let fields = split "," fields_str in
      Hashtbl.replace records name fields
  | _ -> failwith "add_record"

let usage =
  "why3 latex [options] [--prefix PREFIX] [--record NAME:FIELD,...] ... <module>.<Theory>.<ind_type> ..."

let options = [
  "--prefix", Arg.String ((:=) prefix), sprintf "PREFIX Prefix for LaTeX commands (default: %s)" !prefix;
  "--record", Arg.String add_record,    "NAME:FIELD,... Reconstruct record update {v with f=e; ...} from record constructions {f=e; ...}";
]

let config, _, env = Whyconf.Args.initialize options add_path usage

(** {2 Simplified tree}*)

type myid = string

type mypattern =
  | Wild
  | Var' of myid
  | Or of mypattern * mypattern
  | As of mypattern * myid
  | App' of string * mypattern list

type myterm =
  | True
  | False
  | Var of myid
  | Int of BigInt.t
  | Not of myterm
  | Quant of Term.quant * myid list * myterm
  | Binop of Term.binop * myterm * myterm
  | App of string * myterm list
  | Equality of myid * myterm
  | Nonequality of myterm * myterm
  | Let of myid * myterm * myterm
  | Case of myterm * (mypattern * myterm) list
  | If of myterm * myterm * myterm
  | Update of myid * (string * myterm) list

(** {2 Pretty print simplified AST}*)

let sanitize =
  let my_char_to_alpha = function
    | '_' | ' ' -> ""
    | c -> Ident.char_to_alpha c
  in
  Ident.sanitizer my_char_to_alpha my_char_to_alpha

let sanitize2 =
  let my_char_to_alpha = function
    | '\'' -> "\'"
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

(** Print a string suitable as a LaTeX command name *)
let latex_command' fmt str =
  let open Ident in
  pp_print_string fmt !prefix;
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
let latex_command fmt str =
  fprintf fmt "\\%a" latex_command' str

(** {2 Import from Why3 [pmodule]}*)

(** {3 Record command names with arity to print dummy command definitions as comments}*)

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

let pp_requires fmt requirements =
  let rec mk_args acc = function
    | 0 -> acc
    | n -> mk_args (sprintf "#%d" n::acc) (n-1)
  in
  let pp_args fmt n =
    if n = 0 then
      ()
    else
      let args = mk_args [] n in
      let pp_sep fmt () = fprintf fmt ", " in
      fprintf fmt "(%a)" (pp_print_list ~pp_sep pp_print_string) args
  in
  let aux {name; arity} =
    fprintf fmt "%% \\newcommand{%a}[%d]{\\texttt{%a}%a}@."
      latex_command name arity latex_command' name pp_args arity
  in
  Requirements.iter aux requirements

let rec import_pattern p : mypattern =
  let open Term in
  match p.pat_node with
  | Pwild -> Wild
  | Pvar v ->
    let s = v.vs_name.Ident.id_string in
    record_requirement s 0;
    Var' s
  | Papp (ls, ps) ->
      let s = ls.ls_name.Ident.id_string in
      record_requirement s (List.length ps);
      App' (s, List.map import_pattern ps)
  | Por (p1, p2) -> Or (import_pattern p1, import_pattern p2)
  | Pas (p, s) -> As (import_pattern p, s.vs_name.Ident.id_string)

(** {2 Reconstruct record update}

    It's a hack but it seems to work, and is required, as long as there is
    no [Ptree] AST available from the parser.*)

(** A field value is either the field value of a variable [f=x.f] or an assignment of a
   term [f=t] *)
type field_value = Copy_field of string | Other_term of myterm
module FVMap = Map.Make (struct type t = field_value let compare = compare end)

let reconstruct_record ts fs =
  let copy_assigns =
    let aux f = function
      | App (s, [Var x]) when s = f ->
          Copy_field x
      | t ->
          Other_term t
    in
    List.map2 aux fs ts
  in
  let counts =
    let aux fmap ca =
      let n = try 1 + FVMap.find ca fmap with Not_found -> 1 in
      FVMap.add ca n fmap
    in
    List.fold_left aux FVMap.empty copy_assigns |>
    FVMap.bindings |>
    List.sort (fun (_, x) (_, y) -> compare y x)
  in
  match counts with
  | (Copy_field x, n) :: _ ->
      if float_of_int (List.length fs) /. 2. <= float_of_int n then
        let aux f = function
          | Copy_field y when y = x -> None
          | Copy_field y -> Some (f, App (f,  [Var y]))
          | Other_term t -> Some (f, t)
        in
        let fields =
          List.map2 aux fs copy_assigns |>
          List.filter (fun o -> o <> None) |>
          List.map (function Some x -> x | None -> assert false)
        in
        Update (x,  fields)
      else
        invalid_arg "Not enough copies"
  | _ -> invalid_arg "Max not copy"

let rec reconstruct_records ts = function
  | [] -> invalid_arg "Empty records"
  | fs :: records' ->
      try reconstruct_record ts fs
      with Invalid_argument _ ->
        reconstruct_records ts records'

(** {2 Import Why3 [Pmodule] AST to simplified AST} *)

let rec import_term t : myterm =
  let open Term in
  match t.t_node with
  | Tvar v ->
    let s = v.vs_name.Ident.id_string in
    record_requirement s 0;
    Var s
  | Tconst (Number.ConstInt i) -> Int i.Number.il_int
  | Tconst (Number.ConstReal _) -> failwith "import_term: real"
  | Tquant (q, t') ->
      let vsl, _, t = t_open_quant t' in
      let aux vs =
        let s = vs.vs_name.Ident.id_string in
        record_requirement s 0;
        s
      in
      Quant (q, List.map aux vsl, import_term t)
  | Tbinop (op, t1, t2) ->
      Binop (op, import_term t1, import_term t2)
  | Tapp (ls, ts) -> begin
      let s = ls.ls_name.Ident.id_string in
      let ts = List.map import_term ts in
      try
        let re = Str.regexp "mk \\(.*\\)" in
        if Str.string_match re s 0 then (* Is record constructor *)
          let name = Str.matched_group 1 s in
          try
            let fs = Hashtbl.find records name in
            reconstruct_record ts fs
          with Not_found ->
            invalid_arg "Unknown record"
        else
          invalid_arg "Not a record constructor"
      with Invalid_argument _ ->
        record_requirement s (List.length ts);
        App (s, ts)
    end
  | Tlet (t1, t2') ->
      let vs, t2 = t_open_bound t2' in
      let s = vs.vs_name.Ident.id_string in
      record_requirement s 0;
      Let (s, import_term t1, import_term t2)
  | Tnot {t_node=Tapp (ls, [t1; t2])} when ls.ls_name.Ident.id_string = "infix =" ->
      Nonequality (import_term t1, import_term t2)
  | Tnot t' -> Not (import_term t')
  | Ttrue -> True
  | Tfalse -> False
  | Tcase (t, bs) ->
      let aux b =
        let p, t = t_open_branch b in
        import_pattern p, import_term t
      in
      Case (import_term t, List.map aux bs)
  | Tif (t1, t2, t3) -> If (import_term t1, import_term t2, import_term t3)
  | Teps _ -> failwith "import_term: epsilone not implemented"

(** Flatten toplevel implies, let bindings, and universal quantifications *)
let rec flatten_implies t : myterm list =
  let open Term in
  match t.t_node with
  | Tbinop (Timplies, t1, t2) ->
      import_term t1 :: flatten_implies t2
  | Tquant (Tforall, t') ->
      let _, _, t = t_open_quant t' in
      flatten_implies t
  | Tlet (t1, t2') ->
    let vs, t2 = t_open_bound t2' in
    let s = vs.vs_name.Ident.id_string in
    record_requirement s 0;
    Equality (s, import_term t1) ::
    flatten_implies t2
  | _ -> [import_term t]

(** {2 Print simplified AST in LaTeX}*)

let rec latex_pattern fmt p =
  match p with
  | Wild -> fprintf fmt "\\textit{anything}"
  | Var' s -> latex_command fmt s
  | App' (s, ps) ->
      let pp_sep fmt () = pp_print_string fmt "" in
      let pp fmt = fprintf fmt "{%a}" latex_pattern in
      fprintf fmt "%a%a" latex_command s (pp_print_list ~pp_sep pp) ps
  | Or (p1, p2) -> fprintf fmt "%a~\\text{or}~%a" latex_pattern p1 latex_pattern p2
  | As (p, s) -> fprintf fmt "%a~\\text{as}~%a" latex_pattern p latex_command s

let rec latex_term fmt t =
  let open Term in
  match t with
  | True -> fprintf fmt "\\top"
  | False -> fprintf fmt "\\bot"
  | Var s -> latex_command fmt s
  | Int i -> fprintf fmt "%s" (BigInt.to_string i)
  | Not t -> fprintf fmt "\\neg %a" latex_term t
  | Quant (q, vs, t) ->
      let q = match q with Tforall -> "\\forall" | Texists -> "\\exists" in
      let pp_sep fmt () = pp_print_string fmt " " in
      fprintf fmt "%s %a.~%a" q (pp_print_list ~pp_sep latex_command) vs latex_term t
  | Binop (op, t1, t2) ->
      let op = match op with Tand -> "\\wedge" | Tor -> "\\vee" | Timplies -> "\\rightarrow" | Tiff -> "\\leftrightarrow" in
      fprintf fmt "%a %s %a" latex_term t1 op latex_term t2
  | Update (id, fs) ->
      let pp_sep fmt () = fprintf fmt ";@ " in
      let pp_f fmt (s, t) = fprintf fmt "%afield \\leftarrow %a" latex_command s latex_term t in
      fprintf fmt "%a[%a]" latex_command id (pp_print_list ~pp_sep pp_f) fs
  | App (s, ts) -> begin
      let pp_sep fmt () = pp_print_string fmt "" in
      let pp fmt = fprintf fmt "{%a}" latex_term in
      fprintf fmt "%a%a" latex_command s (pp_print_list ~pp_sep pp) ts
    end
  | Equality (id, t) ->
      fprintf fmt "%a = %a" latex_command id latex_term t
  | Nonequality (t1, t2) ->
      fprintf fmt "%a \\neq %a" latex_term t1 latex_term t2
  | Let (v, t1, t2) ->
      fprintf fmt "\\textbf{let}~%a = %a~\\textbf{in}~%a" latex_command v latex_term t1 latex_term t2
  | Case (t, bs) ->
      let pp_sep fmt () = fprintf fmt " | " in
      let pp_b fmt (p, t') = fprintf fmt "%a \\rightarrow %a" latex_pattern p latex_term t' in
      fprintf fmt "\\texttt{match}~%a~\\texttt{with}~%a" latex_term t
        (pp_print_list ~pp_sep pp_b) bs
  | If (t1, t2, t3) ->
      fprintf fmt "\\texttt{if}~%a~\\texttt{then}~%a~\\texttt{else}~%a"
        latex_term t1 latex_term t2 latex_term t3

let latex_rule_name fmt s =
  let f = function
    | '_' -> pp_print_char fmt '-'
    | c -> pp_print_char fmt c
  in
  String.iter f s

let latex_rule fmt (psym, t) =
  match List.rev t with
  | [] -> invalid_arg "latex_rule: empty rule"
  | concl :: precs ->
    let pp_sep fmt () = fprintf fmt "@ \\\\@ " in
    fprintf fmt "  \\inferrule[%a]@.    {%s%a}@.    {%a} \\\\@."
      latex_rule_name psym.Decl.pr_name.Ident.id_string
      (if precs = [] then "~" else "")
      (pp_print_list ~pp_sep latex_term) (List.rev precs)
      latex_term concl

(** {2 Search inductive type corresponding to ["<module>.<Theory>.<ind_type>"] } *)

let split_path path =
  let path = Strings.split '.' path in
  let path, s = Lists.chop_last path in
  let path, m = Lists.chop_last path in
  path, m, s

let find_module path m =
  Mstr.find m @@
  Env.read_library Pmodule.mlw_language env path

exception Found of Term.lsymbol * (Decl.prsymbol * Term.term) list

let search_sym pm s =
  let open Pdecl in
  let open Decl in
  let search_ind (lsym, ts) =
    if lsym.Term.ls_name.Ident.id_string = s then
      raise (Found (lsym, ts))
  in
  let search_pure = function
    | {Decl.d_node=Dind (Ind, li)} ->
        List.iter search_ind li
    | _ -> ()
  in
  let search_unit = function
    | Udecl {pd_node=PDpure; pd_pure} ->
        List.iter search_pure pd_pure
    | _ -> ()
  in
  try
    List.iter search_unit pm.mod_units;
    raise Not_found
  with Found (lsym, def) ->
    lsym, def

(** {2 Main program}*)

let latex_main fmt path =
  let path, m, s = split_path path in
  let pm = find_module path m in
  let lsym, ind_rules = search_sym pm s in
  let ind_rules = List.map (fun (psym, t) -> psym, flatten_implies t) ind_rules in
  pp_requires fmt !requirements;
  fprintf fmt "\\begin{mathparpagebreakable} %% %s@." lsym.Term.ls_name.Ident.id_string;
  List.iter (latex_rule fmt) ind_rules;
  fprintf fmt "\\end{mathparpagebreakable}@."

let () = Queue.iter (latex_main std_formatter) paths
