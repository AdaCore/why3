(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Task
open Ty
open Term
open Trans
open Ident
open Theory
open Decl

exception Parse_error of string
exception Arg_expected of string * string
exception Arg_theory_not_found of string
exception Arg_expected_none of string
exception Arg_qid_not_found of Ptree.qualid
exception Arg_pr_not_found of prsymbol
exception Arg_error of string

let () = Exn_printer.register
    (fun fmt e ->
      match e with
      | Parse_error s ->
          Format.fprintf fmt "Parsing error: %s" s
      | Arg_expected (ty, s) ->
          Format.fprintf fmt "Argument expected of type: %s\n Argument given: %s" ty s
      | Arg_theory_not_found s ->
          Format.fprintf fmt "Theory not found %s" s
      | Arg_expected_none s ->
          Format.fprintf fmt "Argument expected of type %s. None were given." s
      | _ -> raise e)

open Wstdlib

(* Use symb to encapsulate ids into correct categories of symbols *)
type symb =
  | Ts of tysymbol
  | Ls of lsymbol
  | Pr of prsymbol

(* [add_unsafe s id tables] Add (s, id) to tables without any checking. *)
let add_unsafe (s: string) (id: symb) (tables: naming_table) : naming_table =
  match id with
  | Ts ty ->
      {tables with
        namespace = {tables.namespace with ns_ts = Mstr.add s ty tables.namespace.ns_ts};
      }
  | Ls ls ->
      {tables with
        namespace = {tables.namespace with ns_ls = Mstr.add s ls tables.namespace.ns_ls};
      }
  | Pr pr ->
      {tables with
        namespace = {tables.namespace with ns_pr = Mstr.add s pr tables.namespace.ns_pr};
}

let id_unique tables id = id_unique_attr tables.printer id

(* Adds symbols that are introduced to a constructor *)
let constructor_add (cl: constructor list) tables : naming_table =
  List.fold_left
    (fun tables ((ls, cl): constructor) ->
      let tables = List.fold_left
          (fun tables (cs: lsymbol option) ->
            match cs with
            | Some cs ->
                let id = cs.ls_name in
                let s = id_unique tables id in
                add_unsafe s (Ls cs) tables
            | None -> tables) tables cl in
      let id = ls.ls_name in
      let s = id_unique tables id in
      add_unsafe s (Ls ls) tables)
    tables
    cl

(* Add symbols that are introduced by an inductive *)
let ind_decl_add il tables =
  List.fold_left
    (fun tables ((pr, _): prsymbol * term) ->
      let id = pr.pr_name in
      let s = id_unique tables id in
      add_unsafe s (Pr pr) tables)
    il
    tables



(* [add d printer tables] Adds all new declaration of symbol inside d to tables.
  It uses printer to give them a unique name and also register these new names in printer *)
let add (d: decl) (tables: naming_table): naming_table =
  match d.d_node with
  | Dtype ty ->
      (* only current symbol is new in the declaration (see create_ty_decl) *)
      let id = ty.ts_name in
      let s = id_unique tables id in
      add_unsafe s (Ts ty) tables
  | Ddata dl ->
      (* first part is new. Also only first part of each constructor seem new
         (see create_data_decl) *)
      List.fold_left
        (fun tables (dd: data_decl) ->
          let id = (fst dd).ts_name in
          let s = id_unique tables id in
          let tables = add_unsafe s (Ts (fst dd)) tables in
          constructor_add (snd dd) tables)
        tables
        dl
  | Dparam ls ->
      (* Only one lsymbol which is new *)
      let id = ls.ls_name in
      let s = id_unique tables id in
      add_unsafe s (Ls ls) tables
  | Dlogic lsd ->
      (* Only first part of logic_decl is new (see create_logic) *)
      List.fold_left
        (fun tables ((ls,_): logic_decl) ->
          let id = ls.ls_name in
          let s = id_unique tables id in
          add_unsafe s (Ls ls) tables)
        tables
        lsd
  | Dind (_is, il) ->
      (* Every symbol is new except symbol inside terms (see create_ind_decl) *)
      List.fold_left
        (fun tables ((ls,ind): ind_decl) ->
          let id = ls.ls_name in
          let s = id_unique tables id in
          let tables = add_unsafe s (Ls ls) tables in
          ind_decl_add tables ind)
        tables
        il
  | Dprop (_, pr, _) ->
      (* Only pr is new in Dprop (see create_prop_decl) *)
      let id = pr.pr_name in
      let s = id_unique tables id in
      add_unsafe s (Pr pr) tables

(* Adds meta arguments of type ident to tables *)
let add_meta_id_args (al: meta_arg list) (tables: naming_table): naming_table =
  List.fold_left
    (fun t a ->
      match a with
      | MAid id ->
         let s = id_unique tables id in
         { tables with meta_id_args = Mstr.add s id tables.meta_id_args }
      | _ -> t)
    tables al

(* Takes the set of meta defined in the tasks and build the coercions from it.
   TODO we could have a set of coercions in the task ? Same problem for naming
   table ?
*)
let build_coercion_map km_meta =
  try
    let crc_set = Theory.Mmeta.find Theory.meta_coercion km_meta in
    let crc_map = Stdecl.fold (fun elem crc_map ->
      match elem.Theory.td_node with
      | Meta (m,([MAls ls] as _al)) when meta_equal m Theory.meta_coercion ->
        Coercion.add crc_map ls
      | _ -> crc_map) crc_set.tds_set Coercion.empty in
    crc_map
  with
  | Not_found -> Coercion.empty

let build_naming_tables task : naming_table =
  let isanitizer = None (* sanitizer do not seem to be necessary *) in
  let lsanitize = sanitizer char_to_lalpha char_to_alnumus in
  let pr = create_ident_printer Pretty.why3_keywords ?sanitizer:isanitizer in
  let apr = create_ident_printer Pretty.why3_keywords ~sanitizer:lsanitize in
  let km = Task.task_known task in
  let km_meta = Task.task_meta task in
  let tables = {
      namespace = empty_ns;
      known_map = km;
      coercion = Coercion.empty;
      printer = pr;
      aprinter = apr;
      meta_id_args = Mstr.empty;
  } in
(*  We want conflicting names to be named as follows:
    names closer to the goal should be named with lowest
    disambiguation numbers.
    This only works for things defined in .why/.mlw because things
    added by the user are renamed on the fly. *)
  (* TODO:imported theories should be added in the namespace too *)
  let tables = Task.task_fold
    (fun t d ->
      match d.td_node with
      | Decl d -> add d t
      | Meta (_,al) -> add_meta_id_args al t
      | _ -> t) tables task
  in
  let crc_map = build_coercion_map km_meta in
  {tables with coercion = crc_map}

(************* wrapper  *************)

type symbol =
  | Tstysymbol of Ty.tysymbol
  | Tsprsymbol of Decl.prsymbol
  | Tslsymbol of Term.lsymbol

type (_, _) trans_typ =
  | Ttrans      : ((task trans), task) trans_typ
  | Ttrans_l    : ((task tlist), task list) trans_typ
  | Tenvtrans   : (Env.env -> (task trans), task) trans_typ
  | Tenvtrans_l : (Env.env -> (task tlist), task list) trans_typ
  | Tstring     : ('a, 'b) trans_typ -> ((string -> 'a), 'b) trans_typ
  | Tint        : ('a, 'b) trans_typ -> ((int -> 'a), 'b) trans_typ
  | Tty         : ('a, 'b) trans_typ -> ((ty -> 'a), 'b) trans_typ
  | Ttysymbol   : ('a, 'b) trans_typ -> ((tysymbol -> 'a), 'b) trans_typ
  | Tprsymbol   : ('a, 'b) trans_typ -> ((Decl.prsymbol -> 'a), 'b) trans_typ
  | Tprlist     : ('a, 'b) trans_typ -> ((Decl.prsymbol list -> 'a), 'b) trans_typ
  | Tlsymbol    : ('a, 'b) trans_typ -> ((Term.lsymbol -> 'a), 'b) trans_typ
  | Tsymbol     : ('a, 'b) trans_typ -> ((symbol -> 'a), 'b) trans_typ
  | Tlist       : ('a, 'b) trans_typ -> ((symbol list -> 'a), 'b) trans_typ
  | Tidentlist  : ('a, 'b) trans_typ -> ((string list -> 'a), 'b) trans_typ
  | Ttermlist   : ('a, 'b) trans_typ -> ((term list -> 'a), 'b) trans_typ
  | Ttermlist_same : int * ('a, 'b) trans_typ -> ((term list -> 'a), 'b) trans_typ
  | Tterm       : ('a, 'b) trans_typ -> ((term -> 'a), 'b) trans_typ
  | Tformula    : ('a, 'b) trans_typ -> ((term -> 'a), 'b) trans_typ
  | Ttheory     : ('a, 'b) trans_typ -> ((Theory.theory -> 'a), 'b) trans_typ
  | Topt        : string * ('a -> 'c, 'b) trans_typ -> (('a option -> 'c), 'b) trans_typ
  | Toptbool    : string * ('a, 'b) trans_typ -> (bool -> 'a, 'b) trans_typ

let find_pr q tables =
  Theory.ns_find_pr tables.namespace (Typing.string_list_of_qualid q)

let find_ts q tables =
  Theory.ns_find_ts tables.namespace (Typing.string_list_of_qualid q)

let find_ls q tables =
  Theory.ns_find_ls tables.namespace (Typing.string_list_of_qualid q)

let find_symbol q tables =
  try Tsprsymbol (find_pr q tables) with
        | Not_found ->
          try Tslsymbol (find_ls q tables) with
          | Not_found ->
            try Tstysymbol (find_ts q tables) with
            | Not_found -> raise (Arg_qid_not_found q)

let find_pr_list pr_list tables =
  Lists.map_filter (fun id ->
    try Some (find_pr id tables) with
    | Not_found -> Warning.emit "Symbol '%a' not found, ignored"
       Typing.print_qualid id; None) pr_list

let find_symbol_list pr_list tables =
  Lists.map_filter (fun id ->
    try Some (find_symbol id tables) with Arg_qid_not_found _ ->
      Warning.emit "Symbol '%a' not found, ignored"
        Typing.print_qualid id; None) pr_list

let type_ptree ~as_fmla t tables =
  let km = tables.known_map in
  let ns = tables.namespace in
  let crc = tables.coercion in
  if as_fmla
  then Typing.type_fmla_in_namespace ns km crc t
  else Typing.type_term_in_namespace ns km crc t

exception Arg_parse_type_error of Loc.position * string * exn

let registered_lang_parsing_trans = Hashtbl.create 63

exception Add_language_parser

let set_argument_parsing_functions lang ~parse_term ~parse_term_list
    ~parse_qualid ~parse_list_qualid ~parse_list_ident =
  if Hashtbl.mem registered_lang_parsing_trans lang then
    raise Add_language_parser
  else
    Hashtbl.add registered_lang_parsing_trans lang
      (parse_term,
       parse_term_list,
       parse_qualid,
       parse_list_qualid,
       parse_list_ident)

(*
(* The parser/printer for regular Why3 is disabled. Instead, we use the one
   from the plugin for Ada: registered in plugins/ada_terms/ada_main.ml *)
let () =
  set_argument_parsing_functions Lexer.whyml_format
    ~parse_term:(fun _ -> Lexer.parse_term)
    ~parse_term_list:(fun _ -> Lexer.parse_term_list)
    ~parse_qualid:Lexer.parse_qualid
    ~parse_list_qualid:Lexer.parse_list_qualid
    ~parse_list_ident:Lexer.parse_list_ident
*)

let get_parse_term lang =
  let (p, _, _, _, _) =
    try Hashtbl.find registered_lang_parsing_trans lang with
    | Not_found -> Hashtbl.find registered_lang_parsing_trans Lexer.whyml_format in
  p

let get_parse_term_list lang =
  let (_, p, _, _, _) =
    try Hashtbl.find registered_lang_parsing_trans lang with
    | Not_found -> Hashtbl.find registered_lang_parsing_trans Lexer.whyml_format in
  p

let get_parse_qualid lang =
  let (_, _, p, _, _) =
    try Hashtbl.find registered_lang_parsing_trans lang with
    | Not_found -> Hashtbl.find registered_lang_parsing_trans Lexer.whyml_format in
  p

let get_parse_list_qualid lang =
  let (_, _, _, p, _) =
    try Hashtbl.find registered_lang_parsing_trans lang with
    | Not_found -> Hashtbl.find registered_lang_parsing_trans Lexer.whyml_format in
  p

let get_parse_list_ident lang =
  let (_, _, _, _, p) =
    try Hashtbl.find registered_lang_parsing_trans lang with
    | Not_found -> Hashtbl.find registered_lang_parsing_trans Lexer.whyml_format in
  p

(*
  parse_term_ref        := parse_term;
  parse_term_list_ref   := parse_term_list;
  parse_qualid_ref      := parse_qualid;
  parse_list_qualid_ref := parse_list_qualid;
  parse_list_ident_ref  := parse_list_ident
*)

let parse_and_type ~lang ~as_fmla s naming_table =
  try
    let lb = Lexing.from_string s in
    let t = get_parse_term lang naming_table lb in
    type_ptree ~as_fmla:as_fmla t naming_table
  with
  | Loc.Located (loc, e) -> raise (Arg_parse_type_error (loc, s, e))

let parse_and_type_list ~lang ~as_fmla s naming_table =
  try
    let lb = Lexing.from_string s in
    let t_list = get_parse_term_list lang naming_table lb in
    List.map (fun t -> type_ptree ~as_fmla:as_fmla t naming_table) t_list
  with
  | Loc.Located (loc, e) -> raise (Arg_parse_type_error (loc, s, e))

(* This parses and types a list of terms that should have the same type
   (example of replace). Because of coercions, this is not trivial to do in
   this file. To force unification we use a trick that takes the list
   [t1; t2; t3;....tn] and try to type the term
   (t1 = t2 /\ t1 = t3 /\ ... t1 = tn) instead. This enforces the correct
   use of coercions during typing. We then recover the separated terms. *)
let parse_list_same ~lang ~as_fmla ls naming_table =
  (* Deconstruct the term built for typing into the list of typed terms *)
  let rec collect acc t =
    match t.t_node with
    | Tbinop (Tand, t1, {t_node = Tapp (eq, [_; t3]); _}) when ls_equal eq ps_equ ->
        collect (t3 :: acc) t1
    | Tapp (_, [t2; t3]) -> t2 :: t3 :: acc
    | _ -> t :: acc in
  try
    let llb = List.map (fun s -> Lexing.from_string s) ls in
    let t_list = List.map (get_parse_term lang naming_table) llb in
    (* Type them somehow so that they have the same type *)
    let id_equal = Ptree.{id_str = Ident.op_infix "=";
                          id_ats = [];
                          id_loc = Loc.dummy_position } in
    if List.length t_list < 2 then
      (* This case should not happen, fallback to normal typing *)
      List.map (fun t -> type_ptree ~as_fmla t naming_table) t_list
    else
      let hds, t_list = Lists.split 2 t_list in
      let open Ptree in
      match hds with
      | hd1 :: hd2 :: [] ->
          let tfst_eq = {term_desc = Tidapp (Qident id_equal, [hd1; hd2]);
                         term_loc = Loc.dummy_position} in
          let term_to_type = List.fold_left
              (fun acc t ->
                 let teq = {term_desc = Tidapp (Qident id_equal, [hd1; t]);
                            term_loc = Loc.dummy_position} in
                 {term_desc = Tbinnop (acc, Dterm.DTand, teq);
                  term_loc = Loc.dummy_position })
              tfst_eq t_list in
          let typed_term = type_ptree ~as_fmla:true term_to_type naming_table in
          (* Recollect the (now) typed terms from the conjunction *)
          collect [] typed_term
      | _ -> assert false (* Lists.split should give a list of 2 elements *)
  with
  | Loc.Located (loc, e) ->
      let arg = List.fold_left (fun acc x ->
          if acc = "" then x else acc ^ " " ^ x) "" ls in
      raise (Arg_parse_type_error (loc, arg, e))

let parse_qualid ~lang s =
  try
    let lb = Lexing.from_string s in
    get_parse_qualid lang lb
  with
  | Loc.Located (loc, e) -> raise (Arg_parse_type_error (loc, s, e))

let parse_list_qualid ~lang s =
  try
    let lb = Lexing.from_string s in
    get_parse_list_qualid lang lb
  with
  | Loc.Located (loc, e) -> raise (Arg_parse_type_error (loc, s, e))

let parse_list_ident ~lang s =
  try
    let lb = Lexing.from_string s in
    get_parse_list_ident lang lb
  with
  | Loc.Located (loc, e) -> raise (Arg_parse_type_error (loc, s, e))

let build_error s e =
  let loc = Loc.user_position "" 0 0 (String.length s - 1) in
  raise (Arg_parse_type_error (loc, s, e))

let parse_int s =
  try int_of_string s
  with Failure _ ->
    build_error s (Parse_error "int expected")

let parse_theory env s =
  try
    let path, name = match Strings.split '.' s with
      | [name] -> [],name
      | path::[name] ->
        let path = Strings.split '/' path in
        path, name
      | _ ->
          build_error s (Parse_error "Ill-formed theory name")
    in
    Env.read_theory env path name
  with
    _ ->
      build_error s (Parse_error "Theory not found")

let trans_typ_tail: type a b c. (a -> b, c) trans_typ -> (b, c) trans_typ =
  fun t ->
    match t with
    | Tint t       -> t
    | Tty t        -> t
    | Ttysymbol t  -> t
    | Tprsymbol t  -> t
    | Tprlist t    -> t
    | Tlsymbol t   -> t
    | Tsymbol t    -> t
    | Tlist t      -> t
    | Tterm t      -> t
    | Tstring t    -> t
    | Tformula t   -> t
    | Ttheory t    -> t
    | Ttermlist t  -> t
    | Tidentlist t -> t
    | _            -> assert false

type _ trans_typ_is_l = Yes : (task list) trans_typ_is_l | No : task trans_typ_is_l

let rec is_trans_typ_l: type a b. (a, b) trans_typ -> b trans_typ_is_l =
  fun t -> match t with
    | Tenvtrans      -> No
    | Ttrans         -> No
    | Tenvtrans_l    -> Yes
    | Ttrans_l       -> Yes
    | Tint t         -> is_trans_typ_l t
    | Tstring t      -> is_trans_typ_l t
    | Tty t          -> is_trans_typ_l t
    | Ttysymbol t    -> is_trans_typ_l t
    | Tprsymbol t    -> is_trans_typ_l t
    | Tprlist t      -> is_trans_typ_l t
    | Tlsymbol t     -> is_trans_typ_l t
    | Tsymbol t      -> is_trans_typ_l t
    | Tlist t        -> is_trans_typ_l t
    | Tterm t        -> is_trans_typ_l t
    | Tidentlist t   -> is_trans_typ_l t
    | Ttermlist t    -> is_trans_typ_l t
    | Ttermlist_same (_, t) -> is_trans_typ_l t
    | Tformula t     -> is_trans_typ_l t
    | Ttheory t      -> is_trans_typ_l t
    | Topt (_,t)     -> is_trans_typ_l t
    | Toptbool (_,t) -> is_trans_typ_l t

let rec string_of_trans_typ : type a b. (a, b) trans_typ -> string =
  fun t ->
    match t with
    | Ttrans         -> "task"
    | Ttrans_l       -> "list task"
    | Tenvtrans      -> "env -> task"
    | Tenvtrans_l    -> "env -> list task"
    | Tint _         -> "int"
    | Tstring _      -> "string"
    | Tty _          -> "type"
    | Ttysymbol _    -> "tysymbol"
    | Tprsymbol _    -> "prsymbol"
    | Tprlist _      -> "list prsymbol"
    | Tlsymbol _     -> "lsymbol"
    | Tsymbol _      -> "symbol"
    | Tlist _        -> "list symbol"
    | Tterm _        -> "term"
    | Tformula _     -> "formula"
    | Tidentlist _   -> "list ident"
    | Ttermlist _    -> "list term"
    | Ttermlist_same _ -> "list term with same type"
    | Ttheory _      -> "theory"
    | Topt (s,t)     -> "?" ^ s ^ (string_of_trans_typ t)
    | Toptbool (s,_) -> "?" ^ s ^ ":bool"

let rec print_type : type a b. Format.formatter -> (a, b) trans_typ -> unit =
  fun fmt t ->
    match t with
    | Ttrans         -> Format.fprintf fmt "task"
    | Ttrans_l       -> Format.fprintf fmt "list task"
    | Tenvtrans      -> Format.fprintf fmt "env -> task"
    | Tenvtrans_l    -> Format.fprintf fmt "env -> list task"
    | Tint t         -> Format.fprintf fmt "integer -> %a" print_type t
    | Tstring t      -> Format.fprintf fmt "string -> %a" print_type t
    | Tty t          -> Format.fprintf fmt "type -> %a" print_type t
    | Ttysymbol t    -> Format.fprintf fmt "type_symbol -> %a" print_type t
    | Tprsymbol t    -> Format.fprintf fmt "prsymbol -> %a" print_type t
    | Tprlist t      -> Format.fprintf fmt "list prsymbol -> %a" print_type t
    | Tlsymbol t     -> Format.fprintf fmt "lsymbol -> %a" print_type t
    | Tsymbol t      -> Format.fprintf fmt "symbol -> %a" print_type t
    | Tlist t        -> Format.fprintf fmt "list symbol -> %a" print_type t
    | Tterm t        -> Format.fprintf fmt "term -> %a" print_type t
    | Tformula t     -> Format.fprintf fmt "formula -> %a" print_type t
    | Tidentlist t   -> Format.fprintf fmt "list ident -> %a" print_type t
    | Ttermlist t    -> Format.fprintf fmt "list term -> %a" print_type t
    | Ttermlist_same (n, t) -> Format.fprintf fmt "list term (same type arity: %d) -> %a" n print_type t
    | Ttheory t      -> Format.fprintf fmt "theory -> %a" print_type t
    | Topt (s,t)     -> Format.fprintf fmt "?%s -> %a" s print_type t
    | Toptbool (s,t) -> Format.fprintf fmt "?%s:bool -> %a" s print_type t

let rec wrap_to_store : type a b. (a, b) trans_typ -> a -> string list -> Env.env -> naming_table -> Env.fformat -> task -> b =
  fun t f l env tables lang task ->
    match t, l with
    | Ttrans, []-> apply f task
    | Ttrans_l, [] -> apply f task
    | Tenvtrans, [] -> apply (f env) task
    | Tenvtrans_l, [] -> apply (f env) task
    | Ttrans, _ -> raise (Unnecessary_arguments l)
    | Ttrans_l, _ -> raise (Unnecessary_arguments l)
    | Tenvtrans, _ -> raise (Unnecessary_arguments l)
    | Tenvtrans_l, _ -> raise (Unnecessary_arguments l)
    | Tint t', s :: tail ->
      let arg = parse_int s in wrap_to_store t' (f arg) tail env tables lang task
    | Tstring t', s :: tail ->
       wrap_to_store t' (f s) tail env tables lang task
    | Tformula t', s :: tail ->
      let te = parse_and_type ~lang ~as_fmla:true s tables in
      wrap_to_store t' (f te) tail env tables lang task
    | Tterm t', s :: tail ->
      let te = parse_and_type ~lang ~as_fmla:false s tables in
      wrap_to_store t' (f te) tail env tables lang task
    | Tty t', _s :: tail ->
      let ty = Ty.ty_int in (* TODO: parsing + typing of s *)
      wrap_to_store t' (f ty) tail env tables lang task
    | Ttysymbol t', _s :: tail ->
      let tys = Ty.ts_int in (* TODO: parsing + typing of s *)
      wrap_to_store t' (f tys) tail env tables lang task
    | Tprsymbol t', s :: tail ->
       let q = parse_qualid ~lang s in
       let pr = try (find_pr q tables) with
                | Not_found -> raise (Arg_qid_not_found q) in
      wrap_to_store t' (f pr) tail env tables lang task
    | Tprlist t', s :: tail ->
        let pr_list = parse_list_qualid ~lang s in
        let pr_list = find_pr_list pr_list tables in
        wrap_to_store t' (f pr_list) tail env tables lang task
    | Tlsymbol t', s :: tail ->
       let q = parse_qualid ~lang s in
       let pr = try (find_ls q tables) with
               | Not_found -> raise (Arg_qid_not_found q) in
      wrap_to_store t' (f pr) tail env tables lang task
    | Tsymbol t', s :: tail ->
       let q = parse_qualid ~lang s in
       let symbol = find_symbol q tables in
       wrap_to_store t' (f symbol) tail env tables lang task
    | Tlist t', s :: tail ->
       let pr_list = parse_list_qualid ~lang s in
       let pr_list = find_symbol_list pr_list tables in
       wrap_to_store t' (f pr_list) tail env tables lang task
    | Ttheory t', s :: tail ->
       let th = parse_theory env s in
       wrap_to_store t' (f th) tail env tables lang task
    | Tidentlist t', s :: tail ->
       let list = List.map (fun id -> id.Ptree.id_str) (parse_list_ident ~lang s) in
       wrap_to_store t' (f list) tail env tables lang task
    | Ttermlist t', s :: tail ->
       let term_list = parse_and_type_list ~lang ~as_fmla:false s tables in
       wrap_to_store t' (f term_list) tail env tables lang task
    | Ttermlist_same (arity, t'), s :: tail ->
        let n_firsts, lasts =
          try Lists.split arity (s :: tail) with
          | _ ->
              let msg = "list of " ^ string_of_int arity ^ " elements of same type" in
              let args = List.fold_left (fun acc x ->
                  if acc = "" then x else acc ^ " " ^ x) "" (s::tail) in
              raise (Arg_expected (msg, args))
        in
        let term_list = parse_list_same ~lang ~as_fmla:false n_firsts tables in
        wrap_to_store t' (f term_list) lasts env tables lang task
    | Topt (optname, t'), s :: s' :: tail when s = optname ->
       begin match t' with
        | Tint t' ->
          let arg = Some (parse_int s') in
          wrap_to_store t' (f arg) tail env tables lang task
        | Tprsymbol t' ->
           let q = parse_qualid ~lang s' in
           let arg = try Some (find_pr q tables) with
                    | Not_found -> raise (Arg_qid_not_found q) in
          wrap_to_store t' (f arg) tail env tables lang task
        | Tsymbol t' ->
           let q = parse_qualid ~lang s' in
           let arg = Some (find_symbol q tables) in
           wrap_to_store t' (f arg) tail env tables lang task
        | Tformula t' ->
           let arg = Some (parse_and_type ~lang ~as_fmla:true s' tables) in
           wrap_to_store t' (f arg) tail env tables lang task
        | Tterm t' ->
           let arg = Some (parse_and_type ~lang ~as_fmla:false s' tables) in
           wrap_to_store t' (f arg) tail env tables lang task
        | Ttheory t' ->
           let arg = Some (parse_theory env s') in
           wrap_to_store t' (f arg) tail env tables lang task
        | Tstring t' ->
           let arg = Some s' in
           wrap_to_store t' (f arg) tail env tables lang task
        | Tprlist t' ->
            let pr_list = parse_list_qualid ~lang s' in
            let pr_list = find_pr_list pr_list tables in
            let arg = Some pr_list in
            wrap_to_store t' (f arg) tail env tables lang task
        | Ttermlist t' ->
            let term_list = parse_and_type_list ~lang ~as_fmla:false s' tables in
            wrap_to_store t' (f (Some term_list)) tail env tables lang task
        | Tidentlist t' ->
            let list =
              List.map (fun id -> id.Ptree.id_str) (parse_list_ident ~lang s') in
            wrap_to_store t' (f (Some list)) tail env tables lang task
        | Tlist t' ->
            let pr_list = parse_list_qualid ~lang s' in
            let pr_list = find_symbol_list pr_list tables in
            wrap_to_store t' (f (Some pr_list)) tail env tables lang task
        | _ -> raise (Arg_expected (string_of_trans_typ t', s'))
       end
    | Topt (_, t'), _ ->
       wrap_to_store (trans_typ_tail t') (f None) l env tables lang task
    | Toptbool (optname, t'), s :: tail when s = optname ->
      wrap_to_store t' (f true) tail env tables lang task
    | Toptbool (_, t'), _ ->
      wrap_to_store t' (f false) l env tables lang task
    | _, [] -> raise (Arg_expected_none (string_of_trans_typ t))

let wrap_l : type a. (a, task list) trans_typ -> a -> trans_with_args_l =
  fun t f l env tables lang -> Trans.store (wrap_to_store t f l env tables lang)

let wrap   : type a. (a, task) trans_typ -> a -> trans_with_args =
  fun t f l env tables lang -> Trans.store (wrap_to_store t f l env tables lang)

let wrap_any : type a b. (a, b) trans_typ -> a -> string list -> Env.env ->
                    Trans.naming_table -> Env.fformat -> b trans =
  fun t f l env tables lang -> Trans.store (wrap_to_store t f l env tables lang)

(* the one in Scanf is awfully broken with respect to backslashes *)
let format_from_string s fmt =
  Scanf.sscanf_format (Printf.sprintf "%S" s) fmt (fun s -> s)

let wrap_and_register : type a b. desc:Pp.formatted -> string -> (a, b) trans_typ -> a -> unit =
  fun ~desc name t f  ->
    (* "%@\n" is escaped on purpose *)
    let type_desc = Format.asprintf "type: %a%@\n" print_type t in
    let type_desc = format_from_string type_desc Pp.empty_formatted in
    let desc = type_desc ^^ desc in
    let trans = wrap_any t f in
    match is_trans_typ_l t with
    | Yes -> Trans.register_transform_with_args_l ~desc name trans
    | No  -> Trans.register_transform_with_args   ~desc name trans


let find_symbol s tables =
  find_symbol (parse_qualid ~lang:Lexer.whyml_format s) tables
