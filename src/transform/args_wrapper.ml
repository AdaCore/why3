(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
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

exception Arg_parse_error of string * string
exception Arg_expected of string * string
exception Arg_theory_not_found of string
exception Arg_expected_none of string
exception Arg_qid_not_found of Ptree.qualid
exception Arg_error of string

let () = Exn_printer.register
    (fun fmt e ->
      match e with
      | Arg_parse_error (s1, s2) ->
          Format.fprintf fmt "Argument parsing error: %s \n %s" s2 s1
      | Arg_expected (ty, s) ->
          Format.fprintf fmt "Argument expected of type: %s\n Argument given: %s" ty s
      | Arg_theory_not_found s ->
          Format.fprintf fmt "Theory not found %s" s
      | Arg_expected_none s ->
          Format.fprintf fmt "Argument expected of type %s. None were given." s
      | _ -> raise e)

open Stdlib

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

let id_unique tables id = id_unique_label tables.printer id

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

let build_naming_tables task : naming_table =
  let sanitizer = sanitizer char_to_alpha char_to_alnumus in
  let pr = create_ident_printer Pretty.why3_keywords ~sanitizer in
  let km = Task.task_known task in
  let tables = {
      namespace = empty_ns;
      known_map = km;
      printer = pr;
  } in
(*  We want conflicting names to be named as follows:
    names closer to the goal should be named with lowest
    disambiguation numbers.
    This only works for things defined in .why/.mlw because things
    added by the user are renamed on the fly. *)
  (* TODO:imported theories should be added in the namespace too *)
  let l = Mid.fold (fun _id d acc -> d :: acc) km [] in
  List.fold_left (fun tables d -> add d tables) tables l

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
  | Tidentlist : ('a, 'b) trans_typ -> ((string list -> 'a), 'b) trans_typ
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


let type_ptree ~as_fmla t tables =
  let km = tables.known_map in
  let ns = tables.namespace in
  if as_fmla
  then Typing.type_fmla_in_namespace ns km (fun _ -> None) t
  else Typing.type_term_in_namespace ns km (fun _ -> None) t

exception Arg_parse_type_error of Loc.position * string * exn

let parse_and_type ~as_fmla s task =
  try
    let lb = Lexing.from_string s in
    let t =
      Lexer.parse_term lb
    in
    let t =
      type_ptree ~as_fmla:as_fmla t task
    in
    t
  with
  | Loc.Located (loc, e) -> raise (Arg_parse_type_error (loc, s, e))

let parse_qualid s =
  try
    let lb = Lexing.from_string s in
    Lexer.parse_qualid lb
  with
  | Loc.Located (loc, e) -> raise (Arg_parse_type_error (loc, s, e))

let parse_list_qualid s =
  try
    let lb = Lexing.from_string s in
    Lexer.parse_list_qualid lb
  with
  | Loc.Located (loc, e) -> raise (Arg_parse_type_error (loc, s, e))

let parse_list_ident s =
  try
    let lb = Lexing.from_string s in
    Lexer.parse_list_ident lb
  with
  | Loc.Located (loc, e) -> raise (Arg_parse_type_error (loc, s, e))

let parse_int s =
  try int_of_string s
  with Failure _ -> raise (Arg_parse_error (s,"int expected"))

let parse_theory env s =
  try
    let path, name = match Strings.split '.' s with
      | [name] -> [],name
      | path::[name] ->
        let path = Strings.split '/' path in
        path, name
      | _ -> raise (Arg_parse_error (s,"Ill-formed theory name"))
    in
    Env.read_theory env path name
  with
    _ -> raise (Arg_theory_not_found s)

let trans_typ_tail: type a b c. (a -> b, c) trans_typ -> (b, c) trans_typ =
  fun t ->
    match t with
    | Tint t      -> t
    | Tty t       -> t
    | Ttysymbol t -> t
    | Tprsymbol t -> t
    | Tprlist t   -> t
    | Tlsymbol t  -> t
    | Tsymbol t   -> t
    | Tlist t     -> t
    | Tterm t     -> t
    | Tstring t   -> t
    | Tformula t  -> t
    | Ttheory t   -> t
    | _           -> assert false

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
    | Ttheory _      -> "theory"
    | Topt (s,t)     -> "?" ^ s ^ (string_of_trans_typ t)
    | Toptbool (s,_) -> "?" ^ s ^ ":bool"

let rec print_type : type a b. (a, b) trans_typ -> string =
  fun t ->
    match t with
    | Ttrans         -> "task"
    | Ttrans_l       -> "list task"
    | Tenvtrans      -> "env -> task"
    | Tenvtrans_l    -> "env -> list task"
    | Tint t         -> "integer -> " ^ print_type t
    | Tstring t      -> "string -> " ^ print_type t
    | Tty t          -> "type -> " ^ print_type t
    | Ttysymbol t    -> "type_symbol -> " ^ print_type t
    | Tprsymbol t    -> "prsymbol -> " ^ print_type t
    | Tprlist t      -> "list prsymbol -> " ^ print_type t
    | Tlsymbol t     -> "lsymbol -> " ^ print_type t
    | Tsymbol t      -> "symbol -> " ^ print_type t
    | Tlist t        -> "list symbol -> " ^ print_type t
    | Tterm t        -> "term -> " ^ print_type t
    | Tformula t     -> "formula -> " ^ print_type t
    | Tidentlist t    -> "list ident -> " ^ print_type t
    | Ttheory t      -> "theory -> " ^ print_type t
    | Topt (s,t)     -> "?" ^ s ^ ":" ^ print_type t
    | Toptbool (s,t) -> "?" ^ s ^ ":bool -> " ^ print_type t

exception Unnecessary_arguments of string list

let rec wrap_to_store : type a b. (a, b) trans_typ -> a -> string list -> Env.env -> naming_table -> task -> b =
  fun t f l env tables task ->
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
      let arg = parse_int s in wrap_to_store t' (f arg) tail env tables task
    | Tstring t', s :: tail ->
       wrap_to_store t' (f s) tail env tables task
    | Tformula t', s :: tail ->
      let te = parse_and_type ~as_fmla:true s tables in
      wrap_to_store t' (f te) tail env tables task
    | Tterm t', s :: tail ->
      let te = parse_and_type ~as_fmla:false s tables in
      wrap_to_store t' (f te) tail env tables task
    | Tty t', _s :: tail ->
      let ty = Ty.ty_int in (* TODO: parsing + typing of s *)
      wrap_to_store t' (f ty) tail env tables task
    | Ttysymbol t', _s :: tail ->
      let tys = Ty.ts_int in (* TODO: parsing + typing of s *)
      wrap_to_store t' (f tys) tail env tables task
    | Tprsymbol t', s :: tail ->
       let q = parse_qualid s in
       let pr = try (find_pr q tables) with
                | Not_found -> raise (Arg_qid_not_found q) in
      wrap_to_store t' (f pr) tail env tables task
    | Tprlist t', s :: tail ->
        let pr_list = parse_list_qualid s in
        let pr_list =
        List.map (fun id ->
                    try find_pr id tables with
                    | Not_found -> raise (Arg_qid_not_found id))
                 pr_list in
        wrap_to_store t' (f pr_list) tail env tables task
    | Tlsymbol t', s :: tail ->
       let q = parse_qualid s in
       let pr = try (find_ls q tables) with
               | Not_found -> raise (Arg_qid_not_found q) in
      wrap_to_store t' (f pr) tail env tables task
    | Tsymbol t', s :: tail ->
       let q = parse_qualid s in
       let symbol = find_symbol q tables in
       wrap_to_store t' (f symbol) tail env tables task
    | Tlist t', s :: tail ->
       let pr_list = parse_list_qualid s in
       let pr_list =
         List.map (fun id -> find_symbol id tables) pr_list in
       wrap_to_store t' (f pr_list) tail env tables task
    | Ttheory t', s :: tail ->
       let th = parse_theory env s in
       wrap_to_store t' (f th) tail env tables task
    | Tidentlist t', s :: tail ->
       let list = List.map (fun id -> id.Ptree.id_str) (parse_list_ident s) in
       wrap_to_store t' (f list) tail env tables task
    | Topt (optname, t'), s :: s' :: tail when s = optname ->
       begin match t' with
        | Tint t' ->
          let arg = Some (parse_int s') in
          wrap_to_store t' (f arg) tail env tables task
        | Tprsymbol t' ->
           let q = parse_qualid s' in
           let arg = try Some (find_pr q tables) with
                    | Not_found -> raise (Arg_qid_not_found q) in
          wrap_to_store t' (f arg) tail env tables task
        | Tsymbol t' ->
           let q = parse_qualid s' in
           let arg = Some (find_symbol q tables) in
           wrap_to_store t' (f arg) tail env tables task
        | Tformula t' ->
           let arg = Some (parse_and_type ~as_fmla:true s' tables) in
           wrap_to_store t' (f arg) tail env tables task
        | Tterm t' ->
           let arg = Some (parse_and_type ~as_fmla:false s' tables) in
           wrap_to_store t' (f arg) tail env tables task
        | Ttheory t' ->
           let arg = Some (parse_theory env s') in
           wrap_to_store t' (f arg) tail env tables task
        | Tstring t' ->
           let arg = Some s' in
           wrap_to_store t' (f arg) tail env tables task
        | _ -> raise (Arg_expected (string_of_trans_typ t', s'))
       end
    | Topt (_, t'), _ ->
       wrap_to_store (trans_typ_tail t') (f None) l env tables task
    | Toptbool (optname, t'), s :: tail when s = optname ->
      wrap_to_store t' (f true) tail env tables task
    | Toptbool (_, t'), _ ->
      wrap_to_store t' (f false) l env tables task
    | _, [] -> raise (Arg_expected_none (string_of_trans_typ t))

let wrap_l : type a. (a, task list) trans_typ -> a -> trans_with_args_l =
  fun t f l env tables -> Trans.store (wrap_to_store t f l env tables)

let wrap   : type a. (a, task) trans_typ -> a -> trans_with_args =
  fun t f l env tables -> Trans.store (wrap_to_store t f l env tables)

let wrap_any : type a b. (a, b) trans_typ -> a -> string list -> Env.env ->
                    Trans.naming_table -> b trans =
  fun t f l env tables -> Trans.store (wrap_to_store t f l env tables)

let wrap_and_register : type a b. desc:Pp.formatted -> string -> (a, b) trans_typ -> a -> unit =
  fun ~desc name t f  ->
    let type_desc = Scanf.format_from_string ("type : " ^ print_type t ^ "\n") Pp.empty_formatted in
    let trans = wrap_any t f in
    match is_trans_typ_l t with
    | Yes ->
      Trans.register_transform_with_args_l ~desc:(type_desc ^^ desc) name trans
    | No ->
      Trans.register_transform_with_args ~desc:(type_desc ^^ desc) name trans


let find_symbol s tables = find_symbol (parse_qualid s) tables
