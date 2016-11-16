open Task
open Ty
open Term
open Trans
open Ident
open Theory
open Decl

let fresh_printer =
  let bl = ["theory"; "type"; "function"; "predicate"; "inductive";
            "axiom"; "lemma"; "goal"; "use"; "clone"; "prop"; "meta";
            "namespace"; "import"; "export"; "end";
            "forall"; "exists"; "not"; "true"; "false"; "if"; "then"; "else";
            "let"; "in"; "match"; "with"; "as"; "epsilon" ] in
(*
  let isanitize = sanitizer char_to_alpha char_to_alnumus in
 *)
  fun () -> create_ident_printer bl (* ~sanitizer:isanitize *)


open Stdlib

let sanitizer x = x (*sanitizer char_to_lalpha char_to_lalpha x*)

let id_unique printer id =
  id_unique_label printer ~sanitizer:sanitizer id


type id_decl = (Decl.decl list) Ident.Mid.t

type name_tables = {
    namespace : namespace;
    known_map : known_map;
    printer : ident_printer;
(* Associate an id to a list of declarations in which it is used *)
    id_decl : id_decl;
  }

(* Use symb to encapsulate ids into correct categories of symbols *)
type symb =
  | Ts of tysymbol
  | Ls of lsymbol
  | Pr of prsymbol

(* [add_unsafe s id tables] Add (s, id) to tables without any checking. *)
let add_unsafe (s: string) (id: symb) (tables: name_tables) : name_tables =
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

(* Adds symbols that are introduced to a constructor *)
let constructor_add (cl: constructor list) tables : name_tables =
  List.fold_left
    (fun tables ((ls, cl): constructor) ->
      let tables = List.fold_left
          (fun tables (cs: lsymbol option) ->
            match cs with
            | Some cs ->
                let id = cs.ls_name in
                let s = id_unique tables.printer id in
                add_unsafe s (Ls cs) tables
            | None -> tables) tables cl in
      let id = ls.ls_name in
      let s = id_unique tables.printer id in
      add_unsafe s (Ls ls) tables)
    tables
    cl

(* Add symbols that are introduced by an inductive *)
let ind_decl_add il tables =
  List.fold_left
    (fun tables ((pr, _): prsymbol * term) ->
      let id = pr.pr_name in
      let s = id_unique tables.printer id in
      add_unsafe s (Pr pr) tables)
    il
    tables

let rec insert l d =
  match l with
  | hd :: tl -> if hd == d then l else hd :: insert tl d
  | [] -> [d]

let add_decls_id id d tables =
  let l = try (Ident.Mid.find id tables.id_decl) with
  | Not_found -> [] in
  {tables with id_decl = Ident.Mid.add id (insert l d) tables.id_decl}

(* [add_id tables d t] To all identifiants id used in t, adds the associated
   declaration d in the table.id_decl *)
let rec add_id tables d t =
  match t.t_node with
  | Tvar v -> add_decls_id v.vs_name d tables
  | Tconst _ | Ttrue | Tfalse -> tables
  | Tapp (l, tl) ->
      let tables = add_decls_id l.ls_name d tables in
      List.fold_left (fun tables t -> add_id tables d t) tables tl
  | Tlet (t, tb) ->
      let tables = add_id tables d t in
      let (_v1, t1) = t_open_bound tb in
      add_id tables d t1
  | Tcase (t, tbl) ->
      let tables = add_id tables d t in
      List.fold_left (fun tables ob ->
        let (_pat, t) = t_open_branch ob in
        add_id tables d t) tables tbl
  | Teps (tb) ->
      let (_v, t) = t_open_bound tb in
      add_id tables d t
  | Tquant (_, tq) ->
      let (_vl, _, t) = t_open_quant tq in
      add_id tables d t
  | Tbinop (_, t1, t2) ->
      let tables = add_id tables d t1 in
      add_id tables d t2
  | Tnot (t) ->
      add_id tables d t
  | Tif (t1, t2, t3) ->
      let tables = add_id tables d t1 in
      let tables = add_id tables d t2 in
      add_id tables d t3

(* [add d printer tables] Adds all new declaration of symbol inside d to tables.
  It uses printer to give them a unique name and also register these new names in printer *)
let add (d: decl) (tables: name_tables): name_tables =
  match d.d_node with
  | Dtype ty ->
      (* only current symbol is new in the declaration (see create_ty_decl) *)
      let id = ty.ts_name in
      let s = id_unique tables.printer id in
      add_unsafe s (Ts ty) tables
  | Ddata dl ->
      (* first part is new. Also only first part of each constructor seem new
         (see create_data_decl) *)
      List.fold_left
        (fun tables (dd: data_decl) ->
          let id = (fst dd).ts_name in
          let s = id_unique tables.printer id in
          let tables = add_unsafe s (Ts (fst dd)) tables in
          constructor_add (snd dd) tables)
        tables
        dl
  | Dparam ls ->
      (* Only one lsymbol which is new *)
      let id = ls.ls_name in
      let s = id_unique tables.printer id in
      add_unsafe s (Ls ls) tables
  | Dlogic lsd ->
      (* Only first part of logic_decl is new (see create_logic) *)
      List.fold_left
        (fun tables ((ls,_): logic_decl) ->
          let id = ls.ls_name in
          let s = id_unique tables.printer id in
          add_unsafe s (Ls ls) tables)
        tables
        lsd
  | Dind (_is, il) ->
      (* Every symbol is new except symbol inside terms (see create_ind_decl) *)
      List.fold_left
        (fun tables ((ls,ind): ind_decl) ->
          let id = ls.ls_name in
          let s = id_unique tables.printer id in
          let tables = add_unsafe s (Ls ls) tables in
          ind_decl_add tables ind)
        tables
        il
  | Dprop (_, pr, t) ->
      (* Only pr is new in Dprop (see create_prop_decl) *)
      let id = pr.pr_name in
      let s = id_unique tables.printer id in
      let tables = add_unsafe s (Pr pr) tables in
      add_id tables d t


let build_name_tables task : name_tables =
  let pr = fresh_printer () in
  let km = Task.task_known task in
  let empty_decls = Ident.Mid.empty in
  let tables = {
      namespace = empty_ns;
      known_map = km;
      printer = pr;
      id_decl = empty_decls
  } in
(*  We want conflicting names to be named as follows:
    names closer to the goal should be named with lowest
    disambiguation numbers.
    This only works for things defined in .why/.mlw because things
    added by the user are renamed on the fly. *)
  let l = Mid.fold (fun _id d acc -> d :: acc) km [] in
  List.fold_left (fun tables d -> add d tables) tables l


(************* wrapper  *************)

type (_, _) trans_typ =
  | Ttrans    : ((task trans), task) trans_typ
  | Ttrans_l  : ((task tlist), task list) trans_typ
  | Tint      : ('a, 'b) trans_typ -> ((int -> 'a), 'b) trans_typ
  | Tty       : ('a, 'b) trans_typ -> ((ty -> 'a), 'b) trans_typ
  | Ttysymbol : ('a, 'b) trans_typ -> ((tysymbol -> 'a), 'b) trans_typ
  | Tprsymbol : ('a, 'b) trans_typ -> ((Decl.prsymbol -> 'a), 'b) trans_typ
  | Tprsymbolopt : string * ('a, 'b) trans_typ -> ((Decl.prsymbol option -> 'a), 'b) trans_typ
  | Tterm     : ('a, 'b) trans_typ -> ((term -> 'a), 'b) trans_typ
  | Tstring   : ('a, 'b) trans_typ -> ((string -> 'a), 'b) trans_typ
  | Tformula  : ('a, 'b) trans_typ -> ((term -> 'a), 'b) trans_typ
  | Ttheory   : ('a, 'b) trans_typ -> ((Theory.theory -> 'a), 'b) trans_typ
  | Tenv      : ('a, 'b) trans_typ -> ((Env.env -> 'a), 'b) trans_typ

let find_pr s task =
  let tables = build_name_tables task in
  Mstr.find s tables.namespace.ns_pr

let type_ptree ~as_fmla t task =
  let tables = build_name_tables task in
  let km = tables.known_map in
  let ns = tables.namespace in
  if as_fmla
  then Typing.type_fmla_in_namespace ns km (fun _ -> None) t
  else Typing.type_term_in_namespace ns km (fun _ -> None) t

let parse_and_type ~as_fmla s task =
  let lb = Lexing.from_string s in
  let t =
      Lexer.parse_term lb
  in
  let t =
      type_ptree ~as_fmla:as_fmla t task
  in
  t

let last_trans: type a b. (a, b) trans_typ -> bool = function
  | Ttrans -> true
  | Ttrans_l -> true
  | _ -> false

let rec wrap_to_store : type a b. (a, b) trans_typ -> a -> string list -> Env.env -> task -> b =
  fun t f l env task ->
    match t with
    | Ttrans -> apply f task
    | Ttrans_l -> apply f task
    | Tint t' ->
      begin
        match l with
        | s :: tail ->
          (try
             let n = int_of_string s in
             wrap_to_store t' (f n) tail env task
           with Failure _ -> raise (Failure "Parsing error: expecting an integer."))
        | _ -> failwith "Missing argument: expecting an integer."
      end
    | Tformula t' ->
      begin
        match l with
        | s :: tail ->
          let te = parse_and_type ~as_fmla:true s task in
          wrap_to_store t' (f te) tail env task
        | _ -> failwith "Missing argument: expecting a formula."
      end
    | Tterm t' ->
      begin
        match l with
        | s :: tail ->
          let te = parse_and_type ~as_fmla:false s task in
          wrap_to_store t' (f te) tail env task
        | _ -> failwith "Missing argument: expecting a term."
      end
    | Tty t' ->
      begin
        match l with
        | _s :: tail ->
          let ty = Ty.ty_int in (* TODO: parsing + typing of s *)
          wrap_to_store t' (f ty) tail env task
        | _ -> failwith "Missing argument: expecting a type."
      end
    | Ttysymbol t' ->
      begin
        match l with
        | _s :: tail ->
          let tys = Ty.ts_int in (* TODO: parsing + typing of s *)
          wrap_to_store t' (f tys) tail env task
        | _ -> failwith "Missing argument: expecting a type symbol."
      end
    | Tprsymbol t' ->
      begin
        match l with
        | s :: tail ->
          let pr = find_pr s task in
          wrap_to_store t' (f pr) tail env task
        | _ -> failwith "Missing argument: expecting a prop symbol."
      end
    | Tprsymbolopt(argname,t') ->
      begin
        match l with
        | s :: s' :: tail when s = argname ->
             let pr = find_pr s' task in
             wrap_to_store t' (f (Some pr)) tail env task
        | _ ->
             wrap_to_store t' (f None) l env task
      end
    | Ttheory t' ->
      begin
        match l with
        | s :: tail ->
          (try
             let path, name = match Strings.split '.' s with
               | [name] -> [],name
               | path::[name] ->
                 let path = Strings.split '/' path in
                 path, name
               | _ -> failwith "Ill-formed theory name"
             in
             let th = Env.read_theory env path name in
             wrap_to_store t' (f th) tail env task
          with
            _ ->  failwith "Theory not found.")
        | _ -> failwith "Missing argument: expecting a theory."
      end
(* TODO: Tstring is an optional argument if given last. Replaced by a new ident for "h" if
   no arguments is given *)
(* TODO: ugly. Did not know how to use function trans for this. Did not investigate further *)
    | Tstring t' when (last_trans t') ->
        begin
          match l with
          | [] -> (* No more arguments, we build a string *)
              let p = (build_name_tables task).printer in
              let id = Decl.create_prsymbol (Ident.id_fresh "h") in
              let new_name = Ident.id_unique p id.pr_name in
              wrap_to_store t' (f new_name) [] env task
          | s :: tail ->
              let p = (build_name_tables task).printer in
              let id = Decl.create_prsymbol (Ident.id_fresh s) in
              let new_name = Ident.id_unique p id.pr_name in
              wrap_to_store t' (f new_name) tail env task
        end
    | Tstring t' ->
        begin
          match l with
          | s :: tail ->
              let p = (build_name_tables task).printer in
              let id = Decl.create_prsymbol (Ident.id_fresh s) in
              let new_name = Ident.id_unique p id.pr_name in
              wrap_to_store t' (f new_name) tail env task
          | _ -> failwith "Missing argument: expecting a string."
        end
    | Tenv t' ->
        begin
          match l with
          | _ ->
              wrap_to_store t' (f env) l env task
        end

let wrap_l : type a. (a, task list) trans_typ -> a -> trans_with_args_l =
  fun t f l env -> Trans.store (wrap_to_store t f l env)

let wrap   : type a. (a, task) trans_typ -> a -> trans_with_args =
  fun t f l env -> Trans.store (wrap_to_store t f l env)
