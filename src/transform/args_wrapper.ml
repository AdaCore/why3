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

type name_tables = {
    namespace : namespace;
    known_map : known_map;
    printer : ident_printer;
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
  (* TODO: add also the projections *)
  List.fold_left
    (fun tables (c: constructor) ->
      let id = (fst c).ls_name in
      let s = id_unique tables.printer id in
      add_unsafe s (Ls (fst c)) tables)
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
  | Dprop (_, pr, _) ->
      (* Only pr is new in Dprop (see create_prop_decl) *)
      let id = pr.pr_name in
      let s = id_unique tables.printer id in
      add_unsafe s (Pr pr) tables


let build_name_tables task : name_tables =
(*
  TODO:
   - simply use [km = Task.task_known task] as the set of identifiers
     to insert in the tables
   - only one printer (do not attempt te rebuild qualified idents)
   - use syntax_map from why3_itp driver
   - to build the namespace, do a match on the decl associated with the id
      in [km]
  | Dtype  -> tysymbol
  | Ddata | Dparam | Dlogic | Dind  -> lsymbol
  | Dprop  -> prsymbol

  TODO: use the result of this function in
    - a new variant of a printer in this file
    - use the namespace to type the terms
      (change the code in parser/typing.ml to use namespace
      instead of theory_uc)

*)
  let pr = fresh_printer () in
  let km = Task.task_known task in
  let tables = {
      namespace = empty_ns;
      known_map = km;
(*
      unique_names = Mid.empty ;
 *)
      printer = pr;
  } in
  Mid.fold
    (fun _id d tables ->
(* TODO optimization. We may check if id is already there to not explore twice the same
   declaration ? *)
      add d tables)
    km
    tables



(************* wrapper  *************)

type _ trans_typ =
  | Ttrans : (task -> task list) trans_typ
  | Tint : 'a trans_typ -> (int -> 'a) trans_typ
(*
  | Tstring : 'a trans_typ -> (string -> 'a) trans_typ
*)
  | Tty : 'a trans_typ -> (ty -> 'a) trans_typ
  | Ttysymbol : 'a trans_typ -> (tysymbol -> 'a) trans_typ
  | Tprsymbol : 'a trans_typ -> (Decl.prsymbol -> 'a) trans_typ
  | Tterm : 'a trans_typ -> (term -> 'a) trans_typ
  | Tformula : 'a trans_typ -> (term -> 'a) trans_typ

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

(*
(*** term argument parsed in the context of the task ***)
let type_ptree ~as_fmla t task =
  let used_ths = Task.used_theories task in
  let used_symbs = Task.used_symbols used_ths in
  let local_decls = Task.local_decls task used_symbs in
  (* rebuild a theory_uc *)
  let th_uc = Theory.create_theory (Ident.id_fresh "dummy") in
  let th_uc =
    Ident.Mid.fold
      (fun _id th acc ->
       let name = th.Theory.th_name in
       (**)
       Format.eprintf "[Args_wrapper.type_ptree] use theory %s (%s)@."
                      _id.Ident.id_string
                      name.Ident.id_string;
       (**)
       Theory.close_namespace
         (Theory.use_export
            (Theory.open_namespace acc name.Ident.id_string)
            th)
         true)
      used_ths th_uc
  in
  let th_uc =
    List.fold_left
      (fun acc d ->
       (**)
       Format.eprintf "[Args_wrapper.type_ptree] add decl %a@."
                      Pretty.print_decl d;
       (**)
       Theory.add_decl ~warn:false acc d)
      th_uc local_decls
  in
  if as_fmla
  then Typing.type_fmla th_uc (fun _ -> None) t
  else Typing.type_term th_uc (fun _ -> None) t
 *)

let parse_and_type ~as_fmla s task =
  let lb = Lexing.from_string s in
  let t =
      Lexer.parse_term lb
  in
  let t =
      type_ptree ~as_fmla:as_fmla t task
  in
  t

let rec wrap : type a. a trans_typ -> a -> trans_with_args =
  fun t f l task ->
  match t with
  | Ttrans -> f task
  | Tint t' ->
    begin
      match l with
      | s :: tail ->
        (try
          let n = int_of_string s in
          wrap t' (f n) tail task
        with Failure _ -> raise (Failure "Parsing error: expecting an integer."))
      | _ -> failwith "Missing argument: expecting an integer."
    end
(*
  | Tstring t' ->
    begin
      match l with
      | s :: tail -> wrap t' (f s) tail task
      | _ -> failwith "Missing argument: expecting a string."
    end
 *)
  | Tformula t' ->
    begin
      match l with
      | s :: tail ->
         let te = parse_and_type ~as_fmla:true s task in
         wrap t' (f te) tail task
      | _ -> failwith "Missing argument: expecting a formula."
    end
  | Tterm t' ->
    begin
      match l with
      | s :: tail ->
         let te = parse_and_type ~as_fmla:false s task in
         wrap t' (f te) tail task
      | _ -> failwith "Missing argument: expecting a term."
    end
  | Tty t' ->
    begin
      match l with
      | _s :: tail ->
         let ty = Ty.ty_int in (* TODO: parsing + typing of s *)
         wrap t' (f ty) tail task
      | _ -> failwith "Missing argument: expecting a type."
    end
  | Ttysymbol t' ->
    begin
      match l with
      | _s :: tail ->
         let tys = Ty.ts_int in (* TODO: parsing + typing of s *)
         wrap t' (f tys) tail task
      | _ -> failwith "Missing argument: expecting a type symbol."
    end
  | Tprsymbol t' ->
    begin
      match l with
        | s :: tail ->
          let pr = find_pr s task in
          wrap t' (f pr) tail task
      | _ -> failwith "Missing argument: expecting a prop symbol."
    end
