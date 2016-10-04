open Task
open Ty
open Term
open Trans

type _ trans_typ =
  | Ttrans : (task -> task list) trans_typ
  | Tint : 'a trans_typ -> (int -> 'a) trans_typ
  | Tstring : 'a trans_typ -> (string -> 'a) trans_typ
  | Tty : 'a trans_typ -> (ty -> 'a) trans_typ
  | Ttysymbol : 'a trans_typ -> (tysymbol -> 'a) trans_typ
  | Tterm : 'a trans_typ -> (term -> 'a) trans_typ
  | Tformula : 'a trans_typ -> (term -> 'a) trans_typ

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
  | Tstring t' ->
    begin
      match l with
      | s :: tail -> wrap t' (f s) tail task
      | _ -> failwith "Missing argument: expecting a string."
    end
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
