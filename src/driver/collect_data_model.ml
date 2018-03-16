(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Stdlib
open Smt2_model_defs

exception Not_value


(* Printing function *)
let print_table t =
  Format.eprintf "Table key and value@.";
  Mstr.iter (fun key e -> Format.eprintf "%s %a@." key print_def (snd e)) t;
  Format.eprintf "End table@."


(* Adds all referenced cvc4 variables found in the term t to table *)
let rec get_variables_term (table: correspondence_table) t =
  match t with
  | Variable _ | Function_Local_Variable _ | Boolean _ | Integer _
  | Decimal _ | Fraction _ | Float _ | Other _ | Bitvector _ -> table
  | Array a ->
    get_variables_array table a
  | Ite (t1, t2, t3, t4) ->
    let table = get_variables_term table t1 in
    let table = get_variables_term table t2 in
    let table = get_variables_term table t3 in
    let table = get_variables_term table t4 in
    table
  | Cvc4_Variable cvc ->
    if Mstr.mem cvc table then
      table
    else
      Mstr.add cvc (false, Noelement) table
  | Record (_, l) ->
    List.fold_left (fun table (_f, t) -> get_variables_term table t) table l
  | To_array t ->
    get_variables_term table t
  | Apply (_s, lt) ->
      List.fold_left (fun table t -> get_variables_term table t) table lt


and get_variables_array table a =
   match a with
   | Const t ->
    let table = get_variables_term table t in
    table
   | Store (a, t1, t2) ->
     let table = get_variables_array table a in
     let table = get_variables_term table t1 in
     get_variables_term table t2

let get_all_var (table: correspondence_table) =
  Mstr.fold (fun _key element table ->
    match element with
    | _, Noelement -> table
    | _, Function (_, t) -> get_variables_term table t
    | _, Term t -> get_variables_term table t) table table

exception Bad_variable

(* Get the "radical" of a variable *)
let remove_end_num s =
  let n = ref (String.length s - 1) in
  if !n <= 0 then s else
  begin
    while String.get s !n <= '9' && String.get s !n >= '0' && !n >= 0 do
      n := !n - 1
    done;
    try
      String.sub s 0 (!n + 1)
    with
    | _ -> s
  end

(* Add the variables that can be deduced from ITE to the table of variables *)
let add_vars_to_table table value =
  let rec add_vars_to_table ~type_value (table: correspondence_table) value =
    match value with
    | Ite (Cvc4_Variable cvc, Function_Local_Variable _x, t1, t2) ->
        begin
          let table = Mstr.add cvc (false, Term t1) table in
          add_vars_to_table ~type_value table t2
        end
    | Ite (Function_Local_Variable _x, Cvc4_Variable cvc, t1, t2) ->
        begin
          let table = Mstr.add cvc (false, Term t1) table in
          add_vars_to_table ~type_value table t2
        end
    | Ite (t, Function_Local_Variable _x, Cvc4_Variable cvc, t2) ->
        begin
          let table = Mstr.add cvc (false, Term t) table in
          add_vars_to_table ~type_value table t2
        end
    | Ite (Function_Local_Variable _x, t, Cvc4_Variable cvc, t2) ->
        begin
          let table = Mstr.add cvc (false, Term t) table in
          add_vars_to_table ~type_value table t2
        end
    | Ite (_, _, _, _) -> table
    | _ ->
      begin
        match type_value with
        | None -> table
        | Some type_value ->
            Mstr.fold (fun key (_b, elt) acc ->
              let match_str_z3 = type_value ^ "!" in
              let match_str_cvc4 = "_" ^ type_value ^ "_" in
              let match_str = Str.regexp ("\\(" ^ match_str_z3 ^ "\\|" ^ match_str_cvc4 ^ "\\)") in
              match Str.search_forward match_str (remove_end_num key) 0 with
              | exception Not_found -> acc
              | _ ->
                  if elt == Noelement then
                    Mstr.add key (false, Term value) acc
                  else
                    acc)
              table table
      end
  in

  let type_value, t = match (snd value) with
  | Term t -> (None, t)
  | Function (cvc_var_list, t) ->
    begin
      match cvc_var_list with
      | [(_, type_value)] -> (type_value, t)
      | _ -> (None, t)
    end
  | Noelement -> raise Bad_variable in

  add_vars_to_table ~type_value table t

let rec refine_definition table t =
  match t with
  | Term t -> Term (refine_function table t)
  | Function (vars, t) -> Function (vars, refine_function table t)
  | Noelement -> Noelement

and refine_array table a =
  match a with
  | Const t ->
    let t = refine_function table t in
    Const t
  | Store (a, t1, t2) ->
    let a = refine_array table a in
    let t1 = refine_function table t1 in
    let t2 = refine_function table t2 in
    Store (a, t1, t2)

(* This function takes the table of assigned variables and a term and replace
   the variables with the constant associated with them in the table. If their
   value is not a constant yet, recursively apply on these variables and update
   their value. *)
and refine_function table term =
  match term with
  | Integer _ | Decimal _ | Float _ | Fraction _
    | Other _ | Bitvector _ | Boolean _ -> term
  | Cvc4_Variable v ->
    begin
      try (
      let (b, t) = Mstr.find v table in
      let t = match t with
      | Term t -> t
      | Function (_vars, t) -> t
      | Noelement -> raise Not_value
      in
      if b then
        t
      else
        let table = refine_variable_value table v (b, Term t) in
        let t = match (snd (Mstr.find v table)) with
        | Term t -> t
        | Function (_vars, t) -> t
        | Noelement -> raise Not_value in
        t
       ) with
      | Not_found -> term
      | Not_value -> term
    end
  | Function_Local_Variable _ -> term
  | Variable _ -> term
  | Ite (t1, t2, t3, t4) ->
    let t1 = refine_function table t1 in
    let t2 = refine_function table t2 in
    let t3 = refine_function table t3 in
    let t4 = refine_function table t4 in
    Ite (t1, t2, t3, t4)
  | Array a ->
    Array (refine_array table a)
  | Record (n, l) ->
    Record (n, List.map (fun (f, v) -> f, refine_function table v) l)
  | To_array t ->
    To_array (refine_function table t)
  | Apply (s, lt) ->
    Apply (s, List.map (refine_function table) lt)


and refine_variable_value (table: correspondence_table) key v =
  let (b, t) = v in
  if b then
    table
  else
    let tv = refine_definition table t in
    Mstr.add key (true, tv) table

(* Conversion to value referenced as defined in model_parser.
   We assume that array indices fit into an integer *)
let convert_to_indice t =
  match t with
  | Integer i -> i
  | Bitvector bv -> bv
  | Boolean b -> string_of_bool b
  | _ -> raise Not_value

let rec convert_array_value (a: array) : Model_parser.model_array =
  let array_indices = ref [] in

  let rec create_array_value a =
    match a with
    | Const t -> { Model_parser.arr_indices = !array_indices;
                   Model_parser.arr_others = convert_to_model_value t}
    | Store (a, t1, t2) ->
        let new_index =
          { Model_parser.arr_index_key = convert_to_indice t1;
            Model_parser.arr_index_value = convert_to_model_value t2} in
        array_indices := new_index :: !array_indices;
        create_array_value a in
  create_array_value a

and convert_to_model_value (t: term): Model_parser.model_value =
  match t with
  | Integer i -> Model_parser.Integer i
  | Decimal (d1, d2) -> Model_parser.Decimal (d1, d2)
  | Fraction (s1, s2) -> Model_parser.Fraction (s1, s2)
  | Float f -> Model_parser.Float f
  | Bitvector bv -> Model_parser.Bitvector bv
  | Boolean b -> Model_parser.Boolean b
  | Other _s -> raise Not_value
  | Array a -> Model_parser.Array (convert_array_value a)
  | Record (_n, l) ->
      Model_parser.Record (convert_record l)
  | Cvc4_Variable _v -> raise Not_value (*Model_parser.Unparsed "!"*)
  (* TODO change the value returned for non populated Cvc4 variable '!' -> '?' ? *)
  | To_array t -> convert_to_model_value (Array (convert_z3_array t))
  | Apply (s, lt) -> Model_parser.Apply (s, List.map convert_to_model_value lt)
  | Function_Local_Variable _ | Variable _ | Ite _ -> raise Not_value

and convert_z3_array (t: term) : array =

  let rec convert_array t =
    match t with
    (* This works for multidim array because, we call convert_to_model_value on
       the new array generated (which will still contain a To_array).
       Example of value for multidim array:
       To_array (Ite (x, 1, (To_array t), To_array t')) -> call on complete term ->
       Store (1, To_array t, To_array t') -> call on subpart (To_array t) ->
       Store (1, Const t, To_array t') -> call on subpart (To_array t') ->
       Store (1, Const t, Const t')
     *)

    | Ite (Function_Local_Variable _x, if_t, t1, t2) ->
      Store (convert_array t2, if_t, t1)
    | Ite (if_t, Function_Local_Variable _x, t1, t2) ->
      Store (convert_array t2, if_t, t1)
    | t -> Const t
  in
  convert_array t

and convert_record l =
  List.map (fun (f, v) -> f, convert_to_model_value v) l

let convert_to_model_element name t =
  match t with
  | None -> raise Not_value
  | Some t ->
      let value = convert_to_model_value t in
      Model_parser.create_model_element ~name ~value ()

let apply_to_record (list_records: (string list) Mstr.t) (t: term) =

  let rec array_apply_to_record (a: array) =
    match a with
    | Const x ->
        let x = apply_to_record x in
        Const x
    | Store (a, t1, t2) ->
        let a = array_apply_to_record a in
        let t1 = apply_to_record t1 in
        let t2 = apply_to_record t2 in
        Store (a, t1, t2)

  and apply_to_record (v: term) =
    match v with
    | Integer _ | Decimal _ | Fraction _ | Float _ | Boolean _ | Bitvector _
    | Cvc4_Variable _ | Function_Local_Variable _ | Variable _ | Other _ -> v
    | Array a ->
        Array (array_apply_to_record a)
    | Record (s, l) ->
        let l = List.map (fun (f,v) -> f, apply_to_record v) l in
        Record (s, l)
    | Apply (s, l) ->
        let l = List.map apply_to_record l in
        if Mstr.mem s list_records then
          Record (s, List.combine (Mstr.find s list_records) l)
        else
          Apply (s, l)
    | Ite (t1, t2, t3, t4) ->
        let t1 = apply_to_record t1 in
        let t2 = apply_to_record t2 in
        let t3 = apply_to_record t3 in
        let t4 = apply_to_record t4 in
        Ite (t1, t2, t3, t4)
    | To_array t1 ->
        let t1 = apply_to_record t1 in
        To_array t1

  in
  apply_to_record t

let definition_apply_to_record list_records d =
    match d with
    | Function (lt, t) ->
        Function (lt, apply_to_record list_records t)
    | Term t -> Term (apply_to_record list_records t)
    | Noelement -> Noelement

let create_list (projections_list: Sstr.t) (list_records: ((string * string) list) Mstr.t)
    (table: correspondence_table) =

  (* Convert list_records to take replace fields with model_trace when
     necessary. *)
  let list_records =
    Mstr.fold (fun key l acc ->
      Mstr.add key (List.map (fun (a, b) -> if b = "" then a else b) l) acc) list_records Mstr.empty
  in

  (* Convert Apply that were actually recorded as record to Record. *)
  let table =
    Mstr.fold (fun key (b, value) acc ->
      let value = definition_apply_to_record list_records value in
      Mstr.add key (b, value) acc) table Mstr.empty
  in

  (* First populate the table with all references to a cvc variable *)
  let table = get_all_var table in

  (* First recover values stored in projections that were registered *)
  let table =
    Mstr.fold (fun key value acc ->
      if Sstr.mem key projections_list then
        add_vars_to_table acc value
      else
        acc)
      table table in

  (* Then substitute all variables with their values *)
  let table =
    Mstr.fold (fun key v acc -> refine_variable_value acc key v) table table in

  (* Then converts all variables to raw_model_element *)
  Mstr.fold
    (fun key value list_acc ->
      let t = match value with
      | (_, Term t) ->
          Some t
      | (_, Function ([], t)) ->
          Some t
      | _ -> None in
      try (convert_to_model_element key t :: list_acc)
      with Not_value when not (Debug.test_flag Debug.stack_trace) -> list_acc
      | e -> raise e)
    table
    []
