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

open Stdlib
open Smt2_model_defs
open Strings

exception Not_value

(* Adds all referenced cvc4 variables found in the term t to table *)
let rec get_variables_term (table: correspondence_table) t =
  match t with
  | Variable _ | Function_Local_Variable _ | Boolean _ | Integer _
  | Decimal _ | Float _ | Other _ | Bitvector _ -> table
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
    List.fold_left (fun table t -> get_variables_term table t) table l
  | Discr (_, l) ->
    List.fold_left (fun table t -> get_variables_term table t) table l
  | To_array t ->
    get_variables_term table t

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

(* Return true if key is s suffixed with a number *)
(* We should change the code of this function (Str still forbidden) *)
let is_prefix_num key s =
  if (String.length s >= String.length key) || String.length s = 0 then
    false
  else
    try
      let b = ref (has_prefix s key) in
      for i = String.length s to String.length key - 1 do
        b := !b && (String.get key i <= '9') && (String.get key i >= '0')
      done;
      !b
    with
    | _ -> false

(* Add all variables referenced in the model to the table *)
let add_all_cvc s table t =
  Mstr.fold (fun key _element acc ->
    if is_prefix_num key s then
      try
        if snd (Mstr.find key acc) = Noelement then
          Mstr.add key t acc
        else acc
      with Not_found -> acc
    else
      acc) table table

exception Bad_variable

(* Get the "radical" of a variable *)
let remove_end_num s =
  let n = ref (String.length s - 1) in
  while String.get s !n <= '9' && String.get s !n >= '0' && !n >= 0 do
    n := !n - 1
  done;
  try
    String.sub s 0 (!n + 1)
  with
  | _ -> s

(* Add the variables that can be deduced from ITE to the table of variables *)
let add_vars_to_table table value =
  let rec add_vars_to_table (table: correspondence_table) value =
    let t = match (snd value) with
    | Term t -> t
    | Function (_, t) -> t
    | Noelement -> raise Bad_variable in
    match t with
    | Ite (Cvc4_Variable cvc, Function_Local_Variable _x, t1, t2) ->
        begin
          let table = Mstr.add cvc (false, Term t1) table in
          add_vars_to_table table (false, Term t2)
        end
    | Ite (Function_Local_Variable _x, Cvc4_Variable cvc, t1, t2) ->
        begin
          let table = Mstr.add cvc (false, Term t1) table in
          add_vars_to_table table (false, Term t2)
        end
    | Ite (t, Function_Local_Variable _x, Cvc4_Variable cvc, t2) ->
        begin
          let table = Mstr.add cvc (false, Term t) table in
          add_vars_to_table table (false, Term t2)
        end
    | Ite (Function_Local_Variable _x, t, Cvc4_Variable cvc, t2) ->
        begin
          let table = Mstr.add cvc (false, Term t) table in
          add_vars_to_table table (false, Term t2)
        end
    | Ite (_, _, _, _) -> table
    | _ -> table
  in
  add_vars_to_table table value

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
  | Integer _ | Decimal _ | Float _ | Other _ | Bitvector _ | Boolean _ -> term
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
    Record (n, List.map (fun x -> refine_function table x) l)
  | Discr (n, l) ->
    Discr (n, List.map (fun x -> refine_function table x) l)
  | To_array t ->
    To_array (refine_function table t)


and refine_variable_value (table: correspondence_table) key v =
  let (b, t) = v in
  if b then
    table
  else
    let tv = refine_definition table t in
    Mstr.add key (true, tv) table

let convert_float (f: Smt2_model_defs.float_type) : Model_parser.float_type =
  match f with
  | Plus_infinity           -> Model_parser.Plus_infinity
  | Minus_infinity          -> Model_parser.Minus_infinity
  | Plus_zero               -> Model_parser.Plus_zero
  | Minus_zero              -> Model_parser.Minus_zero
  | Not_a_number            -> Model_parser.Not_a_number
  | Float_value (b, eb, sb) -> Model_parser.Float_value (b, eb, sb)

(* Conversion to value referenced as defined in model_parser.
   We assume that array indices fit into an integer *)
let convert_to_indice t =
  match t with
  | Integer i -> i
  | Bitvector bv -> bv
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
  | Float f -> Model_parser.Float (convert_float f)
  | Bitvector bv -> Model_parser.Bitvector bv
  | Boolean b -> Model_parser.Boolean b
  | Other _s -> raise Not_value
  | Array a -> Model_parser.Array (convert_array_value a)
  | Record (_n, l) ->
      Model_parser.Record (convert_record l)
  | Cvc4_Variable _v -> raise Not_value (*Model_parser.Unparsed "!"*)
  (* TODO change the value returned for non populated Cvc4 variable '!' -> '?' ? *)
  | To_array t -> convert_to_model_value (Array (convert_z3_array t))
  | Function_Local_Variable _ | Variable _ | Ite _ | Discr _ -> raise Not_value

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
  let acc = ref [] in
  let rec convert_aux l =
    match l with
    | Discr (_n, l) :: tl ->
        acc := List.map convert_to_model_value l;
        convert_aux tl
    | a :: tl ->
        convert_to_model_value a :: convert_aux tl
    | [] -> []
  in
  let record_field = convert_aux l in
  {
    Model_parser.discrs = !acc;
    Model_parser.fields = record_field
  }

let convert_to_model_element name t =
  match t with
  | None -> raise Not_value
  | Some t ->
      let value = convert_to_model_value t in
      Model_parser.create_model_element ~name ~value ()

(* Printing function *)
let print_table t =
  Format.eprintf "Table key and value@.";
  Mstr.iter (fun key e -> Format.eprintf "%s %a@." key print_def (snd e)) t;
  Format.eprintf "End table@."


(* Analysis function to get the value of Cvc4 variable contained in the model *)

(* Given a to_rep and its corresponding of_rep in the model gives a guessed
   value to unknown variables using constant of_rep/to_rep and "else" case of
   the ITE.*)
let corres_else_element table to_rep of_rep =
  let (_key1, (_b1, to_rep)) = to_rep in
  let (_key2, (_b2, of_rep)) = of_rep in
  let to_rep = match to_rep with
  | Term t -> t
  | Function (_, t) -> t
  | Noelement -> raise Not_value in

  let of_rep = match of_rep with
  | Term t -> t
  | Function (_, t) -> t
  | Noelement -> raise Not_value in

  let rec corres_else_element table to_rep of_rep =
    match (to_rep, of_rep) with
    | Ite (_, _, _, to_rep), _ -> corres_else_element table to_rep of_rep
    | _, Ite (_, _, _, of_rep) -> corres_else_element table to_rep of_rep
    | t, Cvc4_Variable cvc ->
        (* Make all variables not already guessed equal to the else case *)
        let s = remove_end_num cvc in
        add_all_cvc s table (false, Term t)
    | _ -> table
  in
  (* Case where to_rep, of_rep are constant values *)
  let table =
    match (to_rep, of_rep) with
    | t, Cvc4_Variable cvc ->
        Mstr.add cvc (false, Term t) table
    | _ -> table
  in
  corres_else_element table to_rep of_rep

let to_rep_of_rep (table: correspondence_table) =
  let to_reps =
    List.sort (fun x y -> String.compare (fst x) (fst y))
      (Mstr.fold (fun key value acc ->
        if has_prefix "to_rep" key then
        (key,value) :: acc else acc) table []) in

  let of_reps =
    List.sort (fun x y -> String.compare (fst x) (fst y))
      (Mstr.fold (fun key value acc -> if has_prefix "of_rep" key then
        (key,value) :: acc else acc) table []) in

  let rec to_rep_of_rep table to_reps of_reps =
    match to_reps, of_reps with
    | to_rep :: tl1, of_rep :: tl2 ->
      let table = corres_else_element table to_rep of_rep in
      to_rep_of_rep table tl1 tl2
    | [], [] -> table
    | _ -> table (* Error case *) in

  to_rep_of_rep table to_reps of_reps


let create_list (table: correspondence_table) =

  (* First populate the table with all references to a cvc variable *)
  let table = get_all_var table in

  (* First recover the values of variables that can be recovered in to/of_rep *)
  let table =
    Mstr.fold (fun key value acc ->
      if has_prefix "of_rep" key && not (String.contains key '!') then
        add_vars_to_table acc value else acc) table table in

  (* of_rep is done before to_rep because we complete from value with the
     else branch of the function *)
  let table =
    Mstr.fold (fun key value acc ->
      if has_prefix "to_rep" key && not (String.contains key '!') then
        add_vars_to_table acc value else acc) table table in

  (* Recover values from the combination of to_rep and of_rep *)
  let table = to_rep_of_rep table in

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
      with Not_value -> list_acc)
    table
    []
