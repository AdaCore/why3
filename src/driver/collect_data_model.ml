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

open Wstdlib
open Smt2_model_defs

exception Not_value

let debug_cntex = Debug.register_flag "cntex_collection"
    ~desc:"Intermediate representation debugging for counterexamples"

(** Intermediate data structure for propagations of tree projections inside
    counterexamples.
*)

(* Similar to definition except that we have a tree like structure for
    variables *)
type initial_definition = definition

type projection_name = string

module Mpr: Extmap.S with type key = projection_name = Mstr

type tree_variable =
  | Tree of tree
  | Var of string

and tarray =
  | TArray_var of variable
  | TConst of tterm
  | TStore of tarray * tterm * tterm

and tterm =
  | TSval of simple_value
  | TApply of (string * tterm list)
  | TArray of tarray
  | TCvc4_Variable of tree_variable
  | TFunction_Local_Variable of variable
  | TVariable of variable
  | TIte of tterm * tterm * tterm * tterm
  | TRecord of string * ((string * tterm) list)
  | TTo_array of tterm

and tree_definition =
  | TFunction of (variable * string option) list * tterm
  | TTerm of tterm
  | TNoelement

and tree =
  | Node of tree Mpr.t
  | Leaf of tree_definition

(* correpondence_table = map from var_name to tree representing its definition:
   Initially all var name begins with its original definition which is then
   refined using projections (that are saved in the tree) *)
type correspondence_table = tree Mstr.t


(** Printing functions *)
let print_float fmt f =
  match f with
  | Model_parser.Plus_infinity -> Format.fprintf fmt "Plus_infinity"
  | Model_parser.Minus_infinity -> Format.fprintf fmt "Minus_infinity"
  | Model_parser.Plus_zero -> Format.fprintf fmt "Plus_zero"
  | Model_parser.Minus_zero -> Format.fprintf fmt "Minus_zero"
  | Model_parser.Not_a_number -> Format.fprintf fmt "NaN"
  | Model_parser.Float_value (b, eb, sb) -> Format.fprintf fmt "(%s, %s, %s)" b eb sb
  | Model_parser.Float_hexa(s,f) -> Format.fprintf fmt "%s (%g)" s f

let print_value fmt v =
  match v with
  | Integer s -> Format.fprintf fmt "Integer: %s" s
  | Decimal (s1, s2) -> Format.fprintf fmt "Decimal: %s . %s" s1 s2
  | Fraction (s1, s2) -> Format.fprintf fmt "Fraction: %s / %s" s1 s2
  | Float f -> Format.fprintf fmt "Float: %a" print_float f
  | Other s -> Format.fprintf fmt "Other: %s" s
  | Bitvector bv -> Format.fprintf fmt "Bv: %s" bv
  | Boolean b -> Format.fprintf fmt "Boolean: %b " b

let rec print_array fmt a =
  match a with
  | TArray_var v -> Format.fprintf fmt "ARRAY_VAR : %s" v
  | TConst t -> Format.fprintf fmt "CONST : %a" print_term t
  | TStore (a, t1, t2) ->
      Format.fprintf fmt "STORE : %a %a %a"
        print_array a print_term t1 print_term t2

(* Printing function for terms *)
and print_term fmt t =
  match t with
  | TSval v -> print_value fmt v
  | TApply (s, lt) ->
      Format.fprintf fmt "Apply: (%s, %a)" s
        (Pp.print_list_delim ~start:Pp.lsquare ~stop:Pp.rsquare ~sep:Pp.comma print_term)
        lt
  | TArray a -> Format.fprintf fmt "Array: %a" print_array a
  | TCvc4_Variable (Var cvc) -> Format.fprintf fmt "CVC4VAR: %s" cvc
  | TCvc4_Variable _ -> Format.fprintf fmt "CVC4VAR: TREE"
  | TFunction_Local_Variable v -> Format.fprintf fmt "LOCAL: %s" v
  | TVariable v -> Format.fprintf fmt "VAR: %s" v
  | TIte _ -> Format.fprintf fmt "ITE"
  | TRecord (n, l) ->
      Format.fprintf fmt "record_type: %s; list_fields: %a" n
        (Pp.print_list Pp.semi
           (fun fmt (x, a) -> Format.fprintf fmt "(%s, %a)" x print_term a))
        l
  | TTo_array t -> Format.fprintf fmt "TO_array: %a@." print_term t

let print_def fmt d =
  match d with
  | TFunction (_vars, t) -> Format.fprintf fmt "FUNCTION : %a" print_term t
  | TTerm t -> Format.fprintf fmt "TERM : %a" print_term t
  | TNoelement -> Format.fprintf fmt "NOELEMENT"

let rec print_tree fmt t =
  match t with
  | Node mpt -> Format.fprintf fmt "NODE : [%a]" print_mpt mpt
  | Leaf td -> Format.fprintf fmt "LEAF: %a" print_def td

and print_mpt fmt t =
  Mpr.iter (fun key e -> Format.fprintf fmt "P: %s; T: %a" key print_tree e) t


(* Printing function for debugging *)
let print_table (t: correspondence_table) =
  Debug.dprintf debug_cntex "Correspondence table key and value@.";
  Mstr.iter (fun key t ->
      Debug.dprintf debug_cntex "%s %a@." key print_tree t)
    t;
  Debug.dprintf debug_cntex "End table@."

(* Adds all referenced cvc4 variables found in the term t to table.
   In particular, this function helps us to collect all the target prover's
   generated constants so that they become part of constant-to-value
   correspondence.  *)
let rec get_variables_term (table: initial_definition Mstr.t) t =
  match t with
  | Sval _ -> table
  | Variable _ | Function_Local_Variable _ -> table
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
      Mstr.add cvc Noelement table
  | Record (_, l) ->
    List.fold_left (fun table (_f, t) -> get_variables_term table t) table l
  | To_array t ->
    get_variables_term table t
  | Apply (_s, lt) ->
      List.fold_left (fun table t -> get_variables_term table t) table lt
  (* TODO does not exist at this moment *)
  | Trees _ -> raise Not_found

and get_variables_array table a =
   match a with
   | Array_var _v ->
     table
   | Const t ->
    let table = get_variables_term table t in
    table
   | Store (a, t1, t2) ->
     let table = get_variables_array table a in
     let table = get_variables_term table t1 in
     get_variables_term table t2

let get_all_var (table: definition Mstr.t) : definition Mstr.t =
  Mstr.fold (fun _key element table ->
    match element with
    | Noelement -> table
    | Function (_, t) -> get_variables_term table t
    | Term t -> get_variables_term table t) table table

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

(* Used to handle case of badly formed table *)
exception Incorrect_table

(* Add the variables that can be deduced from ITE to the table of variables *)
let add_vars_to_table (table: correspondence_table) key value : correspondence_table =

  let rec add_vars_to_table ~type_value (table: correspondence_table) value =

    let add_var_ite cvc t1 table : correspondence_table =
      let t1 = Leaf (TTerm t1) in
      match Mstr.find cvc table with
      | Node tree ->
          if Mpr.mem key tree then
            raise Incorrect_table
          else
            let new_tree = Node (Mpr.add key t1 tree) in
            Mstr.add cvc new_tree table
      | Leaf TNoelement ->
          Mstr.add cvc (Node (Mpr.add key t1 Mpr.empty)) table
      | Leaf _ ->
          raise Incorrect_table
      | exception Not_found ->
          Mstr.add cvc (Node (Mpr.add key t1 Mpr.empty)) table
    in

    match value with
    | TIte (TCvc4_Variable (Var cvc), TFunction_Local_Variable _x, t1, t2) ->
        let table = add_var_ite cvc t1 table in
        add_vars_to_table ~type_value table t2
    | TIte (TFunction_Local_Variable _x, TCvc4_Variable (Var cvc), t1, t2) ->
        let table = add_var_ite cvc t1 table in
        add_vars_to_table ~type_value table t2
    | TIte (t, TFunction_Local_Variable _x, TCvc4_Variable (Var cvc), t2) ->
        let table = add_var_ite cvc t table in
        add_vars_to_table ~type_value table t2
    | TIte (TFunction_Local_Variable _x, t, TCvc4_Variable (Var cvc), t2) ->
        let table = add_var_ite cvc t table in
        add_vars_to_table ~type_value table t2
    | TIte (_, _, _, _) -> table
    | _ ->
      begin
        match type_value with
        | None -> table
        | Some type_value ->
            Mstr.fold (fun key_val l_elt acc ->
              let match_str_z3 = type_value ^ "!" in
              let match_str_cvc4 = "_" ^ type_value ^ "_" in
              let match_str = Str.regexp ("\\(" ^ match_str_z3 ^ "\\|" ^ match_str_cvc4 ^ "\\)") in
              match Str.search_forward match_str (remove_end_num key_val) 0 with
              | exception Not_found -> acc
              | _ ->
                  if l_elt = Leaf TNoelement then
                    Mstr.add key_val (Node (Mpr.add key (Leaf (TTerm value)) Mpr.empty)) acc
                  else
                    begin match l_elt with
                      | Node mpt ->
                          (* We always prefer explicit assignment to default
                             type assignment. *)
                          if Mpr.mem key mpt then
                            acc
                          else
                            Mstr.add key_val (Node (Mpr.add key (Leaf (TTerm value)) mpt)) acc
                      | _ -> acc
                    end
              )
              table table
      end
  in

  let type_value, t = match value with
  | TTerm t -> (None, t)
  | TFunction (cvc_var_list, t) ->
    begin
      match cvc_var_list with
      | [(_, type_value)] -> (type_value, t)
      | _ -> (None, t)
    end
  | TNoelement -> raise Bad_variable in

  try add_vars_to_table ~type_value table t
  with Incorrect_table ->
    Debug.dprintf debug_cntex "Badly formed table@.";
    table

let rec refine_definition ~enc (table: correspondence_table) t =
  match t with
  | TTerm t -> TTerm (refine_function ~enc table t)
  | TFunction (vars, t) -> TFunction (vars, refine_function ~enc table t)
  | TNoelement -> TNoelement

and refine_array ~enc table a =
  match a with
  | TArray_var _v -> a
  | TConst t ->
    let t = refine_function ~enc table t in
    TConst t
  | TStore (a, t1, t2) ->
    let a = refine_array ~enc table a in
    let t1 = refine_function ~enc table t1 in
    let t2 = refine_function ~enc table t2 in
    TStore (a, t1, t2)

(* This function takes the table of assigned variables and a term and replace
   the variables with the constant associated with them in the table. If their
   value is not a constant yet, recursively apply on these variables and update
   their value. *)
and refine_function ~enc (table: correspondence_table) (term: tterm) =
  match term with
  | TSval _ -> term
  | TCvc4_Variable (Var v) ->
      begin
        try (
          let tree = Mstr.find v table in
          (* Here, it is very *important* to have [enc] so that we don't go in
             circles: remember that we cannot make any assumptions on the result
             prover.
             There has been cases where projections were legitimately circularly
             defined
          *)
          if Hstr.mem enc v then
            TCvc4_Variable (Tree tree)
          else
            let () = Hstr.add enc v () in
            let table = refine_variable_value ~enc table v tree in
            let tree = Mstr.find v table in
            TCvc4_Variable (Tree tree)
        )
      with
      | Not_found -> term
      | Not_value -> term
    end
  | TCvc4_Variable (Tree t) ->
      let t = refine_tree ~enc table t in
      TCvc4_Variable (Tree t)
  | TFunction_Local_Variable _ -> term
  | TVariable _ -> term
  | TIte (t1, t2, t3, t4) ->
    let t1 = refine_function ~enc table t1 in
    let t2 = refine_function ~enc table t2 in
    let t3 = refine_function ~enc table t3 in
    let t4 = refine_function ~enc table t4 in
    TIte (t1, t2, t3, t4)
  | TArray a ->
    TArray (refine_array ~enc table a)
  | TRecord (n, l) ->
    TRecord (n, List.map (fun (f, v) -> f, refine_function ~enc table v) l)
  | TTo_array t ->
    TTo_array (refine_function ~enc table t)
  | TApply (s1, lt) ->
    TApply (s1, List.map (refine_function ~enc table) lt)

and refine_tree ~enc table t =
  match t with
  | Leaf t -> Leaf (refine_definition ~enc table t)
  | Node mpr -> Node (Mpr.map (fun x -> refine_tree ~enc table x) mpr)

and refine_variable_value ~enc (table: correspondence_table) key (t: tree) : correspondence_table =
  let t = refine_tree ~enc table t in
  Mstr.add key t table

(* TODO in the future, we should keep the table that is built at each call of
   this to populate the acc where its called. Because what we do here is
   inefficient. ie we calculate the value of constants several time during
   propagation without saving it: this is currently ok as counterexamples
   parsing is *not* notably taking time/memory *)
let refine_variable_value table key t =
  let encountered_key = Hstr.create 16 in
  refine_variable_value ~enc:encountered_key table key t

(* Conversion to value referenced as defined in model_parser.
   We assume that array indices fit into an integer *)
let convert_to_indice t =
  match t with
  | Sval (Integer i)    -> i
  | Sval (Bitvector bv) -> bv
  | Sval (Boolean b)    -> string_of_bool b
  | _ -> raise Not_value

let convert_simple_to_model_value (v: simple_value) =
  match v with
  | Integer i -> Model_parser.Integer i
  | Decimal (d1, d2) -> Model_parser.Decimal (d1, d2)
  | Fraction (s1, s2) -> Model_parser.Fraction (s1, s2)
  | Float f -> Model_parser.Float f
  | Bitvector bv -> Model_parser.Bitvector bv
  | Boolean b -> Model_parser.Boolean b
  | Other _s -> raise Not_value

(* In the following lf is the list of fields. It is used to differentiate
   projections from fields so that projections cannot be reconstructed into a
   record. *)
let rec convert_array_value lf (a: array) : Model_parser.model_array =
  let array_indices = ref [] in

  let rec create_array_value a =
    match a with
    | Array_var _v -> raise Not_value
    | Const t -> { Model_parser.arr_indices = !array_indices;
                   Model_parser.arr_others = convert_to_model_value lf t}
    | Store (a, t1, t2) ->
        let new_index =
          { Model_parser.arr_index_key = convert_to_indice t1;
            Model_parser.arr_index_value = convert_to_model_value lf t2} in
        array_indices := new_index :: !array_indices;
        create_array_value a in
  create_array_value a

and convert_to_model_value lf (t: term): Model_parser.model_value =
  match t with
  | Sval v -> convert_simple_to_model_value v
  | Array a -> Model_parser.Array (convert_array_value lf a)
  | Record (_n, l) ->
      Model_parser.Record (convert_record lf l)
  | Trees tree ->
      begin match tree with
      | [] -> raise Not_value
      | [field, value] ->
          Model_parser.Proj (field, convert_to_model_value lf value)
      | l ->
          if List.for_all (fun x -> Mstr.mem (fst x) lf) l then
            Model_parser.Record
              (List.map (fun (field, value) ->
                   let model_value = convert_to_model_value lf value in
                   (field, model_value))
                  l)
          else
            let (proj_name, proj_value) = List.hd l in
            Model_parser.Proj (proj_name, convert_to_model_value lf proj_value)
      end
  | Cvc4_Variable _v -> raise Not_value (*Model_parser.Unparsed "!"*)
  (* TODO change the value returned for non populated Cvc4 variable '!' -> '?' ? *)
  | To_array t -> convert_to_model_value lf (Array (convert_z3_array t))
  | Apply (s, lt) -> Model_parser.Apply (s, List.map (convert_to_model_value lf) lt)
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

and convert_record lf l =
  List.map (fun (f, v) -> f, convert_to_model_value lf v) l

let convert_to_model_element ~set_str list_field name (t: term) =
  let value = convert_to_model_value list_field t in
  let attrs =
    match Mstr.find name set_str with
    | exception Not_found -> Ident.Sattr.empty
    | attrs -> attrs
  in
  Model_parser.create_model_element ~name ~value ~attrs ()

let default_apply_to_record (list_records: (string list) Mstr.t)
    (noarg_constructors: string list) (t: term) =

  let rec array_apply_to_record (a: array) =
    match a with
    | Array_var _v -> raise Not_value
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
    | Sval _ -> v
    (* Variable with no arguments can actually be constructors. We check this
       here and if it is the case we change the variable into a value. *)
    | Variable s when List.mem s noarg_constructors ->
        Apply (s, [])
    | Cvc4_Variable _ | Function_Local_Variable _ | Variable _ -> v
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
    (* TODO Does not exist yet *)
    | Trees _ -> raise Not_value
  in
  apply_to_record t

let apply_to_records_ref = ref None

let register_apply_to_records f =
  apply_to_records_ref := Some f

let apply_to_record list_records noarg_constructors t =
  match !apply_to_records_ref with
  | None -> default_apply_to_record list_records noarg_constructors t
  | Some f -> f list_records noarg_constructors t

let definition_apply_to_record list_records noarg_constructors d =
    match d with
    | Function (lt, t) ->
        Function (lt, apply_to_record list_records noarg_constructors t)
    | Term t -> Term (apply_to_record list_records noarg_constructors  t)
    | Noelement -> Noelement

let rec convert_to_tree_def (d: definition) : tree_definition =
  match d with
  | Function (l, t) ->
      TFunction (l, convert_to_tree_term t)
  | Term t -> TTerm (convert_to_tree_term t)
  | Noelement -> TNoelement

and convert_to_tree_term (t: term) : tterm =
  match t with
  | Sval v -> TSval v
  | Apply (s, tl) -> TApply(s, List.map convert_to_tree_term tl)
  | Array a -> TArray (convert_to_tree_array a)
  | Cvc4_Variable v -> TCvc4_Variable (Var v)
  | Function_Local_Variable v -> TFunction_Local_Variable v
  | Variable v -> TVariable v
  | Ite (t1, t2, t3, t4) ->
      TIte (convert_to_tree_term t1, convert_to_tree_term t2, convert_to_tree_term t3, convert_to_tree_term t4)
  | Record (s, tl) -> TRecord (s, List.map (fun (s, t) -> (s, convert_to_tree_term t)) tl)
  | To_array t -> TTo_array (convert_to_tree_term t)
  (* TODO should not appear here *)
  | Trees _ -> raise Not_value

and convert_to_tree_array a =
  match a with
  | Array_var v -> TArray_var v
  | Const t -> TConst (convert_to_tree_term t)
  | Store (a, t1, t2) ->
      TStore (convert_to_tree_array a, convert_to_tree_term t1, convert_to_tree_term t2)

let rec convert_tree_to_term (t: tree) : term =
  match t with
  | Node mpt ->
      let l = Mpr.bindings mpt in
      let l = List.map (fun (k,e) -> (k, convert_tree_to_term e)) l in
      Trees l
  | Leaf t ->
      convert_tdef_to_term t

and convert_tdef_to_term (t: tree_definition) =
  match t with
  | TFunction (_l, t) -> convert_tterm_to_term t
  | TTerm t -> convert_tterm_to_term t
  | TNoelement -> Sval (Other ("error")) (* TODO check which error can be raised here *)

and convert_tterm_to_term t =
  match t with
  | TSval v -> Sval v
  | TApply (s, tl) -> Apply (s, List.map convert_tterm_to_term tl)
  | TArray ta -> Array (convert_tarray_to_array ta)
  | TCvc4_Variable (Var v) -> Cvc4_Variable v
  | TCvc4_Variable (Tree v) -> convert_tree_to_term v
  | TFunction_Local_Variable v -> Function_Local_Variable v
  | TVariable v -> Variable v
  | TIte (t1, t2, t3, t4) ->
      let t1 = convert_tterm_to_term t1 in
      let t2 = convert_tterm_to_term t2 in
      let t3 = convert_tterm_to_term t3 in
      let t4 = convert_tterm_to_term t4 in
      Ite (t1, t2, t3, t4)
  | TRecord (s, ls) ->
      Record (s, List.map (fun (s, t) -> (s, convert_tterm_to_term t)) ls)
  | TTo_array t -> To_array (convert_tterm_to_term t)

and convert_tarray_to_array a =
  match a with
  | TArray_var v -> Array_var v
  | TConst t -> Const (convert_tterm_to_term t)
  | TStore (a, t1, t2) -> Store (convert_tarray_to_array a, convert_tterm_to_term t1, convert_tterm_to_term t2)

let create_list (projections_list: Ident.ident Mstr.t)
    (field_list: Ident.ident Mstr.t)
    (list_records: ((string * string) list) Mstr.t)
    (noarg_constructors: string list) (set_str: Ident.Sattr.t Mstr.t)
    (table: definition Mstr.t) =

  (* Convert list_records to take replace fields with model_trace when
     necessary. *)
  let list_records =
    Mstr.fold (fun key l acc ->
      Mstr.add key (List.map (fun (a, b) -> if b = "" then a else b) l) acc) list_records Mstr.empty
  in

  (* Convert Apply that were actually recorded as record to Record. Also replace
     Variable that are originally unary constructor  *)
  let table =
    Mstr.fold (fun key value acc ->
      let value =
        definition_apply_to_record list_records noarg_constructors value
      in
      Mstr.add key value acc) table Mstr.empty
  in

  (* First populate the table with all references to a cvc variable *)
  let table = get_all_var table in

  Debug.dprintf debug_cntex "After parsing@.";
  Mstr.iter (fun k e ->
      let t = convert_to_tree_def e in
      Debug.dprintf debug_cntex "constant %s : %a@."
        k print_def t)
    table;

  let table: tree_definition Mstr.t =
    Mstr.fold (fun k elt acc ->
        let elt = convert_to_tree_def elt in
        Mstr.add k elt acc) table Mstr.empty
  in

  (* Convert the table to a table of tree *)
  (* TODO this could probably be optimized away *)
  let table1 = Mstr.fold (fun key value acc ->
      Mstr.add key (Leaf value) acc) table Mstr.empty
  in

  (* First recover values stored in projections that were registered *)
  let table =
    Mstr.fold (fun key value acc ->
      if Mstr.mem key projections_list || Mstr.mem key field_list then
        add_vars_to_table acc key value
      else
        acc)
      table table1
  in

  (* Only printed in debug *)
  Debug.dprintf debug_cntex "Value were queried from projections@.";
  print_table table;

  (* Then substitute all variables with their values *)
  let table =
    Mstr.fold (fun key v acc -> refine_variable_value acc key v) table table
  in

  Debug.dprintf debug_cntex "Variable values were propagated@.";
  print_table table;

  let table: term Mstr.t =
    Mstr.fold (fun k e acc ->
        Mstr.add k (convert_tree_to_term e) acc) table Mstr.empty
  in

  (* Then converts all variables to raw_model_element *)
  Mstr.fold
    (fun key value list_acc ->
      try (convert_to_model_element ~set_str field_list key value :: list_acc)
      with Not_value when not (Debug.test_flag Debug.stack_trace) ->
        Debug.dprintf debug_cntex "Element creation failed: %s@." key; list_acc
      | e -> raise e)
    table
    []
