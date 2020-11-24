(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Wstdlib
open Printer
open Model_parser
open Smtv2_model_defs

let debug_cntex = Debug.register_flag "cntex_collection"
    ~desc:"Intermediate representation debugging for counterexamples"

(* Variables in the CE processing may have a direct definition or are defined by a record,
   or projection (i.e., [Node (Mstr.singleton f v)]) *)
type tree =
  | Leaf of definition
  | Node of tree Mstr.t

exception No_value

(************************************************************************)
(*                            Auxiliaries                               *)
(************************************************************************)

let map_snd f (x, y) = x, f y

let rec print_tree fmt = function
  | Leaf def -> print_definition fmt def
  | Node fs ->
      Pp.(print_list semi (print_pair_delim nothing equal nothing string print_tree))
        fmt (Mstr.bindings fs)

(* Printing function for debugging *)
let debug_table t =
  Debug.dprintf debug_cntex "Correspondence table key and value@.";
  Mstr.iter (fun key t ->
      Debug.dprintf debug_cntex "%s %a@." key print_tree t)
    t;
  Debug.dprintf debug_cntex "End table@."

(************************************************************************)
(*             Convert calls to records and constructors                *)
(************************************************************************)

let default_apply_to_record (list_records: (string list) Mstr.t)
    (noarg_constructors: string list) (t: term) =

  let rec array_apply_to_record = function
    | Avar _v -> raise No_value
    | Aconst x ->
        let x = apply_to_record x in
        Aconst x
    | Astore (a, t1, t2) ->
        let a = array_apply_to_record a in
        let t1 = apply_to_record t1 in
        let t2 = apply_to_record t2 in
        Astore (a, t1, t2)

  and apply_to_record = function
    | Sval _ as v -> v
    (* Var with no arguments can actually be constructors. We check this
       here and if it is the case we change the variable into a value. *)
    | Var s when List.mem s noarg_constructors ->
        Apply (s, [])
    | Prover_var _ | Function_var _ | Var _ as v -> v
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

let apply_to_records_ref = ref None

let register_apply_to_records f =
  apply_to_records_ref := Some f

let apply_to_record list_records noarg_constructors t =
  match !apply_to_records_ref with
  | None -> default_apply_to_record list_records noarg_constructors t
  | Some f -> f list_records noarg_constructors t

let definition_apply_to_record list_records noarg_constructors = function
    | Function (lt, t) ->
        Function (lt, apply_to_record list_records noarg_constructors t)
    | Term t -> Term (apply_to_record list_records noarg_constructors  t)
    | Noelement -> Noelement

(************************************************************************)
(*                       Collect prover variables                       *)
(************************************************************************)

let rec collect_prover_vars_term = function
  | Prover_var v -> Sstr.singleton v
  | Sval _ | Var _ | Function_var _ -> Sstr.empty
  | Array a -> collect_prover_vars_array a
  | Ite (t1, t2, t3, t4) ->
      let ss = List.map collect_prover_vars_term [t1; t2; t3; t4] in
      List.fold_right Sstr.union ss Sstr.empty
  | Record (_, fs) ->
      let ss = List.map collect_prover_vars_term (List.map snd fs) in
      List.fold_right Sstr.union ss Sstr.empty
  | To_array t -> collect_prover_vars_term t
  | Apply (_, ts) ->
      let ss = List.map collect_prover_vars_term ts in
      List.fold_right Sstr.union ss Sstr.empty

and collect_prover_vars_array = function
  | Avar _ -> Sstr.empty
  | Aconst t -> collect_prover_vars_term t
  | Astore (a, t1, t2) ->
      List.fold_left Sstr.union (collect_prover_vars_array a)
        (List.map collect_prover_vars_term [t1; t2])

let collect_prover_vars = function
  | Noelement -> Sstr.empty
  | Function (_, t) | Term t ->
      collect_prover_vars_term t

(************************************************************************)
(*                            Simplify ITEs                             *)
(************************************************************************)

(* Used to handle case of badly formed table *)
exception Incorrect_table

let subst_function_var var value =
  let rec aux = function
    | Function_var var' when var' = var -> value
    | Function_var _ | Var _ | Prover_var _ | Sval _ as t -> t
    | Apply (s, args) -> Apply (s, List.map aux args)
    | Ite (t1, t2, t3, t4) -> Ite (aux t1, aux t2, aux t3, aux t4)
    | Array tarray -> Array (aux_array tarray)
    | Record (s, fields) -> Record (s, List.map (map_snd aux) fields)
    | To_array t -> To_array (aux t)
  and aux_array = function
    | Avar _ as a -> a
    | Aconst t ->
        Aconst (aux t)
    | Astore (a, t1, t2) ->
        Astore (aux_array a, aux t1, aux t2) in
  aux

(* Simplify if-then-else in value so that it can be read by
   add_vars_to_model. *)
let rec simplify_value table = function
  | Apply (s, args') ->
      let vars, body = (* Function binding for s *)
        match Mstr.find s table with
        | Leaf (Function (vars, body)) -> vars, body
        | _ -> raise Incorrect_table
        | exception Not_found -> raise Incorrect_table in
      let vars = List.map fst vars in
      let args = List.map (simplify_value table) args' in
      simplify_value table
        (List.fold_right2 subst_function_var vars args body)
  | Ite (Ite (Function_var x, Prover_var v, Prover_var v', _),
          Prover_var v'', tth, tel)
  | Ite (Ite (Prover_var v, Function_var x, Prover_var v', _),
          Prover_var v'', tth, tel)
    when v = v' && v' = v'' ->
      (* ite (ite x = v then v else _) = v then tth else tel *)
      (* Here we chose what we keep from the model. This case is not complete
         but good enough. *)
      simplify_value table
        (Ite (Function_var x, Prover_var v, tth, tel))
  | Ite (Ite (Function_var x, Prover_var v1, Prover_var v1', Prover_var v2),
          Prover_var v2', tth, tel)
  | Ite (Ite (Prover_var v1, Function_var x, Prover_var v1', Prover_var v2),
          Prover_var v2', tth, tel)
    when v1 = v1' && v1 <> v2 && v2 = v2' ->
      (* ite (ite x = v1 then v1 else v2) = v2 then tth else tel *)
      (* Here we chose what we keep from the model. This case is not complete
         but good enough. *)
      simplify_value table
        (Ite (Function_var x, Prover_var v2, tth, tel))
  | Ite (eq1, eq2, tthen, telse) ->
      Ite (eq1, eq2, simplify_value table tthen, simplify_value table telse)
  | v -> v

(************************************************************************)
(*                   Add variables from ITE to table                    *)
(************************************************************************)

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

let is_prover_var value_type name =
  let open Re.Str in
  let match_str_z3 = value_type^"!" in
  let match_str_cvc4 = "_"^value_type^"_" in
  let re = regexp ("\\("^quote match_str_z3^"\\|"^quote match_str_cvc4^"\\)") in
  try ignore (search_forward re (remove_end_num name) 0); true
  with Not_found -> false

exception Bad_variable

(* Add the variables that can be deduced from ITE to the table of variables.

   Keys are projections or fields. *)

(** Add a mapping from [key] to [value] in tree node [tr] (or create the node) *)
let set_field key value tr =
  let fs = match tr with
    | None | Some (Leaf Noelement) ->
        Mstr.singleton key value
    | Some (Node fs) ->
        Mstr.add_new Incorrect_table key value fs
    | Some (Leaf _) -> raise Incorrect_table in
  Some (Node fs)

let rec set_fields_projs key value value_type table =
  match simplify_value table value with
  | Ite (Function_var _, Prover_var v, t1, t2)
  | Ite (Prover_var v, Function_var _, t1, t2) ->
      let table = Mstr.change (set_field key (Leaf (Term t1))) v table in
      set_fields_projs key t2 value_type table
  | Ite (Function_var _, t, Prover_var v, t2)
  | Ite (t, Function_var _, Prover_var v, t2) ->
      let table = Mstr.change (set_field key (Leaf (Term t))) v table in
      set_fields_projs key t2 value_type table
  | Ite _ -> table
  | value -> (
      match value_type with
      | None -> table
      | Some value_type ->
          let aux name tr =
            if not (is_prover_var value_type name) then
              tr
            else match tr with
              | Leaf Noelement ->
                  Node (Mstr.singleton key (Leaf (Term value)))
              | Node fs ->
                  (* We always prefer explicit assignment to default
                     type assignment. *)
                  let fs = if Mstr.mem key fs then fs
                    else Mstr.add key (Leaf (Term value)) fs in
                  Node fs
              | _ -> tr in
          Mstr.mapi aux table )

let set_fields_projs key value table =
  let value, value_type = match value with
    | Function ([_, value_type], t) -> t, value_type
    | Function (_, t) | Term t  -> t, None
    | Noelement -> raise Bad_variable in
  try set_fields_projs key value value_type table
  with Incorrect_table ->
    Debug.dprintf debug_cntex "Badly formed table@.";
    table

(************************************************************************)
(*                       Refine prover variables                        *)
(************************************************************************)

(* This function takes the table of assigned variables and a term and replace
   the variables with the constant associated with them in the table. If their
   value is not a constant yet, recursively apply on these variables and update
   their value. *)
let rec bind_prover_vars_term table t pv_table = match t with
  | Sval _ | Function_var _ | Var _ -> pv_table
  | Prover_var v -> (
      try
        let tr = Mstr.find v table in
        (* Here, it is very *important* to have [enc] so that we don't go in
           circles: remember that we cannot make any assumptions on the result
           prover.
           There has been cases where projections were legitimately circularly
           defined *)
        if Mstr.mem v pv_table then pv_table else
          Mstr.add v tr pv_table |>
          bind_prover_vars_tree table tr
      with Not_found | No_value -> pv_table )
  | Ite (t1, t2, t3, t4) ->
      pv_table |>
      bind_prover_vars_term table t1 |>
      bind_prover_vars_term table t2 |>
      bind_prover_vars_term table t3 |>
      bind_prover_vars_term table t4
  | Array a ->
      bind_prover_vars_array table a pv_table
  | Record (_, fs) ->
      List.fold_left (fun pv_table (_, t) -> bind_prover_vars_term table t pv_table) pv_table fs
  | To_array t ->
      bind_prover_vars_term table t pv_table
  | Apply (_, ts) ->
      List.fold_left (fun pv_table t -> bind_prover_vars_term table t pv_table) pv_table ts

and bind_prover_vars_array table a pv_table = match a with
  | Avar _ -> pv_table
  | Aconst t ->
      bind_prover_vars_term table t pv_table
  | Astore (a, t1, t2) ->
      pv_table |>
      bind_prover_vars_array table a |>
      bind_prover_vars_term table t1 |>
      bind_prover_vars_term table t2

and bind_prover_vars_definition table def pv_table = match def with
  | Term t -> bind_prover_vars_term table t pv_table
  | Function (_, t) -> bind_prover_vars_term table t pv_table
  | Noelement -> pv_table

and bind_prover_vars_tree table tr pv_table = match tr with
  | Leaf t -> bind_prover_vars_definition table t pv_table
  | Node fs -> Mstr.fold (fun _ tr pv_table -> bind_prover_vars_tree table tr pv_table) fs pv_table

(************************************************************************)
(*                       Creation of model values                       *)
(************************************************************************)

(* In the following lf is the list of fields. It is used to differentiate
   projections from fields so that projections cannot be reconstructed into a
   record. *)

let rec model_value lf pv_table = function
  | Sval (Unparsed _) -> raise No_value
  | Sval v -> v
  | Apply (s, ts) -> Model_parser.Apply (s, List.map (model_value lf pv_table) ts)
  | Array a -> Model_parser.Array (model_array lf pv_table a)
  | To_array t -> Model_parser.Array (model_array lf pv_table (array_of_term pv_table t))
  | Record (_n, l) -> Model_parser.Record (List.map (map_snd (model_value lf pv_table)) l)
  | Prover_var v -> model_value_of_tree lf pv_table (Mstr.find_exn No_value v pv_table)
  | Function_var _ -> raise No_value
  | Var _ -> raise No_value
  | Ite _ -> raise No_value

and array_of_term pv_table = function
  (* This works for multidim array because, we call convert_to_model_value on
     the new array generated (which will still contain a To_array).
     Example of value for multidim array:
     To_array (Ite (x, 1, (To_array t), To_array t')) -> call on complete term ->
     Astore (1, To_array t, To_array t') -> call on subpart (To_array t) ->
     Astore (1, Aconst t, To_array t') -> call on subpart (To_array t') ->
     Astore (1, Aconst t, Aconst t') *)
  | Ite (Function_var _, x, t1, t2)
  | Ite (x, Function_var _, t1, t2) ->
      (* if v = x then t1 else t2 --> t2[x <- t1]*)
      Astore (array_of_term pv_table t2, x, t1)
  | Prover_var v as t -> (
      match Mstr.find v pv_table with
      | Leaf (Function (_, t)) ->
          array_of_term pv_table t
      | _ -> Aconst t )
  | t -> Aconst t

and model_array ?(arr_indices=[]) lf pv_table = function
  | Avar _ -> raise No_value
  | Aconst t -> Model_parser.{ arr_indices; arr_others= model_value lf pv_table t }
  | Astore (a, t1, t2) ->
      let arr_indices = Model_parser.{
          arr_index_key= model_value lf pv_table t1;
          arr_index_value= model_value lf pv_table t2;
        } :: arr_indices in
      model_array ~arr_indices lf pv_table a

and model_value_of_def lf pv_table = function
  | Noelement -> raise No_value
  | Function (_, t) | Term t ->
      model_value lf pv_table t

and model_value_of_tree lf pv_table = function
  | Leaf t -> model_value_of_def lf pv_table t
  | Node fs -> match Mstr.bindings fs with
      | [] -> raise No_value
      | [f, t] ->
          Model_parser.Proj (f, model_value_of_tree lf pv_table t)
      | fs ->
          if List.for_all (fun (x, _) -> Mstr.mem x lf) fs then
            Model_parser.Record (List.map (map_snd (model_value_of_tree lf pv_table)) fs)
          else
            Model_parser.Proj (map_snd (model_value_of_tree lf pv_table) (List.hd fs))

let model_element pm pv_table (name, tr)  =
  match model_value_of_tree pm.list_fields pv_table tr with
  | value ->
      let attrs = Mstr.find_def Ident.Sattr.empty name pm.set_str in
      Some (Model_parser.create_model_element ~name ~value ~attrs)
  | exception No_value when not Debug.(test_flag debug_cntex && test_flag stack_trace) ->
      None

(************************************************************************)
(*            Import Smtv2_model_defs to model elements                 *)
(************************************************************************)

let create_list pm (table: definition Mstr.t) =

  (* Convert list_records to take replace fields with model_trace when necessary. *)
  let list_records =
    let select (a, b) = if b = "" then a else b in
    Mstr.mapi (fun _ -> List.map select) pm.list_records in

  (* Convert calls [r'mk v1 .. vn] to [{f1= v1; ...; fn= vn}] and unary calls
     to constructors where applicable *)
  let table =
    Mstr.map (definition_apply_to_record list_records pm.noarg_constructors)
      table in

  (* Bind all prover variables to no-element *)
  let table =
    let var_sets = List.map collect_prover_vars (Mstr.values table) in
    let vars = List.fold_right Sstr.union var_sets Sstr.empty in
    let vars = Sstr.filter (fun v -> not (Mstr.mem v table)) vars in
    Sstr.fold (fun v -> Mstr.add v Noelement) vars table in

  Debug.dprintf debug_cntex "After parsing@.";
  Mstr.iter (fun k -> Debug.dprintf debug_cntex "constant %s : %a@." k print_definition) table;

  (* Recover values stored in projections that were registered *)
  let table : tree Mstr.t =
    let table_fields_projs = Mstr.filter (fun key _ -> Mstr.mem key (list_projs pm)) table in
    let table = Mstr.map (fun v -> Leaf v) table in
    Mstr.fold set_fields_projs table_fields_projs table in

  Debug.dprintf debug_cntex "Value were queried from projections@.";
  debug_table table;

  (* Bind prover variables to their values *)
  let pv_table = Mstr.fold (fun _ -> bind_prover_vars_tree table) table Mstr.empty in

  Debug.dprintf debug_cntex "Var values were propagated@.";
  debug_table table;

  Lists.map_filter (model_element pm pv_table)
    (List.rev (Mstr.bindings table))
