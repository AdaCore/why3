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

exception No_value

let debug_cntex = Debug.register_flag "cntex_collection"
    ~desc:"Intermediate representation debugging for counterexamples"

let map_snd f (x, y) = x, f y

(** Intermediate data structure for propagations of tree projections inside
    counterexamples.
*)

type projection_name = string

module Mpr: Extmap.S with type key = projection_name = Mstr

type tterm =
  | Tsval of model_value
  | Tapply of (string * tterm list)
  | Tarray of tarray
  | Tvar of variable
  | Tfunction_var of variable
  | Tprover_var of tvariable
  | Tite of tterm * tterm * tterm * tterm
  | Trecord of string * ((string * tterm) list)
  | Tto_array of tterm

and tarray =
  | TAvar of variable
  | TAconst of tterm
  | TAstore of tarray * tterm * tterm

and tdefinition =
  | Tfunction of (variable * string option) list * tterm
  | Tterm of tterm
  | Tnoelement

and tvariable =
  | Tree of tree
  | Tree_var of string

and tree =
  | Node of tree Mpr.t
  | Leaf of tdefinition

let rec print_array fmt = function
  | TAvar v -> Format.fprintf fmt "@[<hv2>(Array_var %s)@]" v
  | TAconst t -> Format.fprintf fmt "@[<hv2>(Aconst %a)@]" print_term t
  | TAstore (a, t1, t2) -> Format.fprintf fmt "@[<hv2>(Astore %a %a %a)@]"
                             print_array a print_term t1 print_term t2

(* Printing function for terms *)
and print_term fmt = let open Format in function
  | Tsval v -> print_model_value fmt v
  | Tapply (s, lt) ->
      fprintf fmt "@[<hv2>(Apply %s %a)@]" s
        Pp.(print_list space print_term) lt
  | Tarray a -> fprintf fmt "@[<hv>(Array %a)@]" print_array a
  | Tprover_var (Tree_var v) -> fprintf fmt "(Provervar treevar %s)" v
  | Tprover_var (Tree t) -> fprintf fmt "@[<hv2>(Provervar tree@ %a)@]" print_tree t
  | Tfunction_var v -> fprintf fmt "(Funvar %s)" v
  | Tvar v -> fprintf fmt "(Var %s)" v
  | Tite (teq1, teq2, tthen, telse) ->
      fprintf fmt "@[<hv2>(Ite@ %a@ %a@ %a@ %a)@]"
        print_term teq1 print_term teq2 print_term tthen print_term telse
  | Trecord (n, l) ->
      fprintf fmt "@[<hv2>(Record %s %a)@]" n
        Pp.(print_list semi (fun fmt (x, a) -> fprintf fmt "(%s, %a)" x print_term a)) l
  | Tto_array t -> fprintf fmt "@[<hv2>(To_array %a)@]" print_term t

and print_tree fmt =
  let open Format in function
    | Node mpr -> fprintf fmt "@[<hv2>(Node %a)@]" Pp.(print_list space (print_pair string print_tree)) (Mpr.bindings mpr)
    | Leaf td -> fprintf fmt "@[<hv2>(Leaf %a)@]" print_def td

and print_def fmt =
  let open Format in function
    | Tfunction (vars, t) ->
        fprintf fmt "@[<hv2>(Function %a@ %a)@]" Pp.(print_list space string) (List.map fst vars) print_term t
    | Tterm t -> fprintf fmt "@[<hv2>(Term %a)@]" print_term t
    | Tnoelement -> fprintf fmt "Noelement"

let subst_local_var var value t =
  let rec aux = function
    | Tfunction_var var' when var' = var ->
        value
    | Tfunction_var _ | Tvar _ | Tprover_var _ | Tsval _ as t ->
        t
    | Tapply (s, args) ->
        Tapply (s, List.map aux args)
    | Tite (t1, t2, t3, t4) ->
        Tite (aux t1, aux t2, aux t3, aux t4)
    | Tarray tarray ->
        Tarray (aux_array tarray)
    | Trecord (s, fields) ->
        let aux_field (s, t) = (s, aux t) in
        Trecord (s, List.map aux_field fields)
    | Tto_array t ->
        Tto_array (aux t)
  and aux_array = function
    | TAvar _ as a -> a
    | TAconst t ->
        TAconst (aux t)
    | TAstore (a, t1, t2) ->
        TAstore (aux_array a, aux t1, aux t2) in
  aux t

(* Printing function for debugging *)
let debug_table t =
  Debug.dprintf debug_cntex "Correspondence table key and value@.";
  Mstr.iter (fun key t ->
      Debug.dprintf debug_cntex "%s %a@." key print_tree t)
    t;
  Debug.dprintf debug_cntex "End table@."

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
  | Trees _ -> assert false (* Does not exist at this moment *)

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

(* Simplify if-then-else in value so that it can be read by
   add_vars_to_table. *)
let rec simplify_value table = function
  | Tapply (s, args') ->
      let vars, body = (* Function binding for s *)
        match Mstr.find s table with
        | Leaf (Tfunction (vars, body)) -> vars, body
        | _ -> raise Incorrect_table
        | exception Not_found -> raise Incorrect_table in
      let vars = List.map fst vars in
      let args = List.map (simplify_value table) args' in
      List.fold_right2 subst_local_var vars args body |>
      simplify_value table
  | Tite (
      Tite (Tfunction_var x,
            Tprover_var cvc,
            Tprover_var cvc1,
            _),
      Tprover_var cvc2,
      tth,
      tel) when cvc = cvc1 && cvc = cvc2 ->
      (* Here we chose what we keep from the model. This case is not complete
         but good enough. *)
      let t = Tite (Tfunction_var x, Tprover_var cvc, tth, tel) in
      simplify_value table t
  | Tite (
      Tite (Tprover_var cvc,
            Tfunction_var x,
            Tprover_var cvc1,
            _),
      Tprover_var cvc2,
      tth,
      tel) when cvc = cvc1 && cvc = cvc2 (* Same as above *) ->
      (* Here we chose what we keep from the model. This case is not complete
         but good enough. *)
      let t = Tite (Tfunction_var x, Tprover_var cvc, tth, tel) in
      simplify_value table t
  | Tite (
      Tite (Tfunction_var x,
            Tprover_var cvc,
            Tprover_var cvc1,
            Tprover_var cvc3),
      Tprover_var cvc2,
      tth,
      tel) when cvc = cvc1 && cvc <> cvc2 && cvc3 = cvc2 ->
      (* Here we chose what we keep from the model. This case is not complete
         but good enough. *)
      let t = Tite (Tfunction_var x, Tprover_var cvc3, tth, tel) in
      simplify_value table t
  | Tite (
      Tite (Tprover_var cvc,
            Tfunction_var x,
            Tprover_var cvc1,
            Tprover_var cvc3),
      Tprover_var cvc2,
      tth,
      tel) when cvc = cvc1 && cvc <> cvc2 && cvc3 = cvc2 (* Same as above *) ->
      (* Here we chose what we keep from the model. This case is not complete
         but good enough. *)
      let t = Tite (Tfunction_var x, Tprover_var cvc3, tth, tel) in
      simplify_value table t
  | Tite (eq1, eq2, tthen, telse) ->
      Tite (eq1, eq2, simplify_value table tthen, simplify_value table telse)
  | v -> v

(* Add the variables that can be deduced from ITE to the table of variables *)
let add_vars_to_table key value table  =

  let rec add_vars_to_table ~type_value table value =

    let add_var_ite cvc t1 table =
      let t1 = Leaf (Tterm t1) in
      match Mstr.find cvc table with
      | Node tree ->
          if Mpr.mem key tree then
            raise Incorrect_table
          else
            let new_tree = Node (Mpr.add key t1 tree) in
            Mstr.add cvc new_tree table
      | Leaf Tnoelement ->
          Mstr.add cvc (Node (Mpr.add key t1 Mpr.empty)) table
      | Leaf _ ->
          raise Incorrect_table
      | exception Not_found ->
          Mstr.add cvc (Node (Mpr.add key t1 Mpr.empty)) table
    in

    let value = simplify_value table value in
    match value with
    | Tite (Tprover_var (Tree_var cvc), Tfunction_var _x, t1, t2) ->
        let table = add_var_ite cvc t1 table in
        add_vars_to_table ~type_value table t2
    | Tite (Tfunction_var _x, Tprover_var (Tree_var cvc), t1, t2) ->
        let table = add_var_ite cvc t1 table in
        add_vars_to_table ~type_value table t2
    | Tite (t, Tfunction_var _x, Tprover_var (Tree_var cvc), t2) ->
        let table = add_var_ite cvc t table in
        add_vars_to_table ~type_value table t2
    | Tite (Tfunction_var _x, t, Tprover_var (Tree_var cvc), t2) ->
        let table = add_var_ite cvc t table in
        add_vars_to_table ~type_value table t2
    | Tite _ -> table
    | _ ->
      begin
        match type_value with
        | None -> table
        | Some type_value ->
            Mstr.fold (fun key_val l_elt acc ->
              let match_str_z3 = type_value ^ "!" in
              let match_str_cvc4 = "_" ^ type_value ^ "_" in
              let match_str = Re.Str.regexp ("\\(" ^ match_str_z3 ^ "\\|" ^ match_str_cvc4 ^ "\\)") in
              match Re.Str.search_forward match_str (remove_end_num key_val) 0 with
              | exception Not_found -> acc
              | _ ->
                  if l_elt = Leaf Tnoelement then
                    Mstr.add key_val (Node (Mpr.add key (Leaf (Tterm value)) Mpr.empty)) acc
                  else
                    begin match l_elt with
                      | Node mpt ->
                          (* We always prefer explicit assignment to default
                             type assignment. *)
                          if Mpr.mem key mpt then
                            acc
                          else
                            Mstr.add key_val (Node (Mpr.add key (Leaf (Tterm value)) mpt)) acc
                      | _ -> acc
                    end
              )
              table table
      end
  in

  let type_value, t = match value with
  | Tterm t -> (None, t)
  | Tfunction (cvc_var_list, t) ->
    begin
      match cvc_var_list with
      | [(_, type_value)] -> (type_value, t)
      | _ -> (None, t)
    end
  | Tnoelement -> raise Bad_variable in

  try add_vars_to_table ~type_value table t
  with Incorrect_table ->
    Debug.dprintf debug_cntex "Badly formed table@.";
    table

let rec refine_definition ~enc table = function
  | Tterm t -> Tterm (refine_function ~enc table t)
  | Tfunction (vars, t) -> Tfunction (vars, refine_function ~enc table t)
  | Tnoelement -> Tnoelement

and refine_array ~enc table = function
  | TAvar _ as a -> a
  | TAconst t ->
    let t = refine_function ~enc table t in
    TAconst t
  | TAstore (a, t1, t2) ->
    let a = refine_array ~enc table a in
    let t1 = refine_function ~enc table t1 in
    let t2 = refine_function ~enc table t2 in
    TAstore (a, t1, t2)

(* This function takes the table of assigned variables and a term and replace
   the variables with the constant associated with them in the table. If their
   value is not a constant yet, recursively apply on these variables and update
   their value. *)
and refine_function ~enc table = function
  | Tsval _ as t -> t
  | Tprover_var (Tree_var v) as t -> begin
        try (
          let tree = Mstr.find v table in
          (* Here, it is very *important* to have [enc] so that we don't go in
             circles: remember that we cannot make any assumptions on the result
             prover.
             There has been cases where projections were legitimately circularly
             defined
          *)
          if Hstr.mem enc v then
            Tprover_var (Tree tree)
          else
            let () = Hstr.add enc v () in
            let table = refine_variable_value ~enc table v tree in
            let tree = Mstr.find v table in
            Tprover_var (Tree tree)
        )
      with
      | Not_found -> t
      | No_value -> t
    end
  | Tprover_var (Tree t) ->
      let t = refine_tree ~enc table t in
      Tprover_var (Tree t)
  | Tfunction_var _ as t -> t
  | Tvar _ as t -> t
  | Tite (t1, t2, t3, t4) ->
    let t1 = refine_function ~enc table t1 in
    let t2 = refine_function ~enc table t2 in
    let t3 = refine_function ~enc table t3 in
    let t4 = refine_function ~enc table t4 in
    Tite (t1, t2, t3, t4)
  | Tarray a ->
    Tarray (refine_array ~enc table a)
  | Trecord (n, l) ->
    Trecord (n, List.map (fun (f, v) -> f, refine_function ~enc table v) l)
  | Tto_array t ->
    Tto_array (refine_function ~enc table t)
  | Tapply (s1, lt) ->
    Tapply (s1, List.map (refine_function ~enc table) lt)

and refine_tree ~enc table = function
  | Leaf t -> Leaf (refine_definition ~enc table t)
  | Node mpr -> Node (Mpr.map (fun x -> refine_tree ~enc table x) mpr)

and refine_variable_value ~enc table key (t: tree) =
  let t = refine_tree ~enc table t in
  Mstr.add key t table

(* TODO in the future, we should keep the table that is built at each call of
   this to populate the acc where its called. Because what we do here is
   inefficient. ie we calculate the value of constants several time during
   propagation without saving it: this is currently ok as counterexamples
   parsing is *not* notably taking time/memory *)
let refine_variable_value key t table =
  let encountered_key = Hstr.create 16 in
  refine_variable_value ~enc:encountered_key table key t


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
    (* TODO Does not exist yet *)
    | Trees _ -> raise No_value
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

let rec convert_to_tree_def = function
  | Noelement -> Tnoelement
  | Term t -> Tterm (convert_to_tree_term t)
  | Function (l, t) -> Tfunction (l, convert_to_tree_term t)

and convert_to_tree_term = function
  | Sval v -> Tsval v
  | Apply (s, tl) -> Tapply (s, List.map convert_to_tree_term tl)
  | Array a -> Tarray (convert_to_tree_array a)
  | Prover_var v -> Tprover_var (Tree_var v)
  | Function_var v -> Tfunction_var v
  | Var v -> Tvar v
  | Ite (t1, t2, t3, t4) ->
      let t1 = convert_to_tree_term t1 and t2 = convert_to_tree_term t2 in
      let t3 = convert_to_tree_term t3 and t4 = convert_to_tree_term t4 in
      Tite (t1, t2, t3, t4)
  | Record (s, fs) ->
      let fs = List.map (fun (s, t) -> s, convert_to_tree_term t) fs in
      Trecord (s, fs)
  | To_array t ->
      Tto_array (convert_to_tree_term t)
  | Trees _ -> raise No_value (* TODO should not appear here *)

and convert_to_tree_array = function
  | Avar v -> TAvar v
  | Aconst t -> TAconst (convert_to_tree_term t)
  | Astore (a, t1, t2) ->
      let a = convert_to_tree_array a in
      let t1 = convert_to_tree_term t1 and t2 = convert_to_tree_term t2 in
      TAstore (a, t1, t2)


(* In the following lf is the list of fields. It is used to differentiate
   projections from fields so that projections cannot be reconstructed into a
   record. *)

let rec model_value lf = function
  | Tsval (Unparsed _) -> raise No_value
  | Tsval v -> v
  | Tapply (s, ts) -> Model_parser.Apply (s, List.map (model_value lf) ts)
  | Tarray a -> Model_parser.Array (model_array lf a)
  | Tto_array t -> Model_parser.Array (model_array lf (array_of_term t))
  | Trecord (_n, l) -> Model_parser.Record (List.map (map_snd (model_value lf)) l)
  | Tprover_var (Tree t) -> model_value_of_tree lf t
  | Tprover_var (Tree_var _) -> raise No_value
  | Tfunction_var _ -> raise No_value
  | Tvar _ -> raise No_value
  | Tite _ -> raise No_value

and array_of_term = function
  (* This works for multidim array because, we call convert_to_model_value on
     the new array generated (which will still contain a To_array).
     Example of value for multidim array:
     To_array (Ite (x, 1, (To_array t), To_array t')) -> call on complete term ->
     Astore (1, To_array t, To_array t') -> call on subpart (To_array t) ->
     Astore (1, Aconst t, To_array t') -> call on subpart (To_array t') ->
     Astore (1, Aconst t, Aconst t') *)
  | Tite (Tfunction_var _, x, t1, t2)
  | Tite (x, Tfunction_var _, t1, t2) ->
      (* if v = x then t1 else t2 --> t2[x <- t1]*)
      TAstore (array_of_term t2, x, t1)
  | Tprover_var (Tree (Leaf (Tfunction (_, t)))) ->
      array_of_term t
  | t -> TAconst t

and model_array ?(arr_indices=[]) lf = function
  | TAvar _ -> raise No_value
  | TAconst t -> Model_parser.{ arr_indices; arr_others= model_value lf t }
  | TAstore (a, t1, t2) ->
      let arr_indices = Model_parser.{
          arr_index_key= model_value lf t1;
          arr_index_value= model_value lf t2;
        } :: arr_indices in
      model_array ~arr_indices lf a

and model_value_of_def lf = function
  | Tnoelement -> raise No_value
  | Tfunction (_, t) | Tterm t ->
      model_value lf t

and model_value_of_tree lf = function
  | Leaf t -> model_value_of_def lf t
  | Node mpr ->
      match Mpr.bindings mpr with
      | [] -> raise No_value
      | [f, t] ->
          Model_parser.Proj (f, model_value_of_tree lf t)
      | fs ->
          if List.for_all (fun (x, _) -> Mstr.mem x lf) fs then
            Model_parser.Record (List.map (map_snd (model_value_of_tree lf)) fs)
          else
            Model_parser.Proj (map_snd (model_value_of_tree lf) (List.hd fs))

let model_element pm (name, tree)  =
  match model_value_of_tree pm.list_fields tree with
  | value ->
      let attrs = Mstr.find_def Ident.Sattr.empty name pm.set_str in
      Some (Model_parser.create_model_element ~name ~value ~attrs)
  | exception No_value when not Debug.(test_flag debug_cntex && test_flag stack_trace) ->
      None

let create_list pm (table: definition Mstr.t) =

  (* Convert list_records to take replace fields with model_trace when necessary. *)
  let list_records =
    let select (a, b) = if b = "" then a else b in
    Mstr.mapi (fun _ -> List.map select) pm.list_records in

  (* Convert calls [r'mk v1 .. vn] to [{f1= v1; ...; fn= vn}] and unary calls
     to constructors where applicable *)
  let table =
    Mstr.mapi (fun _ -> definition_apply_to_record list_records pm.noarg_constructors)
      table in

  (* First populate the table with all references to prover variables *)
  let table =
    let var_sets = List.map collect_prover_vars (Mstr.values table) in
    let vars = List.fold_right Sstr.union var_sets Sstr.empty in
    let vars = Sstr.filter (fun v -> not (Mstr.mem v table)) vars in
    Sstr.fold (fun v -> Mstr.add v Noelement) vars table in

  (* Convert from Smtv2_model_defs.definition to Collect_data_model.tdefinition *)
  let table : tdefinition Mstr.t = Mstr.map convert_to_tree_def table in

  Debug.dprintf debug_cntex "After parsing@.";
  Mstr.iter (fun k -> Debug.dprintf debug_cntex "constant %s : %a@." k print_def) table;

  (* First recover values stored in projections that were registered *)
  let table : tree Mstr.t =
    (* Convert the table to a table of tree *)
    let table_leaves = Mstr.map (fun v -> Leaf v) table in
    let table_projs_fields = Mstr.filter (fun key _ ->
        Mstr.mem key pm.list_projections || Mstr.mem key pm.list_fields) table in
    Mstr.fold add_vars_to_table table_projs_fields table_leaves in

  (* Only printed in debug *)
  Debug.dprintf debug_cntex "Value were queried from projections@.";
  debug_table table;

  (* Then substitute all variables with their values *)
  let table = Mstr.fold refine_variable_value table table in

  Debug.dprintf debug_cntex "Var values were propagated@.";
  debug_table table;

  Lists.map_filter (model_element pm)
    (List.rev (Mstr.bindings table))
