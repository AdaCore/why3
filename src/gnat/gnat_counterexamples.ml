(* This contains a function that helps translate counterexamples back into data
   as seen in the Ada language (see function register_apply_to_records of
   Collect_data_model). *)
open Why3
open Wstdlib
open Smt2_model_defs

let get_only_first l =
  match l with
  | [x; y] when Strings.has_prefix "elts" x &&
                Strings.has_prefix "rt" y ->
    (* This recognize records corresponding to unconstrained array. We only
       want the first part of the record (the array). *)
      true
  | [x] when Strings.has_prefix "map__content" x ->
    (* Corresponds to map *)
      true
  | [x] when Strings.has_prefix "t__content" x ->
    (* Corresponds to bv *)
      true
  | [x] when Strings.ends_with x "__content" ->
    (* Records for int__content, bool__content, real__content or anything
       content: we are only interested in the value (not in the record). *)
      true
  | [x] when Strings.has_prefix "__split_fields" x ->
      true
  | [x] when Strings.has_prefix "__split_discrs" x ->
      true
  | _ -> false

let remove_fields_attrs attrs =
  Ident.Sattr.fold (fun attr acc ->
      match Strings.bounded_split ':' attr.Ident.attr_string 3 with
      | "field" :: _ :: s when get_only_first s ->
          acc
      | _ -> Ident.Sattr.add attr acc) attrs Ident.Sattr.empty

let rec remove_fields model_value =
  Model_parser.(match model_value with
  | Integer _ | Decimal _ | Fraction _ | Float _ | Boolean _ | Bitvector _
    | Unparsed _ -> model_value
  | Array a ->
      Array (remove_fields_array a)
  | Record l when get_only_first (List.map fst l) ->
      remove_fields (snd (List.hd l))
  | Record r ->
      let r =
        List.map (fun (field_name, value) ->
            (field_name, remove_fields value)
          )
          r
      in
      Record r
  | Proj p ->
      let proj_name, value = p in
      Proj (proj_name, remove_fields value)
  | Apply (s, l) ->
      Apply (s, (List.map (fun v -> remove_fields v) l)))

and remove_fields_array a =
  Model_parser.(
  let {arr_others = others; arr_indices = arr_index_list} = a in
  let others = remove_fields others in
  let arr_index_list =
    List.map (fun ind ->
        let {arr_index_key = key; arr_index_value = value} = ind in
        let value = remove_fields value in
        { arr_index_key = key; arr_index_value = value}
      )
      arr_index_list
  in
  {arr_others = others; arr_indices = arr_index_list}
  )

let () = Model_parser.register_remove_field
    (fun (attrs, v) -> remove_fields_attrs attrs, remove_fields v)

(* This function should remain consistant with the theories and the gnat2why
   conversion.
*)
let apply_to_record (list_records: (string list) Mstr.t)
    (noarg_constructors: string list) (t: term) =

  let rec array_apply_to_record (a: array) =
    match a with
    | Array_var _ -> a
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
    | Sval _ | Cvc4_Variable _ | Function_Local_Variable _ -> v
    (* Variable with no arguments can actually be constructors. We check this
       here and if it is the case we change the variable into a value. *)
    | Variable s when List.mem s noarg_constructors ->
        Apply (s, [])
    | Variable _ -> v
    | Array a ->
        Array (array_apply_to_record a)
    | Record (s, l) ->
        let l = List.map (fun (f,v) -> f, apply_to_record v) l in
        Record (s, l)
    | Apply (s, l) ->
        let l = List.map apply_to_record l in
        if Mstr.mem s list_records then begin
          let fields = Mstr.find s list_records in
          match fields with
          | _ when get_only_first fields ->
              List.hd l
          | _ ->
            (* For __split_fields and __split__discrs, we need to rebuild the
               whole term. Also, these can apparently appear anywhere in the
               record so we need to scan the whole record. *)
            let new_st =
                List.fold_left2 (fun acc s e ->
                  if Strings.has_prefix "us_split_fields" s ||
                     Strings.has_prefix "us_split_discrs" s ||
                     Strings.has_prefix "__split_discrs" s ||
                     Strings.has_prefix "__split_fields" s
                  then
                    (match e with
                    | Record (_, a) -> acc @ a
                    | _ -> (s,e) :: acc)
                  else
                    if Strings.has_prefix "rec__ext" s then
                      acc
                    else
                      (s, e) :: acc)
                  [] fields l
              in
              Record (s, new_st)
       end
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
    | Trees _ -> assert false

  in
  apply_to_record t

(* Actually register the conversion function *)
let () = Collect_data_model.register_apply_to_records apply_to_record
