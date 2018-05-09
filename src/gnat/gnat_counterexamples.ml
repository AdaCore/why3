(* This contains a function that helps translate counterexamples back into data
   as seen in the Ada language (see function register_apply_to_records of
   Collect_data_model). *)
open Why3
open Stdlib
open Smt2_model_defs

(* This function should remain consistant with the theories and the gnat2why
   conversion.
*)
let apply_to_record (list_records: (string list) Mstr.t) (t: term) =

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
    | Integer _ | Decimal _ | Fraction _ | Float _ | Boolean _ | Bitvector _
    | Cvc4_Variable _ | Function_Local_Variable _ | Variable _ | Other _ -> v
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
          | [x; y] when Strings.has_prefix "elts" x &&
                        Strings.has_prefix "rt" y ->
            (* This recognize records corresponding to unconstrained array. We
               only want the first part of the record (the array). *)
            List.hd l
          | [x] when Strings.has_prefix "map__content" x ->
            (* Corresponds to map *)
              List.hd l
          | [x] when Strings.has_prefix "t__content" x ->
            (* Corresponds to bv *)
              List.hd l
          | [x] when Strings.ends_with x "__content" ->
            (* Records for int__content, bool__content, real__content or
               anything content: we are only interested in the value (not in
               the record). *)
            List.hd l
          | _ ->
            (* For __split_fields and __split__discrs, we need to rebuild the
               whole term. Also, these can apparently appear anywhere in the
               record so we need to scan the whole record. *)
            let new_st =
                List.fold_left2 (fun acc s e ->
                  if Strings.has_prefix "us_split_fields" s ||
                     Strings.has_prefix "us_split_discrs" s
                  then
                    (match e with
                    | Record (_, a) -> acc @ a
                    | _ -> (s,e) :: acc)
                  else
                    if s = "attr__constrained" then
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

  in
  apply_to_record t

(* Actually register the conversion function *)
let () = Collect_data_model.register_apply_to_records apply_to_record
