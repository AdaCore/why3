(* This contains a function that helps translate counterexamples back into data
   as seen in the Ada language (see function register_apply_to_records of
   Collect_data_model). *)
open Why3
open Ident
open Model_parser

(* Some helpers for [clean_value]. *)

let opt_bind o f = match o with
  | Some x -> f x
  | None -> None

let opt_bind_any os f =
  f (Lists.map_filter (fun x -> x) os)

let opt_bind_all os f =
  if List.for_all Opt.inhabited os then
    f (List.map Opt.get os)
  else None

let only_first_field1 str =
  let rec aux = function
    | [] -> true
    | _ :: "" :: "content" :: rest | _ :: "content" :: rest
    | "split_fields" :: rest | "split_discrs" :: rest -> aux rest
    | _ -> false in
  not (String.equal str "") && aux Re.Str.(split (regexp "__") str)

(** Decide for a list of field names of a record to replace the record with the
    value of the first field. *)
let only_first_field2 = function
  | [s] -> only_first_field1 s
  | [s1; s2] ->
      (* This recognize records corresponding to unconstrained array. We only
         want the first part of the record (the array). *)
      Strings.has_prefix "elts" s1 && Strings.has_prefix "rt" s2
  | _ -> false

(** Clean value by a) replacing records according to [only_first_field2] and
   simplifying discriminant records b) removing unparsed values, in which the
   function returns [None]. *)
let rec clean_value = function
  | Unparsed _ -> None
  | String _ | Integer _ | Decimal _ | Fraction _ | Float _
  | Boolean _ | Bitvector _ as v -> Some v
  | Proj (p, v) ->
      opt_bind (clean_value v) @@ fun v ->
      Some (Proj (p, v))
  | Apply (s, vs) ->
      opt_bind_all (List.map clean_value vs) @@ fun vs ->
      Some (Apply (s, vs))
  | Array a ->
      let clean_arr_index ix =
        opt_bind (clean_value ix.arr_index_key) @@ fun key ->
        opt_bind (clean_value ix.arr_index_value) @@ fun value ->
        Some {arr_index_key= key; arr_index_value= value} in
      opt_bind (clean_value a.arr_others) @@ fun others ->
      opt_bind_any (List.map clean_arr_index a.arr_indices) @@ fun indices ->
      Some (Array {arr_others= others; arr_indices= indices})
  | Record fs ->
      if only_first_field2 (List.map fst fs) then
        clean_value (snd (List.hd fs))
      else
        let for_field (f, v) =
          let prefixes = ["us_split_fields"; "us_split_discrs";
                          "__split_discrs"; "__split_fields"] in
          if List.exists (fun s -> Strings.has_prefix s f) prefixes then
            match v with
            | Record fs ->
                let for_field (f, v) =
                  opt_bind (clean_value v) @@ fun v ->
                  Some (f, v) in
                Lists.map_filter for_field fs
            | _ ->
                Opt.get_def [] @@
                opt_bind (clean_value v) @@ fun v -> Some [f, v]
          else if Strings.has_prefix "rec__ext" f then
            []
          else
            Opt.get_def [] @@
            opt_bind (clean_value v) @@ fun v -> Some [f, v] in
        match List.concat (List.map for_field fs) with
        | [] -> None
        | fs -> Some (Record fs)

let get_field_attr attr =
  match Strings.bounded_split ':' attr.attr_string 3 with
  | ["field"; _; s] -> Some s
  | _ -> None

(* The returned [fields] are the strings S in attributes [field:N:S], which have
   to be removed from the model element name *)
let collect_attrs a (men_attrs, fields) = match get_field_attr a with
  | Some f when only_first_field1 f -> men_attrs, f :: fields
  | _ -> Sattr.add a men_attrs, fields

(* Correct a model element name by a field string *)
let correct_name f = Re.Str.global_replace (Re.Str.regexp_string f) ""

let clean_element me =
  opt_bind (clean_value me.me_value) @@ fun me_value ->
  let men_attrs, fields =
    Sattr.fold collect_attrs me.me_name.men_attrs (Sattr.empty, []) in
  let men_name = List.fold_right correct_name fields me.me_name.men_name in
  let me_name = {me.me_name with men_name; men_attrs} in
  Some {me with me_name; me_value}
