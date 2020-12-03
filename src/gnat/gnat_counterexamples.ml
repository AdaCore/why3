(* This contains a function that helps translate counterexamples back into data
   as seen in the Ada language (see function register_apply_to_records of
   Collect_data_model). *)
open Why3
open Ident
open Model_parser

let only_first_field1 str =
  let rec aux = function
    | [] -> true
    | _ :: "" :: "content" :: rest | _ :: "content" :: rest
    | "split_fields" :: rest | "split_discrs" :: rest -> aux rest
    | _ -> false in
  not (String.equal str "") && aux Str.(split (regexp "__") str)

(** Decide for a list of field names of a record to replace the record with the
    value of the first field. *)
let only_first_field2 = function
  | [s] -> only_first_field1 s
  | [s1; s2] ->
      (* This recognize records corresponding to unconstrained array. We only
         want the first part of the record (the array). *)
      Strings.has_prefix "elts" s1 && Strings.has_prefix "rt" s2
  | _ -> false

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
let correct_name f = Str.global_replace (Str.regexp_string f) ""

(** Clean values by a) replacing records according to [only_first_field2] and
   simplifying discriminant records b) removing unparsed values, in which the
   function returns [None]. *)
let clean = object (self)
  inherit Model_parser.clean as super

  method record fs =
    if only_first_field2 (List.map fst fs) then
      self#value (snd (List.hd fs))
    else
      let for_field (f, v) =
        let prefixes = ["us_split_fields"; "us_split_discrs";
                        "__split_discrs"; "__split_fields"] in
        if List.exists (fun s -> Strings.has_prefix s f) prefixes then
          match v with
          | Record fs ->
              let for_field (f, v) =
                Opt.bind (self#value v) @@ fun v ->
                Some (f, v) in
              Lists.map_filter for_field fs
          | _ ->
              Opt.get_def [] @@
              Opt.bind (self#value v) @@ fun v -> Some [f, v]
        else if Strings.has_prefix "rec__ext" f then
          []
        else
          Opt.get_def [] @@
          Opt.bind (self#value v) @@ fun v -> Some [f, v] in
      match List.concat (List.map for_field fs) with
      | [] -> None
      | fs -> Some (Record fs)

  method element me =
    let men_attrs, fields =
      Sattr.fold collect_attrs me.me_name.men_attrs (Sattr.empty, []) in
    let men_name = List.fold_right correct_name fields me.me_name.men_name in
    let me_name = {me.me_name with men_name; men_attrs} in
    super#element {me with me_name}
end
