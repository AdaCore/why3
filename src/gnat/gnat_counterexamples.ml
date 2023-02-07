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

let get_field_attr attr =
  match Strings.bounded_split ':' attr.attr_string 3 with
  | ["field"; _; s] -> Some s
  | _ -> None

let is_split_field f =
  List.exists (fun s -> Strings.has_prefix s f)
    ["us_split_fields"; "us_split_discrs"; "__split_discrs"; "__split_fields"]

let is_rec_ext_field f = Strings.has_prefix "rec__ext" f

let for_field clean (f, v) =
  if is_split_field f then
    match v with
    | Record fs ->
        let for_field (f, v) =
          match clean#value v with
          | Some v -> Some (f, v)
          | None -> None in
        List.filter_map for_field fs
    | _ -> (
        match clean#value v with
        | None -> []
        | Some v -> [f, v] )
  else if is_rec_ext_field f then
    []
  else match clean#value v with
    | None -> []
    | Some v -> [f, v]

(* The returned [fields] are the strings S in attributes [field:N:S], which have
   to be removed from the model element name *)
let collect_attrs a (attrs, fields) = match get_field_attr a with
  | Some f when only_first_field1 f -> attrs, f :: fields
  | _ -> Sattr.add a attrs, fields

(* Correct a model element name by a field string *)
let correct_name f = Re.Str.global_replace (Re.Str.regexp_string f) ""

let clean_name me =
  let me_attrs, fields =
    Sattr.fold collect_attrs me.me_attrs (Sattr.empty, []) in
  let me_name = List.fold_right correct_name fields me.me_name in
  {me with me_name; me_attrs}

(* Filtering the model to remove elements that are not understood by gnat2why
   (sole purpose is to reduce the size of the output). *)
let in_spark (e: model_element) =
  let name = e.me_name in
  (* Names that do not begin with either '.' or a number are not recognized by
     gnat2why *)
  String.length name > 0 && (name.[0] = '.' || (name.[0] <= '9' && name.[0] >= '0'))

(** Clean values by
    a) replacing records according to [only_first_field2] and
    b) simplifying discriminant records. *)
let post_clean = object (self)
  inherit Model_parser.clean as super

  method! element me =
    match super#element me with
    | Some me ->
        let me_name = List.hd (Strings.bounded_split '@' me.me_name 2) in
        let me = clean_name {me with me_name} in
        if in_spark me then Some me else None
    | _ -> None

  method! record fs =
    let field_names, field_values = List.split fs in
    if only_first_field2 field_names then
      self#value (List.hd field_values)
    else match List.concat (List.map (for_field self) fs) with
      | [] -> None
      | fs -> Some (Record fs)
end
