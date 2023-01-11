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
let collect_attrs a (men_attrs, fields) = match get_field_attr a with
  | Some f when only_first_field1 f -> men_attrs, f :: fields
  | _ -> Sattr.add a men_attrs, fields

(* Correct a model element name by a field string *)
let correct_name f = Re.Str.global_replace (Re.Str.regexp_string f) ""

let clean_name men =
  let men_attrs, fields =
    Sattr.fold collect_attrs men.men_attrs (Sattr.empty, []) in
  let men_name = List.fold_right correct_name fields men.men_name in
  {men with men_name; men_attrs}

(* Filtering the model to remove elements that are not understood by gnat2why
   (sole purpose is to reduce the size of the output). *)
let in_spark (e: model_element) =
  let name = e.me_name.men_name in
  (* Names that do not begin with either '.' or a number are not recognized by
     gnat2why *)
  String.length name > 0 && (name.[0] = '.' || (name.[0] <= '9' && name.[0] >= '0'))

(* Don't clean values that will be removed by [post_clean]. TODO Can we entierly
   remove this and do all cleaning after retrieving the Model_parser.model? *)
let clean = object (self)
  inherit Model_parser.clean

  method! element me =
    (* Don't clean names here but in post_clean *)
    if me.me_name.men_kind = Error_message then
      Some me (* Keep unparsed values for error messages *)
    else
      Opt.bind (self#value me.me_value) @@ fun me_value ->
      Some {me with me_value}

  method! record fs =
    if only_first_field2 (List.map fst fs) then
      (* Clean only the first field *)
      match fs with
      | (f, v) :: fs ->
          Opt.bind (self#value v) @@ fun v ->
          Some (Record ((f, v) :: fs))
      | _ -> assert false
    else
      let for_field (f, v) =
        if is_split_field f || is_rec_ext_field f then
          Some (f, v)
        else
          Opt.bind (self#value v) @@ fun v ->
          Some (f, v) in
      match List.filter_map for_field fs with
      | [] -> None
      | fs -> Some (Record fs)
end

(** Clean values by a) replacing records according to [only_first_field2] and
   simplifying discriminant records b) removing unparsed values, in which the
   function returns [None]. *)
let post_clean = object (self)
  inherit Model_parser.clean as super

  method! element me =
    match super#element me with
    | Some me ->
        let {Model_parser.men_name= name; men_attrs= attrs} = me.me_name in
        let men_name = Ident.get_model_trace_string ~name ~attrs in
        let men_name = List.hd (Strings.bounded_split '@' men_name 2) in
        let me_name = clean_name {me.me_name with men_name} in
        let me = {me with me_name} in
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

let model_to_model (m, summary) =
  let open Check_ce in
  match summary with
  | (NC | SW | NC_SW), log ->
      Some (model_of_exec_log ~original_model:m log, summary)
  | _ -> None
