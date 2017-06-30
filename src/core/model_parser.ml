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
open Format
open Term
open Ident
open Printer

(*
let debug = Debug.register_info_flag "model_parser"
  ~desc:"Print@ debugging@ messages@ about@ parsing@ \
         the@ counter-example@ model."
*)

(*
***************************************************************
**  Counter-example model values
****************************************************************
*)

type float_type =
  | Plus_infinity
  | Minus_infinity
  | Plus_zero
  | Minus_zero
  | Not_a_number
  | Float_value of string * string * string

type model_value =
 | Integer of string
 | Decimal of (string * string)
 | Float of float_type
 | Boolean of bool
 | Array of model_array
 | Record of model_record
 | Bitvector of string
 | Unparsed of string
and  arr_index = {
  arr_index_key : string; (* Even array indices can exceed MAX_INT with Z3 *)
  arr_index_value : model_value;
}
and model_array = {
  arr_others  : model_value;
  arr_indices : arr_index list;
}
and model_record = {
  discrs : model_value list;
  fields : model_value list;
}

let array_create_constant ~value =
  {
    arr_others = value;
    arr_indices = [];
  }

let array_add_element ~array ~index ~value =
  (*
     Adds the element value to the array on specified index.
  *)
  let arr_index = {
    arr_index_key = index;
    arr_index_value = value
  } in
  {
    arr_others = array.arr_others;
    arr_indices = arr_index::array.arr_indices;
  }

let convert_float_value f =
  match f with
  | Plus_infinity ->
      let m = Mstr.add "cons" (Json.String "Plus_infinity") Stdlib.Mstr.empty in
      Json.Record m
  | Minus_infinity ->
      let m = Mstr.add "cons" (Json.String "Minus_infinity") Stdlib.Mstr.empty in
      Json.Record m
  | Plus_zero ->
      let m = Mstr.add "cons" (Json.String "Plus_zero") Stdlib.Mstr.empty in
      Json.Record m
  | Minus_zero ->
      let m = Mstr.add "cons" (Json.String "Minus_zero") Stdlib.Mstr.empty in
      Json.Record m
  | Not_a_number ->
      let m = Mstr.add "cons" (Json.String "Not_a_number") Stdlib.Mstr.empty in
      Json.Record m
  | Float_value (b, eb, sb) ->
      let m = Mstr.add "cons" (Json.String "Float_value") Stdlib.Mstr.empty in
      let m = Mstr.add "sign" (Json.String b) m in
      let m = Mstr.add "exponent" (Json.String eb) m in
      let m = Mstr.add "significand" (Json.String sb) m in
      Json.Record m

let rec convert_model_value value : Json.json =
  match value with
  | Integer s ->
      let m = Mstr.add "type" (Json.String "Integer") Stdlib.Mstr.empty in
      let m = Mstr.add "val" (Json.String s) m in
      Json.Record m
  | Float f ->
      let m = Mstr.add "type" (Json.String "Float") Stdlib.Mstr.empty in
      let m = Mstr.add "val" (convert_float_value f) m in
      Json.Record m
  | Decimal (int_part, fract_part) ->
      let m = Mstr.add "type" (Json.String "Decimal") Stdlib.Mstr.empty in
      let m = Mstr.add "val" (Json.String (int_part^"."^fract_part)) m in
      Json.Record m
  | Unparsed s ->
      let m = Mstr.add "type" (Json.String "Unparsed") Stdlib.Mstr.empty in
      let m = Mstr.add "val" (Json.String s) m in
      Json.Record m
  | Bitvector v ->
      let m = Mstr.add "type" (Json.String "Bv") Stdlib.Mstr.empty in
      let m = Mstr.add "val" (Json.String v) m in
      Json.Record m
  | Boolean b ->
      let m = Mstr.add "type" (Json.String "Boolean") Stdlib.Mstr.empty in
      let m = Mstr.add "val" (Json.Bool b) m in
      Json.Record m
  | Array a ->
      let l = convert_array a in
      let m = Mstr.add "type" (Json.String "Array") Stdlib.Mstr.empty in
      let m = Mstr.add "val" (Json.List l) m in
      Json.Record m
  | Record r ->
      convert_record r

and convert_array a =
  let m_others =
    Mstr.add "others" (convert_model_value a.arr_others)  Stdlib.Mstr.empty in
  convert_indices a.arr_indices @ [Json.Record m_others]

and convert_indices indices =
  match indices with
  | [] -> []
  | index :: tail ->
    let m = Mstr.add "indice" (Json.String index.arr_index_key) Stdlib.Mstr.empty in
    let m = Mstr.add "value" (convert_model_value index.arr_index_value) m in
    Json.Record m :: convert_indices tail

and convert_record r =
  let m = Mstr.add "type" (Json.String "Record") Stdlib.Mstr.empty in
  let fields = convert_fields r.fields in
  let discrs = convert_discrs r.discrs in
  let m_field_discr = Mstr.add "Field" fields Stdlib.Mstr.empty in
  let m_field_discr = Mstr.add "Discr" discrs m_field_discr in
  let m = Mstr.add "val" (Json.Record m_field_discr) m in
  Json.Record m

and convert_fields fields =
  Json.List (List.map convert_model_value fields)

and convert_discrs discrs =
  Json.List (List.map convert_model_value discrs)

let print_model_value_sanit fmt v =
  let v = convert_model_value v in
  Json.print_json fmt v

let print_model_value = print_model_value_sanit

(*
***************************************************************
**  Model elements
***************************************************************
*)

type model_element_kind =
| Result
| Old
| Error_message
| Other

type model_element_name = {
  men_name   : string;
  men_kind   : model_element_kind;
}

type model_element = {
  me_name     : model_element_name;
  me_value    : model_value;
  me_location : Loc.position option;
  me_term     : Term.term option;
}

let split_model_trace_name mt_name =
  (* Mt_name is of the form "name[@type[@*]]". Return (name, type) *)
  let splitted = Strings.bounded_split '@' mt_name 3 in
  match splitted with
  | [first] -> (first, "")
  | first::second::_ -> (first, second)
  | [] -> ("", "")

let create_model_element ~name ~value ?location ?term () =
  let (name, type_s) = split_model_trace_name name in
  let me_kind = match type_s with
    | "result" -> Result
    | "old" -> Old
    | _ -> Other in
  let me_name = {
    men_name = name;
    men_kind = me_kind;
  } in
  {
    me_name = me_name;
    me_value = value;
    me_location = location;
    me_term = term;
  }

let construct_name (name: string): model_element_name =
  let (name, type_s) = split_model_trace_name name in
  let me_kind = match type_s with
  | "result" -> Result
  | "old" -> Old
  | _ -> Other in
  {men_name = name; men_kind = me_kind}

(*
let print_location fmt m_element =
    match m_element.me_location with
    | None -> fprintf fmt "\"no location\""
    | Some loc -> Loc.report_position fmt loc
*)

(*
***************************************************************
**  Model definitions
***************************************************************
*)
module IntMap = Stdlib.Mint
module StringMap = Stdlib.Mstr

type model_file = model_element list IntMap.t
type model_files = model_file StringMap.t
type model = {
  vc_term_loc : Loc.position option;
  model_files : model_files;
}

let empty_model = StringMap.empty
let empty_model_file = IntMap.empty
let is_model_empty model =
  model.model_files = empty_model
let default_model = {
  vc_term_loc = None;
  model_files = empty_model;
}

type model_parser =  string -> Printer.printer_mapping -> model

type raw_model_parser =  string -> model_element list

(*
***************************************************************
**  Quering the model
***************************************************************
*)
let print_model_element me_name_trans fmt m_element =
  match m_element.me_name.men_kind with
  | Error_message ->
    fprintf fmt "%s" m_element.me_name.men_name
  | _ ->
    let me_name = me_name_trans m_element.me_name in
    fprintf fmt  "%s = %a"
      me_name print_model_value m_element.me_value

let print_model_elements ?(sep = "\n") me_name_trans fmt m_elements =
  Pp.print_list (fun fmt () -> Pp.string fmt sep) (print_model_element me_name_trans) fmt m_elements

let print_model_file fmt me_name_trans filename model_file =
  (* Relativize does not work on nighly bench: using basename instead. It
     hides the local paths.  *)
  let filename = Filename.basename filename  in
  fprintf fmt "File %s:" filename;
  IntMap.iter
    (fun line m_elements ->
      fprintf fmt "@\nLine %d:@\n" line;
      print_model_elements me_name_trans fmt m_elements)
    model_file;
  fprintf fmt "@\n"

let why_name_trans me_name =
  match me_name.men_kind with
  | Result -> "result"
  | Old    -> "old" ^ " " ^ me_name.men_name
  | _  -> me_name.men_name

let print_model
    ?(me_name_trans = why_name_trans)
    fmt
    model =
  (* Simple and easy way to print file sorted alphabetically
   FIXME: but StringMap.iter is supposed to iter in alphabetic order, so waste of time and memory here !
   *)
  let l = StringMap.bindings model.model_files in
  List.iter (fun (k, e) -> print_model_file fmt me_name_trans k e) l

let model_to_string
    ?(me_name_trans = why_name_trans)
    model =
  print_model ~me_name_trans str_formatter model;
  flush_str_formatter ()

let get_model_file model filename =
  try
    StringMap.find filename model
  with Not_found ->
    empty_model_file

let get_elements model_file line_number =
  try
    IntMap.find line_number model_file
  with Not_found ->
    []

let print_model_vc_term
    ?(me_name_trans = why_name_trans)
    ?(sep = "\n")
    fmt
    model =
  if not (is_model_empty model) then
    match model.vc_term_loc with
    | None -> fprintf fmt "error: cannot get location of the check"
    | Some pos ->
      let (filename, line_number, _, _) = Loc.get pos in
      let model_file = get_model_file model.model_files filename in
      let model_elements = get_elements model_file line_number in
      print_model_elements ~sep me_name_trans fmt model_elements

let model_vc_term_to_string
    ?(me_name_trans = why_name_trans)
    ?(sep = "\n")
    model =
  print_model_vc_term ~me_name_trans ~sep str_formatter model;
  flush_str_formatter ()

let get_padding line =
  try
    let r = Str.regexp " *" in
    ignore (Str.search_forward r line 0);
    Str.matched_string line
  with Not_found -> ""

let interleave_line
    start_comment
    end_comment
    me_name_trans
    model_file
    (source_code, line_number)
    line =
  try
    let model_elements = IntMap.find line_number model_file in
    print_model_elements me_name_trans str_formatter model_elements ~sep:"; ";
    let cntexmp_line =
      (get_padding line) ^
	start_comment ^
	(flush_str_formatter ()) ^
	end_comment in

    (source_code ^ line ^ cntexmp_line ^ "\n", line_number + 1)
  with Not_found ->
    (source_code ^ line, line_number + 1)


let interleave_with_source
    ?(start_comment="(* ")
    ?(end_comment=" *)")
    ?(me_name_trans = why_name_trans)
    model
    ~filename
    ~source_code =
  try
    let model_file = StringMap.find filename model.model_files in
    let src_lines_up_to_last_cntexmp_el source_code model_file =
      let (last_cntexmp_line, _) = IntMap.max_binding model_file in
      let lines = Str.bounded_split (Str.regexp "^") source_code (last_cntexmp_line+1) in
      let remove_last_element list =
	let list_rev = List.rev list in
	match list_rev with
	| _ :: tail -> List.rev tail
	| _ -> List.rev list_rev
      in
      remove_last_element lines in
    let (source_code, _) = List.fold_left
      (interleave_line
	 start_comment end_comment me_name_trans model_file)
      ("", 1)
      (src_lines_up_to_last_cntexmp_el source_code model_file) in
    source_code
  with Not_found ->
    source_code


(*
**  Quering the model - json
*)
let print_model_element_json me_name_to_str fmt me =
  let print_value fmt =
    fprintf fmt "%a" print_model_value_sanit me.me_value in
  let print_kind fmt =
    match me.me_name.men_kind with
    | Result -> fprintf fmt "%a" Json.string "result"
    | Old -> fprintf fmt "%a" Json.string "old"
    | Error_message -> fprintf fmt "%a" Json.string "error_message"
    | Other -> fprintf fmt "%a" Json.string "other" in
  let print_name fmt =
    Json.string fmt (me_name_to_str me) in
  let print_value_or_kind_or_name fmt printer =
    printer fmt in
  Json.map_bindings
    (fun s -> s)
    print_value_or_kind_or_name
    fmt
    [("name", print_name);
     ("value", print_value);
     ("kind", print_kind)]

let print_model_elements_json me_name_to_str fmt model_elements =
  Json.list
    (print_model_element_json me_name_to_str)
    fmt
    model_elements

let print_model_elements_on_lines_json model me_name_to_str vc_line_trans fmt
    (file_name, model_file) =
  Json.map_bindings
    (fun i ->
      match model.vc_term_loc with
      | None ->
	string_of_int i
      | Some pos ->
	let (vc_file_name, line, _, _) = Loc.get pos in
	if file_name = vc_file_name && i = line then
	  vc_line_trans i
	else
	  string_of_int i
    )
    (print_model_elements_json me_name_to_str)
    fmt
    (IntMap.bindings model_file)

let print_model_json
    ?(me_name_trans = why_name_trans)
    ?(vc_line_trans = (fun i -> string_of_int i))
    fmt
    model =
  let me_name_to_str = fun me ->
    me_name_trans me.me_name in
  let model_files_bindings = List.fold_left
    (fun bindings (file_name, model_file) ->
      List.append bindings [(file_name, (file_name, model_file))])
    []
    (StringMap.bindings model.model_files) in
  Json.map_bindings
    (fun s -> s)
    (print_model_elements_on_lines_json model me_name_to_str vc_line_trans)
    fmt
    model_files_bindings


let model_to_string_json
    ?(me_name_trans = why_name_trans)
    ?(vc_line_trans = (fun i -> string_of_int i))
    model =
  print_model_json str_formatter ~me_name_trans ~vc_line_trans model;
  flush_str_formatter ()


(*
***************************************************************
**  Building the model from raw model
***************************************************************
*)

let add_to_model model model_element =
  match model_element.me_location with
  | None -> model
  | Some pos ->
    let (filename, line_number, _, _) = Loc.get pos in
    let model_file = get_model_file model filename in
    let elements = get_elements model_file line_number in
    let elements = model_element::elements in
    let model_file = IntMap.add line_number elements model_file in
    StringMap.add filename model_file model

let build_model_rec (raw_model: model_element list) (term_map: Term.term Mstr.t) (model: model_files) =
  List.fold_left (fun model raw_element ->
    let raw_element_name = raw_element.me_name.men_name in
    try
      (
       let t = Mstr.find raw_element_name term_map in
       let real_model_trace = construct_name (get_model_trace_string ~labels:t.t_label) in
       let model_element = {
	 me_name = real_model_trace;
	 me_value = raw_element.me_value;
	 me_location = t.t_loc;
	 me_term = Some t;
       } in
       add_to_model model model_element
      )
    with Not_found -> model)
    model
    raw_model

let handle_contradictory_vc model_files vc_term_loc =
  (* The VC is contradictory if the location of the term that triggers VC
     was collected, model_files is not empty, and there are no model elements
     in this location.
     If this is the case, add model element saying that VC is contradictory
     to this location. *)
  if model_files = empty_model then
    (* If the counterexample model was not collected, then model_files
       is empty and this does not mean that VC is contradictory. *)
    model_files
  else
    match vc_term_loc with
    | None -> model_files
    | Some pos ->
      let (filename, line_number, _, _) = Loc.get pos in
      let model_file = get_model_file model_files filename in
      let model_elements = get_elements model_file line_number in
      if model_elements = [] then
      (* The vc is contradictory, add special model element  *)
	let me_name = {
	  men_name = "the check fails with all inputs";
	  men_kind = Error_message;
	} in
	let me = {
	  me_name = me_name;
	  me_value = Unparsed "";
	  me_location = Some pos;
	  me_term = None;
	} in
	add_to_model model_files me
      else
	model_files

let build_model raw_model printer_mapping =
  let model_files = build_model_rec raw_model printer_mapping.queried_terms empty_model in
  let model_files = handle_contradictory_vc model_files printer_mapping.Printer.vc_term_loc in
  {
    vc_term_loc = printer_mapping.Printer.vc_term_loc;
    model_files = model_files;
  }


(*
***************************************************************
**  Filtering the model
***************************************************************
*)

let add_loc orig_model new_model position =
  (* Add a given location from orig_model to new_model *)

  let (file_name, line_num, _, _) = (Loc.get position) in
  let orig_model_file = get_model_file orig_model file_name in
  let new_model_file = get_model_file new_model file_name in

  if IntMap.mem line_num new_model_file then
    (* the location already is in new_model *)
    new_model
  else
    try
      (* get the location from original model *)
      let line_map = IntMap.find line_num orig_model_file in
      (* add the location to new model *)
      let new_model_file = IntMap.add line_num line_map new_model_file in
      StringMap.add file_name new_model_file new_model
    with Not_found ->
      new_model

let add_first_model_line filename model_file model =
  let (line_num, cnt_info) = IntMap.min_binding model_file in
  let mf = get_model_file model filename in
  let mf = IntMap.add line_num cnt_info mf in
  StringMap.add filename mf model

let model_for_positions_and_decls model ~positions =
  (* Start with empty model and add locations from model that
     are in locations *)
  let model_filtered = List.fold_left (add_loc model.model_files) empty_model positions in
  (* For each file add mapping corresponding to the first line of the
     counter-example from model to model_filtered.
     This corresponds to function declarations *)
  let model_filtered = StringMap.fold add_first_model_line model.model_files model_filtered in
  { vc_term_loc = model.vc_term_loc;
    model_files = model_filtered }


(*
***************************************************************
** Registering model parser
***************************************************************
*)

exception KnownModelParser of string
exception UnknownModelParser of string

type reg_model_parser = Pp.formatted * raw_model_parser

let model_parsers : reg_model_parser Hstr.t = Hstr.create 17

let make_mp_from_raw (raw_mp:raw_model_parser) =
  fun input printer_mapping ->
    let raw_model = raw_mp input in
    build_model raw_model printer_mapping

let register_model_parser ~desc s p =
  if Hstr.mem model_parsers s then raise (KnownModelParser s);
  Hstr.replace model_parsers s (desc, p)

let lookup_raw_model_parser s =
  try snd (Hstr.find model_parsers s)
  with Not_found -> raise (UnknownModelParser s)

let lookup_model_parser s =
  make_mp_from_raw (lookup_raw_model_parser s)

let list_model_parsers () =
  Hstr.fold (fun k (desc,_) acc -> (k,desc)::acc) model_parsers []

let () = register_model_parser
  ~desc:"Model@ parser@ with@ no@ output@ (used@ if@ the@ solver@ does@ not@ support@ models." "no_model"
  (fun _ -> [])
