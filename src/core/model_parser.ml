(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2015   --   INRIA - CNRS - Paris-Sud University  *)
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

type model_value =
 | Integer of string
 | Array of model_array
 | Unparsed of string
and  arr_index = {
  arr_index_key : int;
  arr_index_value : model_value;
}
and model_array = {
  arr_others  : model_value;
  arr_indices : arr_index list;
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
  let int_index = match index with
    | Integer s -> int_of_string s
    | _ -> raise Not_found in
  let arr_index = {
    arr_index_key = int_index;
    arr_index_value = value
  } in
  {
    arr_others = array.arr_others;
    arr_indices = arr_index::array.arr_indices;
  }

let rec print_indices sanit_print fmt indices =
  match indices with
  | [] -> ()
  | index::tail ->
    fprintf fmt "; %d -> " index.arr_index_key;
    print_model_value_sanit sanit_print fmt index.arr_index_value;
    print_indices sanit_print fmt tail
and
print_array sanit_print fmt arr =
  fprintf fmt "{others -> ";
  print_model_value_sanit sanit_print fmt arr.arr_others;
  print_indices sanit_print fmt arr.arr_indices;
  fprintf fmt "}"
and
print_model_value_sanit sanit_print fmt value =
  (* Prints model value. *)
  match value with
  | Integer s -> sanit_print fmt s
  | Unparsed s -> sanit_print fmt s
  | Array a -> print_array sanit_print fmt a

let print_model_value fmt value =
  print_model_value_sanit (fun fmt s -> fprintf fmt "%s" s) fmt value


(*
***************************************************************
**  Model elements
***************************************************************
*)
type model_element_type =
| Result
| Old
| Other

type model_element = {
  me_name     : string;
  me_type     : model_element_type;
  me_value    : model_value;
  me_location : Loc.position option;
  me_term     : Term.term option;
}

let split_me_name name =
  let splitted = Str.bounded_split (Str.regexp_string "@") name 2 in
  match splitted with
  | [first] -> (first, "")
  | first::[second] ->
    (first, second)
  | _ -> (* here, "_" can only stand for [] *)
    ("", "")

let create_model_element ~name ~value ?location ?term () =
  let (name, type_s) = split_me_name name in
  let t = match type_s with
    | "result" -> Result
    | "old" -> Old
    | _ -> Other in
  {
    me_name = name;
    me_type = t;
    me_value = value;
    me_location = location;
    me_term = term;
  }

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
module IntMap = Map.Make(struct type t  = int let compare = compare end)
module StringMap = Map.Make(String)

type model_file = model_element list IntMap.t
type model = model_file StringMap.t

let empty_model = StringMap.empty
let empty_model_file = IntMap.empty

type model_parser =  string -> Printer.printer_mapping -> model

type raw_model_parser =  string -> model_element list

(*
***************************************************************
**  Quering the model
***************************************************************
*)
let print_model_element me_name_trans fmt m_element =
  let me_name = me_name_trans (m_element.me_name, m_element.me_type) in
  fprintf fmt  "%s = %a"
      me_name print_model_value m_element.me_value

let print_model_elements ?(sep = "\n") me_name_trans fmt m_elements =
  Pp.print_list (fun fmt () -> Pp.string fmt sep) (print_model_element me_name_trans) fmt m_elements

let print_model_file fmt me_name_trans filename model_file =
  fprintf fmt "File %s:" filename;
  IntMap.iter
    (fun line m_elements ->
      fprintf fmt "\nLine %d:\n" line;
      print_model_elements me_name_trans fmt m_elements)
    model_file

let why_name_trans (me_name, me_type) =
  match me_type with
  | Result -> "result"
  | Old -> "old" ^ " " ^ me_name
  | Other -> me_name

let print_model
    ?(me_name_trans = why_name_trans)
    fmt
    model =
  StringMap.iter (print_model_file fmt me_name_trans) model

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
    let model_file = StringMap.find  filename model in
    let lines = Str.split (Str.regexp "^") source_code in
    let (source_code, _) = List.fold_left
      (interleave_line
	 start_comment end_comment me_name_trans model_file)
      ("", 1)
      lines in
    source_code
  with Not_found ->
    source_code


(*
**  Quering the model - json
*)
let print_model_value_json fmt me_value =
  fprintf fmt "%a" (print_model_value_sanit Json.string) me_value

let model_elements_to_map_bindings model_elements =
  List.fold_left
    (fun map_bindings me ->
      (me, me.me_value)::map_bindings
    )
    []
    model_elements

let print_model_elements_json me_name_to_str fmt model_elements =
  Json.map_bindings
    me_name_to_str
    print_model_value_json
    fmt
    (model_elements_to_map_bindings model_elements)

let print_model_elements_on_lines_json me_name_to_str fmt model_file =
  Json.map_bindings
    (fun i -> string_of_int i)
    (print_model_elements_json me_name_to_str)
    fmt
    (IntMap.bindings model_file)

let print_model_json
    ?(me_name_trans = why_name_trans)
    fmt
    model =
  let me_name_to_str = fun me ->
    me_name_trans (me.me_name, me.me_type) in
  Json.map_bindings
    (fun s -> s)
    (print_model_elements_on_lines_json me_name_to_str)
    fmt
    (StringMap.bindings model)

let model_to_string_json
    ?(me_name_trans = why_name_trans)
    model =
  print_model_json str_formatter ~me_name_trans model;
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

(* Estabilish mapping to why3 code *)
let rec extract_element_name labels raw_string regexp =
  match labels with
  | [] -> raw_string
  | label::labels_tail ->
    let l_string = label.lab_string in
    begin
      try
	ignore(Str.search_forward regexp l_string 0);
	let end_pos = Str.match_end () in
	String.sub l_string end_pos ((String.length l_string) - end_pos)
      with Not_found -> extract_element_name labels_tail raw_string regexp
    end

let get_element_name term raw_string  =
  let labels = Slab.elements term.t_label in
  let regexp = Str.regexp "model_trace:" in
  extract_element_name labels raw_string regexp


let rec build_model_rec raw_model terms model =
match raw_model with
  | [] -> model
  | model_element::raw_strings_tail ->
    let (element_name, element_location, element_term, terms_tail) =
      match terms with
      | [] -> (model_element.me_name, None, None, [])
      | term::t_tail ->
        ((get_element_name term model_element.me_name),
         term.t_loc,
         Some term, t_tail) in
    let new_model_element = create_model_element
      ~name:element_name
      ~value:model_element.me_value
      ?location:element_location
      ?term:element_term
      () in
    let model = add_to_model model new_model_element in
    build_model_rec
      raw_strings_tail
      terms_tail
      model


let build_model raw_model printer_mapping =
  build_model_rec raw_model printer_mapping.queried_terms empty_model


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
  let model_filtered = List.fold_left (add_loc model) empty_model positions in
  (* For each file add mapping corresponding to the first line of the
     counter-example from model to model_filtered.
     This corresponds to function declarations *)
  StringMap.fold add_first_model_line model model_filtered


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
