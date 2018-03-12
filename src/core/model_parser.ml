(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
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
 | Fraction of (string * string)
 | Float of float_type
 | Boolean of bool
 | Array of model_array
 | Record of model_record
 | Bitvector of string
 | Apply of string * model_value list
 | Unparsed of string
and  arr_index = {
  arr_index_key : string; (* Even array indices can exceed MAX_INT with Z3 *)
  arr_index_value : model_value;
}
and model_array = {
  arr_others  : model_value;
  arr_indices : arr_index list;
}
and model_record = (field_name * model_value) list
and field_name = string

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
      let m = Mstr.add "cons" (Json_base.String "Plus_infinity") Stdlib.Mstr.empty in
      Json_base.Record m
  | Minus_infinity ->
      let m = Mstr.add "cons" (Json_base.String "Minus_infinity") Stdlib.Mstr.empty in
      Json_base.Record m
  | Plus_zero ->
      let m = Mstr.add "cons" (Json_base.String "Plus_zero") Stdlib.Mstr.empty in
      Json_base.Record m
  | Minus_zero ->
      let m = Mstr.add "cons" (Json_base.String "Minus_zero") Stdlib.Mstr.empty in
      Json_base.Record m
  | Not_a_number ->
      let m = Mstr.add "cons" (Json_base.String "Not_a_number") Stdlib.Mstr.empty in
      Json_base.Record m
  | Float_value (b, eb, sb) ->
      let m = Mstr.add "cons" (Json_base.String "Float_value") Stdlib.Mstr.empty in
      let m = Mstr.add "sign" (Json_base.String b) m in
      let m = Mstr.add "exponent" (Json_base.String eb) m in
      let m = Mstr.add "significand" (Json_base.String sb) m in
      Json_base.Record m

let rec convert_model_value value : Json_base.json =
  match value with
  | Integer s ->
      let m = Mstr.add "type" (Json_base.String "Integer") Stdlib.Mstr.empty in
      let m = Mstr.add "val" (Json_base.String s) m in
      Json_base.Record m
  | Float f ->
      let m = Mstr.add "type" (Json_base.String "Float") Stdlib.Mstr.empty in
      let m = Mstr.add "val" (convert_float_value f) m in
      Json_base.Record m
  | Decimal (int_part, fract_part) ->
      let m = Mstr.add "type" (Json_base.String "Decimal") Stdlib.Mstr.empty in
      let m = Mstr.add "val" (Json_base.String (int_part^"."^fract_part)) m in
      Json_base.Record m
  | Fraction (num, den) ->
      let m = Mstr.add "type" (Json_base.String "Fraction") Stdlib.Mstr.empty in
      let m = Mstr.add "val" (Json_base.String (num^"/"^den)) m in
      Json_base.Record m
  | Unparsed s ->
      let m = Mstr.add "type" (Json_base.String "Unparsed") Stdlib.Mstr.empty in
      let m = Mstr.add "val" (Json_base.String s) m in
      Json_base.Record m
  | Bitvector v ->
      let m = Mstr.add "type" (Json_base.String "Bv") Stdlib.Mstr.empty in
      let m = Mstr.add "val" (Json_base.String v) m in
      Json_base.Record m
  | Boolean b ->
      let m = Mstr.add "type" (Json_base.String "Boolean") Stdlib.Mstr.empty in
      let m = Mstr.add "val" (Json_base.Bool b) m in
      Json_base.Record m
  | Array a ->
      let l = convert_array a in
      let m = Mstr.add "type" (Json_base.String "Array") Stdlib.Mstr.empty in
      let m = Mstr.add "val" (Json_base.List l) m in
      Json_base.Record m
  | Apply (s, lt) ->
      let lt = List.map convert_model_value lt in
      let slt =
        let m = Mstr.add "list" (Json_base.List lt) Stdlib.Mstr.empty in
        let m = Mstr.add "apply" (Json_base.String s) m in
        Json_base.Record m
      in
      let m = Mstr.add "type" (Json_base.String "Apply") Stdlib.Mstr.empty in
      let m = Mstr.add "val" slt m in
      Json_base.Record m
  | Record r ->
      convert_record r

and convert_array a =
  let m_others =
    Mstr.add "others" (convert_model_value a.arr_others)  Stdlib.Mstr.empty in
  convert_indices a.arr_indices @ [Json_base.Record m_others]

and convert_indices indices =
  match indices with
  | [] -> []
  | index :: tail ->
    let m = Mstr.add "indice" (Json_base.String index.arr_index_key) Stdlib.Mstr.empty in
    let m = Mstr.add "value" (convert_model_value index.arr_index_value) m in
    Json_base.Record m :: convert_indices tail

and convert_record r =
  let m = Mstr.add "type" (Json_base.String "Record") Stdlib.Mstr.empty in
  let fields = convert_fields r in
  let m_field = Mstr.add "Field" fields Stdlib.Mstr.empty in
  let m = Mstr.add "val" (Json_base.Record m_field) m in
  Json_base.Record m

and convert_fields fields =
  Json_base.List
    (List.map
       (fun (f, v) ->
         let m = Mstr.add "field" (Json_base.String f) Stdlib.Mstr.empty in
         let m = Mstr.add "value" (convert_model_value v) m in
         Json_base.Record m)
       fields)

let print_model_value_sanit fmt v =
  let v = convert_model_value v in
  Json_base.print_json fmt v

let print_model_value = print_model_value_sanit


(******************************************)
(* Print values for humans                *)
(******************************************)
let print_float_human fmt f =
  match f with
  | Plus_infinity ->
      fprintf fmt "+∞"
  | Minus_infinity ->
      fprintf fmt "-∞"
  | Plus_zero ->
      fprintf fmt "+0"
  | Minus_zero ->
      fprintf fmt "-0"
  | Not_a_number ->
      fprintf fmt "NaN"
  | Float_value (b, eb, sb) ->
      fprintf fmt "float(%s,%s,%s)" b eb sb

let rec print_array_human fmt (arr: model_array) =
  fprintf fmt "(";
  List.iter (fun e ->
    fprintf fmt "%s => %a," e.arr_index_key print_model_value_human e.arr_index_value)
    arr.arr_indices;
  fprintf fmt "others => %a)" print_model_value_human arr.arr_others

and print_record_human fmt r =
  fprintf fmt "%a"
    (Pp.print_list_delim ~start:Pp.lbrace ~stop:Pp.rbrace ~sep:Pp.semi
    (fun fmt (f, v) -> fprintf fmt "%s = %a" f print_model_value_human v)) r

and print_model_value_human fmt (v: model_value) =
  match v with
  | Integer s -> fprintf fmt "%s" s
  | Decimal (s1,s2) -> fprintf fmt "%s" (s1 ^ "." ^ s2)
  | Fraction (s1, s2) -> fprintf fmt "%s" (s1 ^ "/" ^ s2)
  | Float f -> print_float_human fmt f
  | Boolean b -> fprintf fmt "%b"  b
  | Apply (s, lt) ->
    fprintf fmt "[%s %a]" s (Pp.print_list Pp.space print_model_value_human) lt
  | Array arr -> print_array_human fmt arr
  | Record r -> print_record_human fmt r
  | Bitvector s -> fprintf fmt "%s" s
  | Unparsed s -> fprintf fmt "%s" s

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

type raw_model_parser =
  Stdlib.Sstr.t -> ((string * string) list) Stdlib.Mstr.t ->
    string -> model_element list

(*
***************************************************************
**  Quering the model
***************************************************************
*)
let print_model_element print_model_value me_name_trans fmt m_element =
  match m_element.me_name.men_kind with
  | Error_message ->
    fprintf fmt "%s" m_element.me_name.men_name
  | _ ->
    let me_name = me_name_trans m_element.me_name in
    fprintf fmt  "%s = %a"
      me_name print_model_value m_element.me_value

let print_model_elements ?(sep = "\n") print_model_value me_name_trans fmt m_elements =
  Pp.print_list (fun fmt () -> Pp.string fmt sep) (print_model_element print_model_value me_name_trans) fmt m_elements

let print_model_file ~print_model_value fmt me_name_trans filename model_file =
  (* Relativize does not work on nighly bench: using basename instead. It
     hides the local paths.  *)
  let filename = Filename.basename filename  in
  fprintf fmt "File %s:" filename;
  IntMap.iter
    (fun line m_elements ->
      fprintf fmt "@\nLine %d:@\n" line;
      print_model_elements print_model_value me_name_trans fmt m_elements)
    model_file;
  fprintf fmt "@\n"

let why_name_trans me_name =
  match me_name.men_kind with
  | Result -> "result"
  | Old    -> "old" ^ " " ^ me_name.men_name
  | _  -> me_name.men_name

let print_model
    ?(me_name_trans = why_name_trans)
    ~print_model_value
    fmt
    model =
  (* Simple and easy way to print file sorted alphabetically
   FIXME: but StringMap.iter is supposed to iter in alphabetic order, so waste of time and memory here !
   *)
  let l = StringMap.bindings model.model_files in
  List.iter (fun (k, e) -> print_model_file ~print_model_value fmt me_name_trans k e) l

let print_model_human
    ?(me_name_trans = why_name_trans)
    fmt
    model = print_model ~me_name_trans ~print_model_value:print_model_value_human fmt model


let print_model ?(me_name_trans = why_name_trans)
    fmt
    model = print_model ~me_name_trans ~print_model_value fmt model

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
      print_model_elements ~sep print_model_value me_name_trans fmt model_elements

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

(* This assumes that l is sorted and split the list of locations in two:
   those that are applied on this line and the others. For those that are on
   this line, we split the locations that appear on several lines. *)
let rec partition_loc line lc l =
  match l with
  | (hd,a) :: tl ->
      let (hdf, hdl, hdfc, hdlc) = Loc.get hd in
      if hdl = line then
        if hdlc > lc then
          let old_sloc = Loc.user_position hdf hdl hdfc lc in
          let newlc = hdlc - lc in
          let new_sloc = Loc.user_position hdf (hdl + 1) 1 newlc in
          let (rem_loc, new_loc) = partition_loc line lc tl in
          ((new_sloc,a) :: rem_loc, (old_sloc,a) :: new_loc)
        else
          let (rem_loc, new_loc) = partition_loc line lc tl in
          (rem_loc, (hd,a) :: new_loc)
      else
        (l, [])
  | _ -> (l, [])

(* Change a locations so that it points to a different line number *)
let add_offset off (loc, a) =
  let (f, l, fc, lc) = Loc.get loc in
  (Loc.user_position f (l + off) fc lc, a)

let interleave_line
    start_comment
    end_comment
    me_name_trans
    model_file
    (source_code, line_number, offset, remaining_locs, locs)
    line =
  let remaining_locs, list_loc =
    partition_loc line_number (String.length line) remaining_locs
  in
  let list_loc = List.map (add_offset offset) list_loc in
  try
    let model_elements = IntMap.find line_number model_file in
    print_model_elements print_model_value_human me_name_trans str_formatter model_elements ~sep:"; ";
    let cntexmp_line =
      (get_padding line) ^
        start_comment ^
        (flush_str_formatter ()) ^
        end_comment in

    (source_code ^ line ^ cntexmp_line ^ "\n", line_number + 1, offset + 1, remaining_locs, list_loc @ locs)
  with Not_found ->
    (source_code ^ line, line_number + 1, offset, remaining_locs, list_loc @ locs)


let interleave_with_source
    ?(start_comment="(* ")
    ?(end_comment=" *)")
    ?(me_name_trans = why_name_trans)
    model
    ~rel_filename
    ~source_code
    ~locations =
  let locations =
    List.sort (fun x y -> compare (fst x) (fst y))
      (List.filter (fun x -> let (f, _, _, _) = Loc.get (fst x) in f = rel_filename) locations)
  in
  try
    (* There is no way to compare rel_filename and the locations of filename in
       the file because they contain extra ".." which cannot be reliably removed
       (because of potential symbolic link). So, we use the basename.
    *)
    let model_files =
      StringMap.filter (fun k _ -> Filename.basename k = Filename.basename rel_filename)
        model.model_files
    in
    let model_file = snd (StringMap.choose model_files) in
    let src_lines_up_to_last_cntexmp_el source_code model_file =
      let (last_cntexmp_line, _) = IntMap.max_binding model_file in
      Str.bounded_split (Str.regexp "^") source_code (last_cntexmp_line+1)
    in
    let (source_code, _, _, _, gen_loc) =
      List.fold_left
        (interleave_line
           start_comment end_comment me_name_trans model_file)
        ("", 1, 0, locations, [])
        (src_lines_up_to_last_cntexmp_el source_code model_file)
    in
    source_code, gen_loc
  with Not_found ->
    source_code, locations


(*
**  Quering the model - json
*)
let print_model_element_json me_name_to_str fmt me =
  let print_value fmt =
    fprintf fmt "%a" print_model_value_sanit me.me_value in
  let print_kind fmt =
    match me.me_name.men_kind with
    | Result -> fprintf fmt "%a" Json_base.string "result"
    | Old -> fprintf fmt "%a" Json_base.string "old"
    | Error_message -> fprintf fmt "%a" Json_base.string "error_message"
    | Other -> fprintf fmt "%a" Json_base.string "other" in
  let print_name fmt =
    Json_base.string fmt (me_name_to_str me) in
  let print_value_or_kind_or_name fmt printer =
    printer fmt in
  Json_base.map_bindings
    (fun s -> s)
    print_value_or_kind_or_name
    fmt
    [("name", print_name);
     ("value", print_value);
     ("kind", print_kind)]

let print_model_elements_json me_name_to_str fmt model_elements =
  Json_base.list
    (print_model_element_json me_name_to_str)
    fmt
    model_elements

let print_model_elements_on_lines_json model me_name_to_str vc_line_trans fmt
    (file_name, model_file) =
  Json_base.map_bindings
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
  Json_base.map_bindings
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
    let list_proj = printer_mapping.list_projections in
    let list_records = printer_mapping.list_records in
    let raw_model = raw_mp list_proj list_records input in
    build_model raw_model printer_mapping

let register_model_parser ~desc s p =
  if Hstr.mem model_parsers s then raise (KnownModelParser s);
  Hstr.replace model_parsers s (desc, p)

let lookup_raw_model_parser s : raw_model_parser =
  try snd (Hstr.find model_parsers s)
  with Not_found -> raise (UnknownModelParser s)

let lookup_model_parser s : model_parser =
  make_mp_from_raw (lookup_raw_model_parser s)

let list_model_parsers () =
  Hstr.fold (fun k (desc,_) acc -> (k,desc)::acc) model_parsers []

let () = register_model_parser
  ~desc:"Model@ parser@ with@ no@ output@ (used@ if@ the@ solver@ does@ not@ support@ models." "no_model"
  (fun _ _ _ -> [])
