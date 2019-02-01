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

open Wstdlib
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
  | Float_hexa of string * float


let interp_float ?(interp=true) b eb sb =
    try
      (* We don't interpret when this is disable *)
      if not interp then
        raise Exit;
      let is_neg = match b with
        | "#b0" -> false
        | "#b1" -> true
        | _ -> raise Exit
      in
      if String.length eb = 13 && String.sub eb 0 2 = "#b" &&
         String.length sb = 15 && String.sub sb 0 2 = "#x" then
         (* binary 64 *)
         let exp_base2 = String.sub eb 2 11 in
         let mant_base16 = String.sub sb 2 13 in
         let exp = int_of_string ("0b" ^ exp_base2) in
         if exp = 0 then (* subnormals *)
           let s = (if is_neg then "-" else "")^
                   "0x0."^mant_base16^"p-1023"
            in Float_hexa(s,float_of_string s)
           else if exp = 2047 then (* infinities and NaN *)
             if mant_base16="0000000000000" then
                if is_neg then Minus_infinity else Plus_infinity
                else Not_a_number
           else
           let exp = exp - 1023 in
           let s = (if is_neg then "-" else "")^
                   "0x1."^mant_base16^"p"^(string_of_int exp)
           in Float_hexa(s,float_of_string s)
      else
      if String.length eb = 4 && String.sub eb 0 2 = "#x" &&
         String.length sb = 25 && String.sub sb 0 2 = "#b" then
         (* binary 32 *)
         let exp_base16 = String.sub eb 2 2 in
         let mant_base2 = String.sub sb 2 23 in
         let mant_base16 =
           Format.asprintf "%06x" (2*int_of_string ("0b" ^ mant_base2))
         in
         let exp = int_of_string ("0x" ^ exp_base16) in
         if exp = 0 then (* subnormals *)
           let s = (if is_neg then "-" else "")^
                   "0x0."^mant_base16^"p-127"
            in Float_hexa(s,float_of_string s)
           else if exp = 255 then (* infinities and NaN *)
             if mant_base16="0000000" then
                if is_neg then Minus_infinity else Plus_infinity
                else Not_a_number
           else
           let exp = exp - 127 in
           let s = (if is_neg then "-" else "")^
                   "0x1."^mant_base16^"p"^(string_of_int exp)
           in Float_hexa(s,float_of_string s)
      else raise Exit
   with Exit -> Float_value (b, eb, sb)

type model_value =
 | Integer of string
 | Decimal of (string * string)
 | Fraction of (string * string)
 | Float of float_type
 | Boolean of bool
 | Array of model_array
 | Record of model_record
 | Proj of model_proj
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
and model_proj = (proj_name * model_value)
and proj_name = string
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
      let m = Mstr.add "cons" (Json_base.String "Plus_infinity") Mstr.empty in
      Json_base.Record m
  | Minus_infinity ->
      let m = Mstr.add "cons" (Json_base.String "Minus_infinity") Mstr.empty in
      Json_base.Record m
  | Plus_zero ->
      let m = Mstr.add "cons" (Json_base.String "Plus_zero") Mstr.empty in
      Json_base.Record m
  | Minus_zero ->
      let m = Mstr.add "cons" (Json_base.String "Minus_zero") Mstr.empty in
      Json_base.Record m
  | Not_a_number ->
      let m = Mstr.add "cons" (Json_base.String "Not_a_number") Mstr.empty in
      Json_base.Record m
  | Float_value (b, eb, sb) ->
      let m = Mstr.add "cons" (Json_base.String "Float_value") Mstr.empty in
      let m = Mstr.add "sign" (Json_base.String b) m in
      let m = Mstr.add "exponent" (Json_base.String eb) m in
      let m = Mstr.add "significand" (Json_base.String sb) m in
      Json_base.Record m
  | Float_hexa(s,f) ->
      let m = Mstr.add "cons" (Json_base.String "Float_hexa") Mstr.empty in
      let m = Mstr.add "str_hexa" (Json_base.String s) m in
      let m = Mstr.add "value" (Json_base.Float f) m in
      Json_base.Record m

let rec convert_model_value value : Json_base.json =
  match value with
  | Integer s ->
      let m = Mstr.add "type" (Json_base.String "Integer") Mstr.empty in
      let m = Mstr.add "val" (Json_base.String s) m in
      Json_base.Record m
  | Float f ->
      let m = Mstr.add "type" (Json_base.String "Float") Mstr.empty in
      let m = Mstr.add "val" (convert_float_value f) m in
      Json_base.Record m
  | Decimal (int_part, fract_part) ->
      let m = Mstr.add "type" (Json_base.String "Decimal") Mstr.empty in
      let m = Mstr.add "val" (Json_base.String (int_part^"."^fract_part)) m in
      Json_base.Record m
  | Fraction (num, den) ->
      let m = Mstr.add "type" (Json_base.String "Fraction") Mstr.empty in
      let m = Mstr.add "val" (Json_base.String (num^"/"^den)) m in
      Json_base.Record m
  | Unparsed s ->
      let m = Mstr.add "type" (Json_base.String "Unparsed") Mstr.empty in
      let m = Mstr.add "val" (Json_base.String s) m in
      Json_base.Record m
  | Bitvector v ->
      let m = Mstr.add "type" (Json_base.String "Bv") Mstr.empty in
      let m = Mstr.add "val" (Json_base.String v) m in
      Json_base.Record m
  | Boolean b ->
      let m = Mstr.add "type" (Json_base.String "Boolean") Mstr.empty in
      let m = Mstr.add "val" (Json_base.Bool b) m in
      Json_base.Record m
  | Array a ->
      let l = convert_array a in
      let m = Mstr.add "type" (Json_base.String "Array") Mstr.empty in
      let m = Mstr.add "val" (Json_base.List l) m in
      Json_base.Record m
  | Apply (s, lt) ->
      let lt = List.map convert_model_value lt in
      let slt =
        let m = Mstr.add "list" (Json_base.List lt) Mstr.empty in
        let m = Mstr.add "apply" (Json_base.String s) m in
        Json_base.Record m
      in
      let m = Mstr.add "type" (Json_base.String "Apply") Mstr.empty in
      let m = Mstr.add "val" slt m in
      Json_base.Record m
  | Record r ->
      convert_record r
  | Proj p ->
      convert_proj p

and convert_array a =
  let m_others =
    Mstr.add "others" (convert_model_value a.arr_others) Mstr.empty in
  convert_indices a.arr_indices @ [Json_base.Record m_others]

and convert_indices indices =
  match indices with
  | [] -> []
  | index :: tail ->
    let m = Mstr.add "indice" (Json_base.String index.arr_index_key) Mstr.empty in
    let m = Mstr.add "value" (convert_model_value index.arr_index_value) m in
    Json_base.Record m :: convert_indices tail

and convert_record r =
  let m = Mstr.add "type" (Json_base.String "Record") Mstr.empty in
  let fields = convert_fields r in
  let m_field = Mstr.add "Field" fields Mstr.empty in
  let m = Mstr.add "val" (Json_base.Record m_field) m in
  Json_base.Record m

and convert_proj p =
  let proj_name, value = p in
  let m = Mstr.add "type" (Json_base.String "Proj") Mstr.empty in
  let m = Mstr.add "proj_name" (Json_base.String proj_name) m in
  let m = Mstr.add "value" (convert_model_value value) m in
  Json_base.Proj m

and convert_fields fields =
  Json_base.List
    (List.map
       (fun (f, v) ->
         let m = Mstr.add "field" (Json_base.String f) Mstr.empty in
         let m = Mstr.add "value" (convert_model_value v) m in
         Json_base.Record m)
       fields)

let print_model_value_sanit fmt v =
  let v = convert_model_value v in
  Json_base.print_json fmt v

let print_model_value = print_model_value_sanit


(********************************************)
(* Print values (as to be displayed in IDE) *)
(********************************************)
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
     fprintf fmt "float_bits(%s,%s,%s)" b eb sb
  | Float_hexa(s,f) -> fprintf fmt "%s (%g)" s f

let rec print_array_human fmt (arr: model_array) =
  fprintf fmt "@[(";
  List.iter (fun e ->
    fprintf fmt "@[%s =>@ %a,@]" e.arr_index_key print_model_value_human e.arr_index_value)
    arr.arr_indices;
  fprintf fmt "@[others =>@ %a@])@]" print_model_value_human arr.arr_others

and print_record_human fmt r =
  match r with
  | [_, value] ->
      (* Special pretty printing for record with only one element *)
      fprintf fmt "%a" print_model_value_human value
  | _ ->
    fprintf fmt "@[%a@]"
      (Pp.print_list_delim ~start:Pp.lbrace ~stop:Pp.rbrace ~sep:Pp.semi
         (fun fmt (f, v) ->
            fprintf fmt "@[%s =@ %a@]" f print_model_value_human v)) r

and print_proj_human fmt p =
  let s, v = p in
  fprintf fmt "@[{%s =>@ %a}@]"
    s print_model_value_human v

and print_model_value_human fmt (v: model_value) =
  match v with
  | Integer s -> fprintf fmt "%s" s
  | Decimal (s1,s2) -> fprintf fmt "%s" (s1 ^ "." ^ s2)
  | Fraction (s1, s2) -> fprintf fmt "%s" (s1 ^ "/" ^ s2)
  | Float f -> print_float_human fmt f
  | Boolean b -> fprintf fmt "%b"  b
  | Apply (s, []) ->
      fprintf fmt "%s" s
  | Apply (s, lt) ->
    fprintf fmt "@[(%s@ %a)@]" s (Pp.print_list Pp.space print_model_value_human) lt
  | Array arr -> print_array_human fmt arr
  | Record r -> print_record_human fmt r
  | Proj p -> print_proj_human fmt p
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
  (* Attributes associated to the id of the men *)
  men_attrs : Sattr.t;
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
  | [] -> (mt_name, "")

(* Elements that are of record with only one field in the source code, are
   simplified by eval_match in wp generation. So, this allows to reconstruct
   their value (using the "field" attribute that were added). *)
let readd_one_fields ~attrs value =
  (* Small function that insert in a sorted list *)
  let rec insert_sorted (n, name) l =
    match l with
    | (n1, _) :: _ when n1 < n ->
        (n, name) :: l
    | (n1, name1) :: tl ->
        (n1, name1) :: insert_sorted (n, name) tl
    | [] -> [n, name]
  in
  (* l is the list of ordered field_names *)
  let l = Sattr.fold (fun x l ->
      match Ident.extract_field x with
      | None -> l
      | Some (n, field_name) -> insert_sorted (n, field_name) l) attrs [] in
  match Ident.get_model_trace_attr ~attrs with
  | mtrace ->
      let attrs = Sattr.remove mtrace attrs in
      (* Special cases for 'Last and 'First. TODO: Should be avoided here but
         there is no simple way.  *)
      if Strings.ends_with mtrace.attr_string "'Last" then
        let new_mtrace = Strings.remove_suffix "'Last" mtrace.attr_string in
        let new_mtrace = List.fold_left (fun acc (_, field_name) ->
            acc ^ field_name) new_mtrace l in
        let new_mtrace = new_mtrace ^ "'Last" in
        let attrs = Sattr.add (create_attribute new_mtrace) attrs in
        attrs, value
      else if Strings.ends_with mtrace.attr_string "'First" then
        let new_mtrace = Strings.remove_suffix "'First" mtrace.attr_string in
        let new_mtrace = List.fold_left (fun acc (_, field_name) ->
            acc ^ field_name) new_mtrace l in
        let new_mtrace = new_mtrace ^ "'First" in
        let attrs = Sattr.add (create_attribute new_mtrace) attrs in
        attrs, value
      else
        (* General case *)
        Sattr.add mtrace attrs,
        List.fold_left (fun v (_, field_name) ->
            Record [field_name, v]) value l
  | exception Not_found ->
      (* No model trace attribute present, same as general case *)
      attrs, List.fold_left (fun v (_, field_name) ->
          Record [field_name, v]) value l

let create_model_element ~name ~value ~attrs ?location ?term () =
  let (name, type_s) = split_model_trace_name name in
  let me_kind = match type_s with
    | "result" -> Result
    | _ -> Other
  in
  let attrs =
    match term with
    | None -> attrs
    | Some t -> Sattr.union t.t_attrs attrs
  in
  let me_name = {
    men_name = name;
    men_kind = me_kind;
    men_attrs = attrs;
  } in
  {
    me_name = me_name;
    me_value = value;
    me_location = location;
    me_term = term;
  }

let construct_name (name: string) attrs : model_element_name =
  let (name, type_s) = split_model_trace_name name in
  let me_kind = match type_s with
  | "result" -> Result
  | _ -> Other in
  {men_name = name; men_kind = me_kind; men_attrs = attrs}

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
module IntMap = Mint
module StringMap = Mstr

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
  Ident.ident Mstr.t -> Ident.ident Mstr.t -> ((string * string) list) Mstr.t ->
    string list -> Ident.Sattr.t Mstr.t -> string -> model_element list

(*
***************************************************************
**  Quering the model
***************************************************************
*)

(* Adapt name of the model to potential labels applying to it: *)
let apply_location_label ~at_loc ~attrs me_name =
  let sats =
    Sattr.filter (fun x -> Strings.has_prefix "at" x.attr_string) attrs
  in
  let _labels_added, me_name =
    Sattr.fold (fun attr_at (labels_added, me_name) ->
      match Strings.split ':' attr_at.attr_string with
      | "at" :: label :: "loc" :: loc_file :: loc_line :: [] ->
          let loc_line = int_of_string loc_line in
          if at_loc = (Filename.basename loc_file, loc_line) &&
             not (Sstr.mem label labels_added)
          then
            (Sstr.add label labels_added, me_name ^ " at " ^ label)
          else
            (labels_added, me_name)
      | _ -> (labels_added, me_name))
      sats (Sstr.empty, me_name)
  in
  me_name

let print_model_element ~at_loc ~print_attrs print_model_value me_name_trans fmt m_element =
  match m_element.me_name.men_kind with
  | Error_message ->
    fprintf fmt "%s" m_element.me_name.men_name
  | _ ->
    let me_name = me_name_trans m_element.me_name in
    let attrs = m_element.me_name.men_attrs in
    let me_name = apply_location_label ~at_loc ~attrs me_name in
    if print_attrs then
      fprintf fmt  "%s, [%a] = %a"
        me_name
        (Pp.print_list Pp.comma Pretty.print_attr)
        (Sattr.elements m_element.me_name.men_attrs)
        print_model_value m_element.me_value
    else
      fprintf fmt  "%s = %a"
        me_name
        print_model_value m_element.me_value

let print_model_elements ~at_loc ~print_attrs ?(sep = "\n")
    print_model_value me_name_trans fmt m_elements
  =
  Pp.print_list (fun fmt () -> Pp.string fmt sep)
    (print_model_element ~at_loc ~print_attrs print_model_value me_name_trans)
    fmt m_elements

let print_model_file ~print_attrs ~print_model_value fmt
    me_name_trans filename model_file
  =
  (* Relativize does not work on nighly bench: using basename instead. It
     hides the local paths.  *)
  let filename = Filename.basename filename  in
  fprintf fmt "File %s:" filename;
  IntMap.iter
    (fun line m_elements ->
      fprintf fmt "@\nLine %d:@\n" line;
      print_model_elements ~at_loc:(filename,line) ~print_attrs print_model_value me_name_trans fmt m_elements)
    model_file;
  fprintf fmt "@\n"

let why_name_trans me_name =
  match me_name.men_kind with
  | Result -> "result"
  | Old    -> "old" ^ " " ^ me_name.men_name
  | _  -> me_name.men_name

let print_model
    ~print_attrs
    ?(me_name_trans = why_name_trans)
    ~print_model_value
    fmt
    model =
  StringMap.iter (fun k e ->
      print_model_file ~print_attrs ~print_model_value fmt me_name_trans k e)
    model.model_files

let print_model_human
    ?(me_name_trans = why_name_trans)
    fmt
    model =
  print_model ~me_name_trans ~print_model_value:print_model_value_human fmt model

let print_model ?(me_name_trans = why_name_trans)
    ~print_attrs
    fmt
    model = print_model ~print_attrs ~me_name_trans ~print_model_value fmt model

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
    ~filename
    ~print_attrs
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
    let cntexmp_line =
      asprintf "%s%s%a%s"
        (get_padding line)
        start_comment
        (print_model_elements ~at_loc:(filename,line_number) ~print_attrs ~sep:"; " print_model_value_human me_name_trans) model_elements
        end_comment in

    (* We need to know how many lines will be taken by the counterexample. This
       is ad hoc as we don't really know how the lines are split in IDE. *)
    let len_cnt =
      1 + (String.length cntexmp_line) / 80
    in

    (source_code ^ line ^ cntexmp_line ^ "\n", line_number + 1, offset + len_cnt, remaining_locs, list_loc @ locs)
  with Not_found ->
    (source_code ^ line, line_number + 1, offset, remaining_locs, list_loc @ locs)


let interleave_with_source
    ~print_attrs
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
    let rel_filename = Filename.basename rel_filename in
    let model_files =
      StringMap.filter (fun k _ -> Filename.basename k = rel_filename)
        model.model_files
    in
    let model_file = snd (StringMap.choose model_files) in
    let src_lines_up_to_last_cntexmp_el source_code model_file =
      let (last_cntexmp_line, _) = IntMap.max_binding model_file in
      Str.bounded_split (Str.regexp "^") source_code (last_cntexmp_line+1)
    in
    let (source_code, _, _, _, gen_loc) =
      List.fold_left
        (interleave_line ~filename:rel_filename ~print_attrs
           start_comment end_comment me_name_trans model_file)
        ("", 1, 0, locations, [])
        (src_lines_up_to_last_cntexmp_el source_code model_file)
    in
    source_code, gen_loc
  with Not_found ->
    source_code, locations

let print_attrs_json (me: model_element_name) fmt =
  Json_base.list (fun fmt attr -> Json_base.string fmt attr.attr_string) fmt
    (Sattr.elements me.men_attrs)

(* Compute the kind of a model_element using its attributes and location *)
let compute_kind (me: model_element) =
  let me_kind = me.me_name.men_kind in
  let location = me.me_location in
  let attrs = me.me_name.men_attrs in
  let me_kind =
    (* We match on the attribute on the form [@at:'Old:loc:file:line]. If it
       exists, depending on the location of the me, we use it or not. If it
       does not we keep me_kind.
    *)
    match Sattr.choose (Sattr.filter (fun x -> Strings.has_prefix "at:'Old:" x.attr_string) attrs) with
    | exception Not_found -> me_kind
    | a ->
        begin
          match Strings.split ':' a.attr_string, location with
          | "at" :: "'Old" :: "loc" :: file :: line_number :: [], Some location ->
              let (loc_file, loc_line, _, _) =
                Loc.get location
              in
              if loc_file = file && loc_line = int_of_string line_number then
                Old
              else
                me_kind
          | _ -> me_kind
        end
  in
  me_kind

(*
**  Quering the model - json
*)
let print_model_element_json me_name_to_str fmt me =
  let print_value fmt =
    fprintf fmt "%a" print_model_value_sanit me.me_value
  in
  let print_kind fmt =
    (* We compute kinds using the attributes and locations *)
    let me_kind = compute_kind me in
    match me_kind with
    | Result -> fprintf fmt "%a" Json_base.string "result"
    | Old -> fprintf fmt "%a" Json_base.string "old"
    | Error_message -> fprintf fmt "%a" Json_base.string "error_message"
    | Other -> fprintf fmt "%a" Json_base.string "other"
  in
  let print_name fmt =
    Json_base.string fmt (me_name_to_str me)
  in
  let print_json_attrs fmt =
    print_attrs_json me.me_name fmt
  in
  let print_value_or_kind_or_name fmt printer =
    printer fmt
  in
  Json_base.map_bindings
    (fun s -> s)
    print_value_or_kind_or_name
    fmt
    [("name", print_name);
     ("attrs", print_json_attrs);
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
    let el = model_element.me_name in
    (* This removes elements that are duplicated *)
    let found_elements =
      List.find_all (fun x ->
          let xme = x.me_name in
          Ident.get_model_trace_string ~name:xme.men_name ~attrs:xme.men_attrs =
          Ident.get_model_trace_string ~name:el.men_name ~attrs:el.men_attrs &&
          (* TODO Add an efficient version of symmetric difference to extset *)
          let symm_diff =
            Sattr.diff (Sattr.union x.me_name.men_attrs el.men_attrs)
              (Sattr.inter x.me_name.men_attrs el.men_attrs) in
          Sattr.for_all (fun x ->
              not (Strings.has_prefix "at" x.attr_string)) symm_diff
        ) elements in
    let elements =
      if found_elements <> [] then
        elements
      else
        model_element::elements
    in
    let model_file = IntMap.add line_number elements model_file in
    StringMap.add filename model_file model

let recover_name list_projs term_map raw_name =
  let name, attrs =
    try let t = Mstr.find raw_name term_map in
      match t.t_node with
      | Tapp (ls, []) -> (ls.ls_name.id_string, t.t_attrs)
      | _ -> ("", t.t_attrs)
    with Not_found ->
      let id = Mstr.find raw_name list_projs in
      (id.id_string, id.id_attrs)
  in
  construct_name (get_model_trace_string ~name ~attrs) attrs

let rec replace_projection (const_function: string -> string) model_value =
  match model_value with
  | Integer _ | Decimal _ | Fraction _ | Float _ | Boolean _ | Bitvector _
    | Unparsed _ -> model_value
  | Array a ->
      Array (replace_projection_array const_function a)
  | Record r ->
      let r =
        List.map (fun (field_name, value) ->
          let field_name = try const_function field_name with
            Not_found -> field_name
          in
          (field_name, replace_projection const_function value)
          )
          r
      in
      Record r
  | Proj p ->
      let proj_name, value = p in
      let proj_name =
        try const_function proj_name
        with Not_found -> proj_name
      in
      Proj (proj_name, replace_projection const_function value)
  | Apply (s, l) ->
      let s = try const_function s
        with Not_found -> s
      in
      Apply (s, (List.map (fun v -> replace_projection const_function v) l))

and replace_projection_array const_function a =
  let {arr_others = others; arr_indices = arr_index_list} = a in
  let others = replace_projection const_function others in
  let arr_index_list =
    List.map
      (fun ind ->
         let {arr_index_key = key; arr_index_value = value} = ind in
         let value = replace_projection const_function value in
         {arr_index_key = key; arr_index_value = value}
      )
      arr_index_list
  in
  {arr_others = others; arr_indices = arr_index_list}

let internal_loc t =
  match t.t_node with
  | Tvar vs -> vs.vs_name.id_loc
  | Tapp (ls, []) -> ls.ls_name.id_loc
  | _ -> None

let default_remove_field (attrs, v: Sattr.t * model_value) = attrs, v

let remove_field_fun = ref None

let register_remove_field f =
  remove_field_fun := Some f

let build_model_rec (raw_model: model_element list) (term_map: Term.term Mstr.t)
    (list_projs: Ident.ident Mstr.t)
  =
  List.fold_left (fun model raw_element ->
    let raw_element_name = raw_element.me_name.men_name in
    try
      (
       let t = Mstr.find raw_element_name term_map in
       let attrs = Sattr.union raw_element.me_name.men_attrs t.t_attrs in
       let name, attrs =
         match t.t_node with
         | Tapp (ls, []) ->
             ls.ls_name.id_string, Sattr.union attrs ls.ls_name.id_attrs
         | _ -> "", attrs
       in
       let raw_element_value = raw_element.me_value in
       (* Replace projections with their real name *)
       let raw_element_value =
         replace_projection
           (fun x -> (recover_name list_projs term_map x).men_name)
           raw_element_value
       in
       (* Remove some specific record field related to the front-end language.
          This function is registered. *)
       let attrs, raw_element_value =
         Opt.get_def default_remove_field !remove_field_fun (attrs, raw_element_value) in
       (* Transform value flattened by eval_match (one field record) back to
          records *)
       let attrs, raw_element_value = readd_one_fields ~attrs raw_element_value in
       let model_element = {
         me_name = construct_name (get_model_trace_string ~name ~attrs) attrs;
         me_value = raw_element_value;
         me_location = t.t_loc;
         me_term = Some t;
       } in
       let model = add_to_model model model_element in
       let internal_loc = internal_loc t in
       let model =
         if (internal_loc = None) then
           model
         else
           add_to_model model {model_element with me_location = internal_loc}
       in
       (* Here we create the same element for all its possible locations (given
          by attribute vc:written).
       *)
       Sattr.fold (fun attr model ->
           let loc = Ident.extract_written_loc attr in
           if loc = None then
             model
           else
             add_to_model model {model_element with me_location = loc}
         ) attrs model
      )
    with Not_found -> model)
    StringMap.empty
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
          men_attrs = Sattr.empty;
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
  let list_projs =
    Wstdlib.Mstr.union (fun _ x _ -> Some x) printer_mapping.list_projections
      printer_mapping.list_fields in
  let model_files =
    build_model_rec raw_model printer_mapping.queried_terms list_projs in
  let model_files =
    handle_contradictory_vc model_files printer_mapping.Printer.vc_term_loc in
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
    let list_fields = printer_mapping.list_fields in
    let list_records = printer_mapping.list_records in
    let noarg_cons = printer_mapping.noarg_constructors in
    let set_str = printer_mapping.set_str in
    let raw_model = raw_mp list_proj list_fields list_records noarg_cons set_str input in
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
  (fun _ _ _ _ _ _ -> [])
