(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
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

type model_int = { int_value: BigInt.t; int_verbatim: string }
type model_dec = { dec_int: BigInt.t; dec_frac: BigInt.t; dec_verbatim: string }
type model_frac = { frac_nom: BigInt.t; frac_den: BigInt.t; frac_verbatim: string }
type model_bv = { bv_value: BigInt.t; bv_length: int; bv_verbatim: string }
type model_float_binary = { sign: model_bv; exp: model_bv; mant: model_bv }
type model_float =
  | Plus_infinity | Minus_infinity | Plus_zero | Minus_zero | Not_a_number
  | Float_number of {hex: string option; binary: model_float_binary}

type model_value =
  | Boolean of bool
  | String of string
  | Integer of model_int
  | Float of model_float
  | Bitvector of model_bv
  | Decimal of model_dec
  | Fraction of model_frac
  | Array of model_array
  | Record of model_record
  | Proj of model_proj
  | Apply of string * model_value list
  | Undefined
  | Unparsed of string

and arr_index = {arr_index_key: model_value; arr_index_value: model_value}

and model_array = {arr_others: model_value; arr_indices: arr_index list}

and model_record = (field_name * model_value) list

and model_proj = proj_name * model_value

and proj_name = string

and field_name = string

let array_create_constant ~value = {arr_others= value; arr_indices= []}

let array_add_element ~array ~index ~value =
  (*
     Adds the element value to the array on specified index.
  *)
  let arr_index = {arr_index_key= index; arr_index_value= value} in
  {arr_others= array.arr_others; arr_indices= arr_index :: array.arr_indices}

let pad_with_zeros width s =
  let filled =
    let len = width - String.length s in
    if len <= 0 then "" else String.make len '0' in
  filled ^ s

(* (-) integer . fractional e (-) exponent *)
(* ?%d+.%d*E-?%d+ *)
(* 0X-?%x+.%x*P-?%d+ *)

let float_of_binary binary =
  try
    let open BigInt in
    let {sign; mant; exp} = binary in
    let exp_bias = pred (pow_int_pos 2 (exp.bv_length - 1)) in
    let exp_max = pred (pow_int_pos 2 exp.bv_length) in
    let frac_len = (* Length of the hexadecimal representation (after the ".") *)
      if mant.bv_length mod 4 = 0
      then mant.bv_length / 4
      else (mant.bv_length / 4) + 1 in
    let is_neg = match to_int sign.bv_value with 0 -> false | 1 -> true | _ -> raise Exit in
    (* Compute exponent (int) and frac (string of hexa) *)
    let frac =
      (* The hex value is used after the decimal point. So we need to adjust
         it to the number of binary elements there are.
         Example in 32bits: significand is 23 bits, and the hexadecimal
         representation will have a multiple of 4 bits (ie 24). So, we need to
         multiply by two to account the difference. *)
      if Strings.has_prefix "#b" mant.bv_verbatim then
        let adjust = 4 - (mant.bv_length mod 4) in
        if adjust = 4 then
          mant.bv_value (* No adjustment needed *)
        else
          mul (pow_int_pos 2 adjust) mant.bv_value
      else
        mant.bv_value in
    let frac = pad_with_zeros frac_len (Format.sprintf "%x" (to_int frac)) in
    if eq exp.bv_value zero then (* subnormals and zero *)
      (* Case for zero *)
      if eq mant.bv_value zero then
        if is_neg then Minus_zero else Plus_zero
      else
        (* Subnormals *)
        let hex = Format.asprintf "%t0x0.%sp-%s"
            (fun fmt -> if is_neg then Pp.string fmt "-")
            frac (to_string exp_bias) in
        Float_number {hex= Some hex; binary}
    else if eq exp.bv_value exp_max (* infinities and NaN *) then
      if eq mant.bv_value zero then
        if is_neg then Minus_infinity else Plus_infinity
      else Not_a_number
    else
      let exp = sub exp.bv_value exp_bias in
      let hex = Format.asprintf "%t0x1.%sp%s"
          (fun fmt -> if is_neg then Pp.string fmt "-")
          frac (to_string exp) in
      Float_number {hex= Some hex; binary}
  with Exit ->
    Float_number {hex= None; binary}

let binary_of_bigint d =
  let open BigInt in
  if lt d zero then invalid_arg "bin_of_int";
  if eq d zero then "0" else
    let rec loop acc d =
      if eq d zero then acc else
        let d, m = computer_div_mod d (of_int 2) in
        loop (BigInt.to_string m :: acc) d in
    String.concat "" (loop [] d)

let binary_of_bv bv =
  let b = binary_of_bigint bv.bv_value in
  let p = String.make (bv.bv_length-String.length b) '0' in
  Printf.sprintf "#b%s%s" p b

let debug_force_binary_floats = Debug.register_flag "model_force_binary_floats"
    ~desc:"Print all floats using bitvectors in JSON output for models"

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
  | Float_number {binary= {sign; exp; mant}} when Debug.test_flag debug_force_binary_floats ->
      let m = Mstr.add "cons" (Json_base.String "Float_value") Mstr.empty in
      let m = Mstr.add "sign" (Json_base.String (binary_of_bv sign)) m in
      let m = Mstr.add "exponent" (Json_base.String (binary_of_bv exp)) m in
      let m = Mstr.add "significand" (Json_base.String (binary_of_bv mant)) m in
      Json_base.Record m
  | Float_number {hex= Some hex} ->
      let m = Mstr.add "cons" (Json_base.String "Float_hexa") Mstr.empty in
      let m = Mstr.add "str_hexa" (Json_base.String hex) m in
      let m = Mstr.add "value" (Json_base.Float (float_of_string hex)) m in
      Json_base.Record m
  | Float_number {binary= {sign; exp; mant}} ->
      let m = Mstr.add "cons" (Json_base.String "Float_value") Mstr.empty in
      let m = Mstr.add "sign" (Json_base.String sign.bv_verbatim) m in
      let m = Mstr.add "exponent" (Json_base.String exp.bv_verbatim) m in
      let m = Mstr.add "significand" (Json_base.String mant.bv_verbatim) m in
      Json_base.Record m

let rec convert_model_value value : Json_base.json =
  match value with
  | String s ->
      let m = Mstr.add "type" (Json_base.String "String") Mstr.empty in
      let m = Mstr.add "val" (Json_base.String s) m in
      Json_base.Record m
  | Integer r ->
      let m = Mstr.add "type" (Json_base.String "Integer") Mstr.empty in
      let m = Mstr.add "val" (Json_base.String (BigInt.to_string r.int_value)) m in
      Json_base.Record m
  | Float f ->
      let m = Mstr.add "type" (Json_base.String "Float") Mstr.empty in
      let m = Mstr.add "val" (convert_float_value f) m in
      Json_base.Record m
  | Decimal d ->
      let m = Mstr.add "type" (Json_base.String "Decimal") Mstr.empty in
      let m = Mstr.add "val" (Json_base.String (Format.sprintf "%s.%s" (BigInt.to_string d.dec_int) (BigInt.to_string d.dec_frac))) m in
      Json_base.Record m
  | Fraction f ->
      let m = Mstr.add "type" (Json_base.String "Fraction") Mstr.empty in
      let m = Mstr.add "val" (Json_base.String (Format.sprintf "%s/%s" (BigInt.to_string f.frac_nom) (BigInt.to_string f.frac_den))) m in
      Json_base.Record m
  | Unparsed s ->
      let m = Mstr.add "type" (Json_base.String "Unparsed") Mstr.empty in
      let m = Mstr.add "val" (Json_base.String s) m in
      Json_base.Record m
  | Bitvector bv ->
      let m = Mstr.add "type" (Json_base.String "Integer") Mstr.empty in
      let m = Mstr.add "val" (Json_base.String (BigInt.to_string bv.bv_value)) m in
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
        Json_base.Record m in
      let m = Mstr.add "type" (Json_base.String "Apply") Mstr.empty in
      let m = Mstr.add "val" slt m in
      Json_base.Record m
  | Record r -> convert_record r
  | Proj p -> convert_proj p
  | Undefined ->
      let m = Mstr.add "type" (Json_base.String "Undefined") Mstr.empty in
      Json_base.Record m

and convert_array a =
  let m_others =
    Mstr.add "others" (convert_model_value a.arr_others) Mstr.empty in
  convert_indices a.arr_indices @ [Json_base.Record m_others]

and convert_indices indices =
  match indices with
  | [] -> []
  | index :: tail ->
      let m =
        Mstr.add "indice" (convert_model_value index.arr_index_key) Mstr.empty
      in
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
  | Plus_infinity -> fprintf fmt "+∞"
  | Minus_infinity -> fprintf fmt "-∞"
  | Plus_zero -> fprintf fmt "+0"
  | Minus_zero -> fprintf fmt "-0"
  | Not_a_number -> fprintf fmt "NaN"
  | Float_number {hex= Some hex} ->
      fprintf fmt "%s (%g)" hex (float_of_string hex)
  | Float_number {binary= {sign; exp; mant}} ->
      fprintf fmt "float_bits(%s,%s,%s)" sign.bv_verbatim exp.bv_verbatim mant.bv_verbatim

let print_integer fmt (i: BigInt.t) =
  pp_print_string fmt (BigInt.to_string i);
  if BigInt.(gt (abs i) (of_int 9)) then
    (* Print hex representation only when it isn't redundant *)
    fprintf fmt " (%t0X%a)"
      (fun fmt -> if BigInt.sign i < 0 then pp_print_string fmt "-")
      (Number.print_in_base 16 None) (BigInt.abs i)

let rec print_array_human fmt (arr : model_array) =
  let print_others fmt v =
    fprintf fmt "@[others =>@ %a@]" print_model_value_human v in
  let print_key_val fmt arr =
    let {arr_index_key= key; arr_index_value= v} = arr in
    fprintf fmt "@[%a =>@ %a@]" print_model_value_human key
      print_model_value_human v in
  fprintf fmt "@[(%a%a)@]"
    (Pp.print_list_delim ~start:Pp.nothing ~stop:Pp.comma ~sep:Pp.comma
       print_key_val)
    arr.arr_indices print_others arr.arr_others

and print_record_human fmt r =
  match r with
  | [(_, value)] ->
      (* Special pretty printing for record with only one element *)
      fprintf fmt "%a" print_model_value_human value
  | _ ->
      fprintf fmt "@[<hv1>%a@]"
        (Pp.print_list_delim ~start:Pp.lbrace ~stop:Pp.rbrace ~sep:Pp.semi
           (fun fmt (f, v) ->
             fprintf fmt "@[%s =@ %a@]" f print_model_value_human v))
        r

and print_proj_human fmt p =
  let s, v = p in
  fprintf fmt "@[{%s =>@ %a}@]" s print_model_value_human v

and print_bv fmt (bv : model_bv) =
  (* TODO Not implemented yet. Ideally, fix the differentiation made in the
     parser between Bv_int and Bv_sharp -> convert Bv_int to Bitvector not
     Integer. And print Bv_int exactly like Bv_sharp.
  *)
  fprintf fmt "%s" bv.bv_verbatim

and print_model_value_human fmt (v : model_value) =
  match v with
  | String s -> Constant.print_string_def fmt s
  | Integer i -> print_integer fmt i.int_value
  | Decimal d -> fprintf fmt "%s.%s" (BigInt.to_string d.dec_int) (BigInt.to_string d.dec_frac)
  | Fraction f -> fprintf fmt "%s/%s" (BigInt.to_string f.frac_nom) (BigInt.to_string f.frac_den)
  | Float f -> print_float_human fmt f
  | Boolean b -> fprintf fmt "%b" b
  | Apply (s, []) -> fprintf fmt "%s" s
  | Apply (s, lt) ->
      fprintf fmt "@[(%s@ %a)@]" s
        (Pp.print_list Pp.space print_model_value_human)
        lt
  | Array arr -> print_array_human fmt arr
  | Record r -> print_record_human fmt r
  | Proj p -> print_proj_human fmt p
  | Bitvector s -> print_bv fmt s
  | Undefined -> fprintf fmt "UNDEFINED"
  | Unparsed s -> fprintf fmt "%s" s

(*
***************************************************************
**  Model elements
***************************************************************
*)

type model_element_kind =
  | Result
  | Old
  | At of string
  | Error_message
  | Loop_before
  | Loop_previous_iteration
  | Loop_current_iteration
  | Other

type model_element_name = {
  men_name: string;
  men_kind: model_element_kind; (* Attributes associated to the id of the men *)
  men_attrs: Sattr.t;
}

type model_element = {
  me_name: model_element_name;
  me_value: model_value;
  me_location: Loc.position option;
  me_term: Term.term option;
}

let model_trace_is_result attrs =
  match Ident.get_model_trace_attr ~attrs with
  | exception Not_found -> false
  | a ->
      match Strings.(bounded_split '@' a.attr_string 3) with
      | _ :: "result" :: _ -> true
      | _ -> false

let create_model_element ~name ~value ~attrs =
  let kind = if model_trace_is_result attrs then Result else Other in
  let me_name = {men_name= name; men_kind= kind; men_attrs= attrs} in
  {me_name; me_value= value; me_location= None; me_term= None}

let create_model_element_name name attrs : model_element_name =
  let kind = if model_trace_is_result attrs then Result else Other in
  {men_name= name; men_kind= kind; men_attrs= attrs}

(*
***************************************************************
**  Model definitions
***************************************************************
*)

type model_file = model_element list Mint.t
type model_files = model_file Mstr.t

type model = {
  model_files: model_files;
  vc_term_loc: Loc.position option;
  vc_term_attrs: Sattr.t;
}

let map_filter_model_files f =
  let f_list elts =
    match Lists.map_filter f elts with
    | [] -> None | l -> Some l in
  let f_files mf =
    let mf = Mint.map_filter f_list mf in
    if Mint.is_empty mf then None else Some mf in
  Mstr.map_filter f_files

let map_filter_model_elements f m =
  {m with model_files= map_filter_model_files f m.model_files}

let empty_model_file = Mint.empty
let empty_model_files = Mstr.empty
let is_model_empty m = Mstr.is_empty m.model_files

let empty_model =
  {vc_term_loc=None; vc_term_attrs=Sattr.empty; model_files=empty_model_files}

let set_model_files model model_files =
  { model with model_files }

let get_model_elements m =
  List.(concat (concat (map Mint.values (Mstr.values m.model_files))))

let get_model_term_loc m = m.vc_term_loc
let get_model_term_attrs m = m.vc_term_attrs

let trace_by_id id =
  Ident.get_model_trace_string ~name:id.id_string ~attrs:id.id_attrs

let trace_by_men men =
  Ident.get_model_trace_string ~name:men.men_name ~attrs:men.men_attrs

let get_model_element model name loc =
  let aux me =
    trace_by_men me.me_name = name &&
    Opt.equal Loc.equal me.me_location (Some loc) in
  List.find_opt aux (get_model_elements model)

let get_model_element_value model name loc =
  let aux me =
    trace_by_men me.me_name = name &&
    Opt.equal Loc.equal me.me_location (Some loc) in
  List.find_opt aux (get_model_elements model)

let get_model_element_by_id model id =
  match id.id_loc with
  | None -> None
  | Some loc -> get_model_element_value model (trace_by_id id) loc

let get_model_element_by_loc model loc =
  let aux me = Opt.equal Loc.equal me.me_location (Some loc) in
  List.find_opt aux (get_model_elements model)

(*
***************************************************************
**  Quering the model
***************************************************************
*)

(* Adapt kind to matching label *)
let fix_loc_kind ~at_loc name =
  let aux attr_at (labels_added, name) =
    try
      Scanf.sscanf attr_at.attr_string "at:%[^:]:loc:%[^:]:%d" @@ fun label loc_file loc_line ->
      if at_loc = (Filename.basename loc_file, loc_line) &&
         not (Sstr.mem label labels_added) &&
         label <> "'Old" (* Already dealt with in [get_kind] *)
      then Sstr.add label labels_added, {name with men_kind=At label}
      else labels_added, name
    with End_of_file | Scanf.Scan_failure _ ->
      labels_added, name in
  snd (Sattr.fold aux name.men_attrs (Sstr.empty, name))

let cmp_attrs a1 a2 =
  String.compare a1.attr_string a2.attr_string

let print_model_element ?(print_locs=false) ~at_loc ~print_attrs ~print_model_value ~me_name_trans fmt m_element =
  match m_element.me_name.men_kind with
  | Error_message -> fprintf fmt "%s" m_element.me_name.men_name
  | _ ->
      let m_element = {m_element with me_name=fix_loc_kind ~at_loc m_element.me_name} in
      fprintf fmt "@[<hv2>@[<hov2>%s%t%t =@]@ %a@]" (me_name_trans m_element.me_name)
        (fun fmt ->
           if print_attrs then
             fprintf fmt " %a" Pp.(print_list space Pretty.print_attr)
               (List.sort cmp_attrs (Sattr.elements m_element.me_name.men_attrs)))
        (fun fmt ->
           if print_locs then fprintf fmt " (%a)"
               (Pp.print_option_or_default "NO LOC "Pretty.print_loc) m_element.me_location)
        print_model_value m_element.me_value

let similar_model_element_names me_nm1 me_nm2 =
  (* TODO Add an efficient version of symmetric difference to extset *)
  let symm_diff = Sattr.diff (Sattr.union me_nm1.men_attrs me_nm2.men_attrs)
                    (Sattr.inter me_nm1.men_attrs me_nm2.men_attrs) in
  Ident.get_model_trace_string ~name:me_nm1.men_name ~attrs:me_nm1.men_attrs
  = Ident.get_model_trace_string ~name:me_nm2.men_name ~attrs:me_nm2.men_attrs
  && Sattr.for_all (fun x ->
         not (Strings.has_prefix "at" x.attr_string)) symm_diff

(* TODO optimize *)
let rec filter_duplicated l =
  let exist_similar a l = List.exists (fun x ->
    similar_model_element_names a.me_name x.me_name) l in
  match l with
  | [] | [_] -> l
  | me :: l when exist_similar me l -> filter_duplicated l
  | me :: l -> me :: filter_duplicated l

let print_model_elements ~filter_similar ~at_loc ~print_attrs ?(sep = Pp.newline)
    ~print_model_value ~me_name_trans fmt m_elements =
  let m_elements =
    if filter_similar then filter_duplicated m_elements else m_elements in
  fprintf fmt "@[%a@]"
    (Pp.print_list sep
       (print_model_element ?print_locs:None ~at_loc ~print_attrs ~print_model_value
          ~me_name_trans))
    m_elements

let print_model_file ~filter_similar ~print_attrs ~print_model_value ~me_name_trans fmt (filename, model_file) =
  (* Relativize does not work on nighly bench: using basename instead. It
     hides the local paths. *)
  let filename = Filename.basename filename in
  let pp fmt (line, m_elements) =
    fprintf fmt "  @[<v 2>Line %d:@ %a@]" line
      (print_model_elements ~filter_similar ?sep:None ~at_loc:(filename, line) ~print_attrs
         ~print_model_value ~me_name_trans) m_elements in
  fprintf fmt "@[<v 0>File %s:@ %a@]" filename
    Pp.(print_list space pp) (Mint.bindings model_file)

let why_name_trans men =
  let name = get_model_trace_string ~name:men.men_name ~attrs:men.men_attrs in
  let name = List.hd (Strings.bounded_split '@' name 2) in
  match men.men_kind with
  | Result -> "result"
  | Old -> "old "^name
  | At l -> name^" at "^l
  (* | Loop_before -> "[before loop] "^name *)
  | Loop_previous_iteration -> "[before iteration] "^name
  | Loop_current_iteration -> "[current iteration] "^name
  | _ -> name

let json_name_trans men =
  let name = get_model_trace_string ~name:men.men_name ~attrs:men.men_attrs in
  let name = List.hd (Strings.bounded_split '@' name 2) in
  match men.men_kind with
  | Result -> "result"
  | Old -> "old "^name
  | _ -> name

let print_model ~filter_similar ~print_attrs ?(me_name_trans = why_name_trans)
    ~print_model_value fmt model =
  Pp.print_list Pp.newline (print_model_file ~filter_similar ~print_attrs ~print_model_value ~me_name_trans)
    fmt (Mstr.bindings model.model_files)

let print_model_human ?(filter_similar = true) ?(me_name_trans = why_name_trans) fmt model =
  print_model ~filter_similar ~me_name_trans ~print_model_value:print_model_value_human fmt model

let print_model ?(filter_similar = true) ?(me_name_trans = why_name_trans) ~print_attrs fmt model =
  print_model ~filter_similar ~print_attrs ~me_name_trans ~print_model_value fmt model

let get_model_file model filename =
  Mstr.find_def empty_model_file filename model

let get_elements model_file line_number =
  Mint.find_def [] line_number model_file

let get_padding line =
  try
    let r = Re.Str.regexp " *" in
    ignore (Re.Str.search_forward r line 0) ;
    Re.Str.matched_string line
  with Not_found -> ""

(* This assumes that l is sorted and split the list of locations in two:
   those that are applied on this line and the others. For those that are on
   this line, we split the locations that appear on several lines. *)
let rec partition_loc line lc l =
  match l with
  | (hd, a) :: tl ->
      let hdf, hdl, hdfc, hdlc = Loc.get hd in
      if hdl = line then
        if hdlc > lc then
          let old_sloc = Loc.user_position hdf hdl hdfc lc in
          let newlc = hdlc - lc in
          let new_sloc = Loc.user_position hdf (hdl + 1) 1 newlc in
          let rem_loc, new_loc = partition_loc line lc tl in
          ((new_sloc, a) :: rem_loc, (old_sloc, a) :: new_loc)
        else
          let rem_loc, new_loc = partition_loc line lc tl in
          (rem_loc, (hd, a) :: new_loc)
      else (l, [])
  | _ -> (l, [])

(* Change a locations so that it points to a different line number *)
let add_offset off (loc, a) =
  let f, l, fc, lc = Loc.get loc in
  (Loc.user_position f (l + off) fc lc, a)

let interleave_line ~filename ~print_attrs start_comment end_comment
    me_name_trans model_file
    (source_code, line_number, offset, remaining_locs, locs) line =
  let remaining_locs, list_loc =
    partition_loc line_number (String.length line) remaining_locs in
  let list_loc = List.map (add_offset offset) list_loc in
  try
    let model_elements = Mint.find line_number model_file in
    let cntexmp_line =
      asprintf "@[<h 0>%s%s%a%s@]" (get_padding line) start_comment
        (print_model_elements ~filter_similar:true ~sep:Pp.semi ~at_loc:(filename, line_number)
           ~print_attrs ~print_model_value:print_model_value_human ~me_name_trans)
        model_elements end_comment in
    (* We need to know how many lines will be taken by the counterexample. This
       is ad hoc as we don't really know how the lines are split in IDE. *)
    let len_cnt = 1 + (String.length cntexmp_line / 80) in
    ( source_code ^ line ^ cntexmp_line ^ "\n"
    , line_number + 1
    , offset + len_cnt
    , remaining_locs
    , list_loc @ locs )
  with Not_found ->
    ( source_code ^ line
    , line_number + 1
    , offset
    , remaining_locs
    , list_loc @ locs )

let interleave_with_source ~print_attrs ?(start_comment = "(* ")
    ?(end_comment = " *)") ?(me_name_trans = why_name_trans) model ~rel_filename
    ~source_code ~locations =
  let locations =
    List.sort
      (fun x y -> compare (fst x) (fst y))
      (List.filter
         (fun x ->
           let f, _, _, _ = Loc.get (fst x) in
           f = rel_filename)
         locations) in
  try
    (* There is no way to compare rel_filename and the locations of filename in
       the file because they contain extra ".." which cannot be reliably removed
       (because of potential symbolic link). So, we use the basename.
    *)
    let rel_filename = Filename.basename rel_filename in
    let model_files =
      Mstr.filter
        (fun k _ -> Filename.basename k = rel_filename)
        model.model_files in
    let model_file = snd (Mstr.choose model_files) in
    let src_lines_up_to_last_cntexmp_el source_code model_file =
      let last_cntexmp_line, _ = Mint.max_binding model_file in
      Re.Str.bounded_split (Re.Str.regexp "^") source_code
        (last_cntexmp_line + 1) in
    let source_code, _, _, _, gen_loc =
      List.fold_left
        (interleave_line ~filename:rel_filename ~print_attrs start_comment
           end_comment me_name_trans model_file)
        ("", 1, 0, locations, [])
        (src_lines_up_to_last_cntexmp_el source_code model_file) in
    (source_code, gen_loc)
  with Not_found -> (source_code, locations)

let print_attrs_json (me : model_element_name) fmt =
  Json_base.list
    (fun fmt attr -> Json_base.string fmt attr.attr_string)
    fmt
    (List.sort cmp_attrs (Sattr.elements me.men_attrs))

(* Compute the kind of a model_element using its attributes and location *)
let compute_kind (me : model_element) =
  let me_kind = me.me_name.men_kind in
  let location = me.me_location in
  let attrs = me.me_name.men_attrs in
  let me_kind =
    (* We match on the attribute on the form [@at:'Old:loc:file:line]. If it
       exists, depending on the location of the me, we use it or not. If it
       does not we keep me_kind.
    *)
    match
      Sattr.choose
        (Sattr.filter
           (fun x -> Strings.has_prefix "at:'Old:" x.attr_string)
           attrs)
    with
    | exception Not_found -> me_kind
    | a -> (
      match (Strings.split ':' a.attr_string, location) with
      | ["at"; "'Old"; "loc"; file; line_number], Some location ->
          let loc_file, loc_line, _, _ = Loc.get location in
          if loc_file = file && loc_line = int_of_string line_number then Old
          else me_kind
      | _ -> me_kind ) in
  me_kind

(*
**  Quering the model - json
*)
let print_model_element_json me_name_to_str fmt me =
  let print_value fmt = fprintf fmt "%a" print_model_value_sanit me.me_value in
  let print_kind fmt =
    (* We compute kinds using the attributes and locations *)
    match compute_kind me with
    | Result -> fprintf fmt "%a" Json_base.string "result"
    | At l -> fprintf fmt "@%s" l
    | Old -> fprintf fmt "%a" Json_base.string "old"
    | Error_message -> fprintf fmt "%a" Json_base.string "error_message"
    | Other -> fprintf fmt "%a" Json_base.string "other"
    | Loop_before -> fprintf fmt "%a" Json_base.string "before_loop"
    | Loop_previous_iteration ->
        fprintf fmt "%a" Json_base.string "before_iteration"
    | Loop_current_iteration ->
        fprintf fmt "%a" Json_base.string "current_iteration" in
  let print_name fmt = Json_base.string fmt (me_name_to_str me.me_name) in
  let print_json_attrs fmt = print_attrs_json me.me_name fmt in
  let print_value_or_kind_or_name fmt printer = printer fmt in
  Json_base.map_bindings (fun s -> s) print_value_or_kind_or_name fmt
    [ ("name", print_name); ("attrs", print_json_attrs);
      ("value", print_value) ; ("kind", print_kind) ]

let print_model_elements_json me_name_to_str fmt model_elements =
  let model_elements = filter_duplicated model_elements in
  Json_base.list (print_model_element_json me_name_to_str) fmt model_elements

let print_model_elements_on_lines_json model me_name_to_str vc_line_trans fmt
    (file_name, model_file) =
  Json_base.map_bindings
    (fun i ->
      match model.vc_term_loc with
      | None -> string_of_int i
      | Some pos ->
          let vc_file_name, line, _, _ = Loc.get pos in
          if file_name = vc_file_name && i = line then vc_line_trans i
          else string_of_int i)
    (print_model_elements_json me_name_to_str)
    fmt
    (Mint.bindings model_file)

let print_model_json ?(me_name_trans = json_name_trans)
    ?(vc_line_trans = fun i -> string_of_int i) fmt model =
  let model_files_bindings =
    List.fold_left
      (fun bindings (file_name, model_file) ->
        List.append bindings [(file_name, (file_name, model_file))])
      []
      (Mstr.bindings model.model_files) in
  Json_base.map_bindings
    (fun s -> s)
    (print_model_elements_on_lines_json model me_name_trans vc_line_trans)
    fmt model_files_bindings

(*
***************************************************************
**  Building the model from raw model
***************************************************************
*)

let at_old_kind at_loc attrs =
  let rec search = function
    | [] -> None
    | attr :: attrs ->
        try
          Scanf.sscanf attr.attr_string "at:%[^:]:loc:%[^:]:%d" @@
          fun label loc_file loc_line ->
          if at_loc = (loc_file, loc_line) then
            Some (if label = "'Old" then Old else At label)
          else
            search attrs
        with End_of_file | Scanf.Scan_failure _ ->
          search attrs in
  search (Sattr.elements attrs)

let loc_starts_le loc1 loc2 =
  loc1 <> Loc.dummy_position && loc2 <> Loc.dummy_position &&
  let f1, l1, b1, _ = Loc.get loc1 in
  let f2, l2, b2, _ = Loc.get loc2 in
  f1 = f2 && l1 <= l2 && l1 <= l2 && b1 <= b2

let while_loop_kind vc_attrs var_loc =
  let is_inv_pres a = a.attr_string = "expl:loop invariant preservation" in
  if Sattr.exists is_inv_pres vc_attrs then
    let loop_loc =
      let is_while a = Strings.has_prefix "loop:" a.attr_string in
      let attr = Sattr.choose (Sattr.filter is_while vc_attrs) in
      Scanf.sscanf attr.attr_string "loop:%[^:]:%d:%d:%d"
        Loc.user_position in
    let kind =
      if var_loc = loop_loc then Loop_previous_iteration
      else if loc_starts_le loop_loc var_loc then Loop_current_iteration
      else Loop_before in
    Some kind
  else None

let fix_kind at_loc vc_attrs me =
  let men_kind =
    match at_old_kind at_loc me.me_name.men_attrs with
    | Some k -> k
    | None -> (
        match Opt.map (while_loop_kind vc_attrs) me.me_location with
        | Some (Some k) -> k
        | _ -> me.me_name.men_kind) in
  {me with me_name={me.me_name with men_kind}}

let add_to_model ?vc_term_attrs model_element model =
  match model_element.me_location with
  | None -> model
  | Some pos ->
      let filename, line_number, _, _ = Loc.get pos in
      let model_file = get_model_file model filename in
      let elements = get_elements model_file line_number in
      let model_element =
        match vc_term_attrs with
        | Some vc_term_attrs ->
            fix_kind (filename, line_number) vc_term_attrs model_element
        | None -> model_element in
      let el = model_element.me_name in
      (* This removes elements that are duplicated *)
      let found_elements =
        List.exists (fun x ->
            similar_model_element_names x.me_name el
            && pos = Opt.get_def Loc.dummy_position x.me_location)
          elements in
      let elements = if found_elements then elements
                     else model_element :: elements in
      let model_file = Mint.add line_number elements model_file in
      Mstr.add filename model_file model

let recover_name pm list_projs raw_name =
  let name, attrs =
    try
      let t = Mstr.find raw_name pm.queried_terms in
      match t.t_node with
      | Tapp (ls, []) -> (ls.ls_name.id_string, t.t_attrs)
      | _ -> ("", t.t_attrs)
    with Not_found ->
      let id = Mstr.find raw_name list_projs in
      (id.id_string, id.id_attrs) in
  create_model_element_name (get_model_trace_string ~name ~attrs) attrs

(** [replace_projection const_function mv] replaces record names, projections, and application callees
   in [mv] using [const_function] *)
let rec replace_projection (const_function : string -> string) =
  let const_function s = try const_function s with Not_found -> s in
  function
  | Integer _ | Decimal _ | Fraction _ | Float _ | Boolean _ | Bitvector _
  | String _ | Undefined | Unparsed _ as mv -> mv
  | Record fs ->
      let aux (f, mv) = const_function f, replace_projection const_function mv in
      Record (List.map aux fs)
  | Proj (f, mv) ->
      Proj (const_function f, replace_projection const_function mv)
  | Array a -> Array (replace_projection_array const_function a)
  | Apply (s, l) ->
      Apply (const_function s, List.map (replace_projection const_function) l)

and replace_projection_array const_function a =
  let for_index a =
    let arr_index_value = replace_projection const_function a.arr_index_value in
    {a with arr_index_value} in
  {arr_others= replace_projection const_function a.arr_others;
   arr_indices= List.map for_index a.arr_indices}

(* Elements that are of record with only one field in the source code, are
   simplified by eval_match in wp generation. So, this allows to reconstruct
   their value (using the "field" attribute that were added). *)
let read_one_fields ~attrs value =
  let field_names =
    let fields = Lists.map_filter Ident.extract_field (Sattr.elements attrs) in
    List.sort (fun (d1, _) (d2, _) -> d2 - d1) fields in
  let add_record v (_, f) = Record [f, v] in
  match Ident.get_model_trace_attr ~attrs with
  | mtrace -> (
      let attrs = Sattr.remove mtrace attrs in
      (* Special cases for 'Last and 'First. TODO: Should be avoided here but
         there is no simple way. *)
      try
        let new_mtrace =
          Strings.remove_suffix "'Last" mtrace.attr_string ^
          String.concat "" (List.map snd field_names) ^
          "'Last" in
        let new_attr = create_attribute new_mtrace in
        Sattr.add new_attr attrs, value
      with Not_found ->
      try
        let new_mtrace =
          Strings.remove_suffix "'First" mtrace.attr_string ^
          String.concat "" (List.map snd field_names) ^
          "'First" in
        let new_attr = create_attribute new_mtrace in
        Sattr.add new_attr attrs, value
      with Not_found -> (* General case *)
        Sattr.add mtrace attrs, List.fold_left add_record value field_names )
  | exception Not_found ->
      (* No model trace attribute present, same as general case *)
      attrs, List.fold_left add_record value field_names

let internal_loc t =
  match t.t_node with
  | Tvar vs -> vs.vs_name.id_loc
  | Tapp (ls, []) -> ls.ls_name.id_loc
  | _ -> None

let remove_field : (Sattr.t * model_value -> Sattr.t * model_value) ref = ref (fun x -> x)
let register_remove_field f = remove_field := f

(** Build the model by replacing projections and restore single field records in the model
   elements, and adding the element at all relevant locations *)
let build_model_rec pm (elts: model_element list) : model_files =
  let add_with_loc ~vc_term_attrs model_elt loc model =
    match loc with
    | None -> model
    | me_location -> add_to_model ~vc_term_attrs {model_elt with me_location} model in
  let list_projs = list_projs pm and vc_term_attrs = pm.Printer.vc_term_attrs in
  let process_me me =
    assert (me.me_location = None && me.me_term = None);
    let aux t =
      let attrs = Sattr.union me.me_name.men_attrs t.t_attrs in
      let name, attrs = match t.t_node with
        | Tapp (ls, []) -> ls.ls_name.id_string, Sattr.union attrs ls.ls_name.id_attrs
        | _ -> "", attrs in
      (* Replace projections with their real name *)
      let me_value = replace_projection
          (fun s -> (recover_name pm list_projs s).men_name)
          me.me_value in
      (* Remove some specific record field related to the front-end language.
         This function is registered. *)
      let attrs, me_value = !remove_field (attrs, me_value) in
      (* Transform value flattened by eval_match (one field record) back to records *)
      let attrs, me_value = read_one_fields ~attrs me_value in
      let me_name = create_model_element_name name attrs in
      {me_name; me_value; me_location= t.t_loc; me_term= Some t} in
    Opt.map aux (Mstr.find_opt me.me_name.men_name pm.queried_terms) in
  (** Add a model element at the relevant locations *)
  let add_model_elt model me =
    let model = add_to_model ~vc_term_attrs me model in
    let model = add_with_loc ~vc_term_attrs me (internal_loc (Opt.get me.me_term)) model in
    let add_written_loc a =
      add_with_loc ~vc_term_attrs me (Ident.extract_written_loc a) in
    Sattr.fold add_written_loc me.me_name.men_attrs model in
  List.fold_left add_model_elt Mstr.empty (Lists.map_filter process_me elts)

let handle_contradictory_vc vc_term_loc model_files =
  (* The VC is contradictory if the location of the term that triggers VC
     was collected, model_files is not empty, and there are no model elements
     in this location.
     If this is the case, add model element saying that VC is contradictory
     to this location. *)
  if Mstr.is_empty model_files then
    (* If the counterexample model was not collected, then model_files
       is empty and this does not mean that VC is contradictory. *)
    model_files
  else match vc_term_loc with
    | None -> model_files
    | Some pos ->
        let filename, line_number, _, _ = Loc.get pos in
        let model_file = get_model_file model_files filename in
        match get_elements model_file line_number with
        | [] ->
            (* The vc is contradictory, add special model element  *)
            let me = {
              me_name= {
                men_name= "the check fails with all inputs";
                men_kind= Error_message;
                men_attrs= Sattr.empty;
              };
              me_value= Unparsed "";
              me_location= Some pos;
              me_term= None;
            } in
            add_to_model me model_files
        | _ -> model_files

(*
***************************************************************
** Model cleaning
***************************************************************
*)

let opt_bind_any os f =
  f (Lists.map_filter (fun x -> x) os)

let opt_bind_all os f =
  if List.for_all Opt.inhabited os then
    f (List.map Opt.get os)
  else None

class clean = object (self)
  method model m =
    {m with model_files= map_filter_model_files self#element m.model_files}
  method element me =
    if me.me_name.men_kind = Error_message then
      (* Keep unparsed values for error messages *)
      Some me
    else
      Opt.bind (self#value me.me_value) @@ fun me_value ->
      Some {me with me_value}
  method value v = match v with
    | Unparsed s    -> self#unparsed s | String v      -> self#string v
    | Integer v     -> self#integer v  | Decimal v     -> self#decimal v
    | Fraction v    -> self#fraction v | Float v       -> self#float v
    | Boolean v     -> self#boolean v  | Bitvector v   -> self#bitvector v
    | Proj (p, v)   -> self#proj p v   | Apply (s, vs) -> self#apply s vs
    | Array a       -> self#array a    | Record fs     -> self#record fs
    | Undefined     -> self#undefined
  method unparsed _ = None
  method string v = Some (String v)
  method integer v = Some (Integer v)
  method decimal v = Some (Decimal v)
  method fraction v = Some (Fraction v)
  method float v = Some (Float v)
  method boolean v = Some (Boolean v)
  method bitvector v = Some (Bitvector v)
  method proj p v =
    Opt.bind (self#value v) @@ fun v ->
    Some (Proj (p, v))
  method apply s vs =
    opt_bind_all (List.map self#value vs) @@ fun vs ->
    Some (Apply (s, vs))
  method array a =
    let clean_arr_index ix =
      Opt.bind (self#value ix.arr_index_key) @@ fun key ->
      Opt.bind (self#value ix.arr_index_value) @@ fun value ->
      Some {arr_index_key= key; arr_index_value= value} in
    Opt.bind (self#value a.arr_others) @@ fun others ->
    opt_bind_any (List.map clean_arr_index a.arr_indices) @@ fun indices ->
    Some (Array {arr_others= others; arr_indices= indices})
  method record fs =
    let clean_field (f, v) =
      Opt.bind (self#value v) @@ fun v ->
      Some (f, v) in
    opt_bind_all (List.map clean_field fs) @@ fun fs ->
    Some (Record fs)
  method undefined = Some Undefined
end

let clean = ref (new clean)

let customize_clean c = clean := (c :> clean)

(*
***************************************************************
**  Filtering the model
***************************************************************
*)

let add_loc orig_model new_model position =
  (* Add a given location from orig_model to new_model *)
  let file_name, line_num, _, _ = Loc.get position in
  let orig_model_file = get_model_file orig_model file_name in
  let new_model_file = get_model_file new_model file_name in
  if Mint.mem line_num new_model_file then
    (* the location already is in new_model *)
    new_model
  else
    try
      (* get the location from original model *)
      let line_map = Mint.find line_num orig_model_file in
      (* add the location to new model *)
      let new_model_file = Mint.add line_num line_map new_model_file in
      Mstr.add file_name new_model_file new_model
    with Not_found -> new_model

let add_first_model_line filename model_file model =
  let line_num, cnt_info = Mint.min_binding model_file in
  let mf = get_model_file model filename in
  let mf = Mint.add line_num cnt_info mf in
  Mstr.add filename mf model

let model_for_positions_and_decls model ~positions =
  (* Start with empty model and add locations from model that
     are in locations *)
  let model_filtered =
    List.fold_left (add_loc model.model_files) empty_model_files positions in
  (* For each file add mapping corresponding to the first line of the
     counter-example from model to model_filtered.
     This corresponds to function declarations *)
  let model_filtered =
    Mstr.fold add_first_model_line model.model_files model_filtered in
  {model with model_files= model_filtered}

(*
***************************************************************
** Registering model parser
***************************************************************
*)

type model_parser = printer_mapping -> string -> model
type raw_model_parser = printer_mapping -> string -> model_element list

let model_parser (raw: raw_model_parser) : model_parser =
  fun ({Printer.vc_term_loc; vc_term_attrs} as pm) str ->
  raw pm str |> (* For example, Smtv2_model_parser.parse for "smtv2" *)
  build_model_rec pm |>
  map_filter_model_files !clean#element |>
  handle_contradictory_vc pm.Printer.vc_term_loc |>
  fun model_files -> { model_files; vc_term_loc; vc_term_attrs }

exception KnownModelParser of string
exception UnknownModelParser of string

type reg_model_parser = Pp.formatted * model_parser

let model_parsers : reg_model_parser Hstr.t = Hstr.create 17

let register_model_parser ~desc s p =
  if Hstr.mem model_parsers s then raise (KnownModelParser s) ;
  Hstr.replace model_parsers s (desc, model_parser p)

let lookup_model_parser s =
  snd (Hstr.find_exn model_parsers (UnknownModelParser s) s)

let list_model_parsers () =
  Hstr.fold (fun k (desc, _) acc -> (k, desc) :: acc) model_parsers []

let () =
  register_model_parser
    ~desc:
      "Model@ parser@ with@ no@ output@ (used@ if@ the@ solver@ does@ not@ \
       support@ models."
    "no_model" (fun _ _ -> [])
