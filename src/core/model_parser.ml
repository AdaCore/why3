(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2022 --  Inria - CNRS - Paris-Saclay University  *)
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


let debug = Debug.register_info_flag "model_parser"
  ~desc:"Print@ debugging@ messages@ about@ parsing@ \
         the@ counter-example@ model."

(*
***************************************************************
**  Model elements
***************************************************************
*)

type model_element_kind =
  | Result
  | Call_result of Loc.position
  | Old
  | At of string
  | Loop_before
  | Loop_previous_iteration
  | Loop_current_iteration
  | Error_message
  | Other

let print_model_kind fmt = function
  | Result -> pp_print_string fmt "Result"
  | Call_result loc -> fprintf fmt "Call_result (file %a)" Loc.pp_position loc
  | Old -> pp_print_string fmt "Old"
  | At l -> fprintf fmt "At %s" l
  | Error_message -> pp_print_string fmt "Error_message"
  | Loop_before -> pp_print_string fmt "Loop_before"
  | Loop_previous_iteration -> pp_print_string fmt "Loop_previous_iteration"
  | Loop_current_iteration -> pp_print_string fmt "Loop_current_iteration"
  | Other -> pp_print_string fmt "Other"

type model_element = {
  me_kind: model_element_kind;
  me_value: term;
  me_location: Loc.position option;
  me_attrs: Sattr.t;
  me_lsymbol: lsymbol;
}

let create_model_element ~value ~oloc ~attrs ~lsymbol =
  {me_kind= Other; me_value= value; me_location= oloc; me_attrs= attrs; me_lsymbol= lsymbol}

let get_name me =
  Ident.get_model_trace_string
    ~name:(me.me_lsymbol.ls_name.Ident.id_string) ~attrs:(me.me_attrs)
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

(** [search_model_element ?file ?line m p] searches a model element [me] in
    model [m], whose file is [file] and line is [line], and which fullfils
    [p me]. *)
let search_model_element ?file ?line m p =
  let iter_line f line' mes = if line = None || line = Some line' then
      List.iter f mes in
  let iter_file f file' lines = if file = None || file = Some file' then
      Mint.iter (iter_line f) lines in
  let iter_files f = Mstr.iter (iter_file f) m.model_files in
  try Some (Util.iter_first iter_files p) with Not_found -> None

let trace_by_id id =
  Ident.get_model_trace_string ~name:id.id_string ~attrs:id.id_attrs

let trace_by_name me =
  Ident.get_model_trace_string ~name:(get_name me) ~attrs:(me.me_attrs)

let search_model_element_for_id m ?loc id =
  let oloc = if loc <> None then loc else id.id_loc in
  let id_trace = trace_by_id id in
  let p me =
    if trace_by_name me = id_trace &&
       Opt.equal Loc.equal me.me_location oloc
    then Some me else None in
  search_model_element m p

let matching_call_id id attrs =
  Opt.equal Int.equal (Some id)
    (search_attribute_value get_call_id_value attrs)

let matching_call_result_loc attrs loc =
  Opt.equal Loc.equal (Some loc)
    (search_attribute_value get_call_result_loc attrs)

let search_model_element_call_result model call_id loc =
  let p me = (* [@model_trace:result] [@call_result_loc:<loc>] [@RAC:call_id:<id>] *)
    let has_model_trace_result attrs =
      get_model_trace_string ~name:"" ~attrs = "result" in
    if (match call_id with
        | Some call_id ->
            matching_call_id call_id me.me_attrs
        | None ->
            has_model_trace_result me.me_attrs &&
            matching_call_result_loc me.me_attrs loc)
    then Some me else None in
  search_model_element model p

(*
***************************************************************
**  Converting the model elements to JSON
***************************************************************
*)

let cmp_attrs a1 a2 =
  String.compare a1.attr_string a2.attr_string

let find_call_id = Ident.search_attribute_value Ident.get_call_id_value

let similar_model_element_names n1 n2 =
  let name1 = get_name n1 in
  let name2 = get_name n2 in
  name1 = name2 &&
  Opt.equal (=) (find_call_id n1.me_attrs) (find_call_id n2.me_attrs) &&
  n1.me_kind = n2.me_kind &&
  Strings.has_suffix unused_suffix name1 =
  Strings.has_suffix unused_suffix name2

(* TODO_WIP *)
(* TODO optimize *)
let rec filter_duplicated l =
  let exist_similar a l = List.exists (fun x ->
    similar_model_element_names a x) l in
  match l with
  | [] | [_] -> l
  | me :: l when exist_similar me l -> filter_duplicated l
  | me :: l -> me :: filter_duplicated l

let json_type oty =
  let open Json_base in
  let rec type_to_string ty =
    let open Ty in
    let open Pretty in
    match ty.ty_node with
    | Tyvar v -> Format.asprintf "%a" print_tv v
    | Tyapp (ts, [t1;t2]) when ts_equal ts ts_func ->
      Format.asprintf "%s -> %s" (type_to_string t1) (type_to_string t2)
    | Tyapp (ts, []) when is_ts_tuple ts -> "unit"
    | Tyapp (ts, tl) when is_ts_tuple ts ->
      Format.asprintf "(%a)"
        Pp.(print_list comma print_string) (List.map type_to_string tl)
    | Tyapp (ts, []) -> Format.asprintf "%a" print_ts ts
    | Tyapp (ts, tl) ->
      Format.asprintf "%a %a"
        print_ts ts
        Pp.(print_list comma print_string) (List.map type_to_string tl)
  in
  match oty with
  | None -> String "bool"
  | Some ty -> String (type_to_string ty)

let json_lsymbol ls =
  Json_base.String ls.ls_name.id_string

let json_vsymbol ?(with_ty=false) vs =
  let open Pretty in
  let open Json_base in
  let vs_string = Format.asprintf "%a" print_vs vs in
  if with_ty then
    Record [
      "vs", String vs_string;
      "ty", json_type (Some vs.vs_ty)
    ]
  else
    Record [
      "vs", String vs_string;
      "ty", json_type (Some vs.vs_ty)
    ]

let rec json_of_term t =
  let open Json_base in
  match t.t_node with
  | Tvar vs -> Record [
    "Tvar", Record [ "vs", json_vsymbol vs ]
  ]
  | Tconst c ->
    let const_type = match c with
    | ConstInt _ -> "ConstInt"
    | ConstReal _ -> "ConstReal"
    | ConstStr _ -> "ConstStr"
    in
    Record [
      "Tconst", Record [ const_type, String (Format.asprintf "%a" Constant.print_def c) ]
    ]
  | Tapp (ls,ts) ->
    Record [
    "Tapp",
    Record [
      "ls_app", json_lsymbol ls;
      "ls_args", List (List.map json_of_term ts) ]
  ]
  | Tif (t1,t2,t3) -> Record [
    "Tif",
    Record [
      "if", json_of_term t1;
      "then", json_of_term t2;
      "else", json_of_term t3 ]
  ]
  | Tlet (t,tb) ->
    let vs,t' = t_open_bound tb in
      Record [
    "Tlet",
    Record [
      "vs_let", json_vsymbol vs;
      "t_let", json_of_term t;
      "tbound_let", json_of_term t'
    ]
  ]
  | Tcase _ -> Record [ "Tcase", String "UNSUPPORTED" ]
  | Teps tb ->
    let vs,_,t' = t_open_lambda t in
    if vs = [] then
      let vs,t' = t_open_bound tb in
      Record [
      "Teps",
      Record [
        "vs_eps", json_vsymbol vs;
        "t_eps", json_of_term t' ]
      ]
    else
      Record [
      "Tfun",
      Record [
        "args", List (List.map (fun vs -> json_vsymbol ~with_ty:true vs) vs);
        "body", json_of_term t' ]
      ]
  | Tquant (q,tq) ->
    let quant = match q with Tforall -> "Tforall" | Texists -> "Texists" in
    let vsl,_,t' = t_open_quant tq in
    Record [
    "Tquant",
    Record [
      "quant", String quant;
      "vslist", List (List.map (fun vs -> json_vsymbol vs) vsl);
      "t_quant", json_of_term t' ]
  ]
  | Tbinop (op,t1,t2) ->
    let binop = match op with
    | Tand -> "Tand"
    | Tor -> "Tor"
    | Timplies -> "Timplies"
    | Tiff -> "Tiff"
    in
    Record [
    "Tbinop",
    Record [
      "binop", String binop;
      "t1", json_of_term t1;
      "t2", json_of_term t2
    ]
  ]
  | Tnot t' -> Record [
    "Tnot", json_of_term t'
  ]
  | Ttrue -> String "Ttrue"
  | Tfalse -> String "Tfalse"

let json_model_element me =
  let open Json_base in
  let kind =
    match me.me_kind with
    | Result -> "result"
    | Call_result _ -> "result"
    | At l -> Printf.sprintf "@%s" l
    | Old -> "old"
    | Error_message -> "error_message"
    | Other -> "other"
    | Loop_before -> "before_loop"
    | Loop_previous_iteration ->"before_iteration"
    | Loop_current_iteration -> "current_iteration" in
  let loc = Format.asprintf "%a"
    (Pp.print_option_or_default "NO LOC" Pretty.print_loc_as_attribute) me.me_location
  in
  Record [
      "location", String loc;
      "attrs",
        List (List.map
          (fun attr -> String attr.attr_string)
          (List.sort cmp_attrs (Sattr.elements me.me_attrs)));
      "value",
        Record [
          "type", json_type me.me_value.t_ty;
          "node", json_of_term me.me_value ];
      "lsymbol", json_lsymbol me.me_lsymbol;
      "kind", String kind
    ]

let json_model_elements model_elements =
  let model_elements = filter_duplicated model_elements in
  Json_base.List (List.map json_model_element model_elements)

let json_model_elements_on_lines model (file_name, model_file) =
  let l =
    List.map (fun (i, e) ->
        let is_vc_line =
          match model.vc_term_loc with
          | None -> false
          | Some pos ->
              let vc_file_name, line, _, _, _ = Loc.get pos in
              file_name = vc_file_name && i = line in
        Json_base.(Record [
          "loc", String (string_of_int i);
          "is_vc_line", Bool is_vc_line;
          "model_elements", json_model_elements e
        ]))
      (Mint.bindings model_file) in
  Json_base.List l

let json_model model =
  let l =
    List.map (fun (file_name, model_file) ->
        Json_base.(Record [
          "filename", String file_name;
          "model", json_model_elements_on_lines model (file_name, model_file)
        ]))
      (Mstr.bindings model.model_files) in
  Json_base.List l

(*
***************************************************************
**  Quering the model
***************************************************************
*)

(* TODO_WIP print_json_as_term *)
(* let rec print_json_as_term fmt json_value =
  let open Json_base in
  match json_value with
  | Record [ "Tvar", String vs ] -> fprintf fmt "%s" vs
  | Record [ "Tconst", Record [ _, String c ] ] -> fprintf fmt "%s" c
  | Record [ "Tapp", Record [ "ls_app", String ls; "ls_args", List args ] ] ->
    fprintf fmt "%s(%a)" ls
      (Pp.print_list Pp.comma print_json_as_term) args
  | Record [ "Tnot", t ] ->
    fprintf fmt "not(%a)" print_json_as_term t
  | String "True" -> fprintf fmt "true"
  | String "False" -> fprintf fmt "false"
  | _ -> fprintf fmt "" *)

let print_model_element ?(print_locs=false) ~print_attrs ~me_name_trans fmt m_element =
  match m_element.me_kind with
  | Error_message ->
    pp_print_string fmt (get_name m_element)
  | _ ->
      (* let json_value = json_of_term m_element.me_value in *) (* TODO_WIP *)
      fprintf fmt "@[<hv2>@[<hov2>%s%t :@]@ %a = %a@]" (me_name_trans m_element)
        (fun fmt ->
           if print_attrs then
             fprintf fmt " %a" Pp.(print_list space Pretty.print_attr)
               (List.sort cmp_attrs (Sattr.elements m_element.me_attrs));
           if print_locs then
             fprintf fmt " (%a)"
               (Pp.print_option_or_default "NO LOC" Pretty.print_loc_as_attribute)
               m_element.me_location)
        (Pp.print_option (Pretty.print_ty)) m_element.me_value.t_ty
        (Pretty.print_term) m_element.me_value
        (* print_json_as_term json_value *) (* TODO_WIP *)

let print_model_elements ~filter_similar ~print_attrs ?(sep = Pp.newline)
    ~me_name_trans fmt m_elements =
  let m_elements =
    if filter_similar then filter_duplicated m_elements else m_elements in
  fprintf fmt "@[%a@]"
    (Pp.print_list sep
       (print_model_element ?print_locs:None ~print_attrs
          ~me_name_trans))
    m_elements

let print_model_file ~filter_similar ~print_attrs ~me_name_trans fmt (filename, model_file) =
  (* Relativize does not work on nighly bench: using basename instead. It
     hides the local paths. *)
  let filename = Filename.basename filename in
  let pp fmt (line, m_elements) =
    let cmp me1 me2 =
      let n = String.compare (get_name me1) (get_name me2) in
      if n = 0 then Sattr.compare me1.me_attrs me2.me_attrs else n in
    let m_elements = List.sort cmp m_elements in
    fprintf fmt "  @[<v 2>Line %d:@ %a@]" line
      (print_model_elements ~filter_similar ?sep:None ~print_attrs
         ~me_name_trans) m_elements in
  fprintf fmt "@[<v 0>File %s:@ %a@]" filename
    Pp.(print_list space pp) (Mint.bindings model_file)

let why_name_trans me =
  let name = get_name me in
  let name = List.hd (Strings.bounded_split '@' name 2) in
  match me.me_kind with
  | Result -> "result"
  | Call_result loc ->
     asprintf "result of call at %a" Loc.pp_position_no_file loc
  | Old -> "old "^name
  | At l -> name^" at "^l
  | Loop_previous_iteration -> "[before iteration] "^name
  | Loop_current_iteration -> "[current iteration] "^name
  | Loop_before | Error_message | Other -> name

let print_model ~filter_similar ~print_attrs ?(me_name_trans = why_name_trans)
    fmt model =
  Pp.print_list Pp.newline (print_model_file ~filter_similar ~print_attrs ~me_name_trans)
    fmt (Mstr.bindings model.model_files)

let print_model_human ?(filter_similar = true) ?(me_name_trans = why_name_trans) fmt model =
  print_model ~filter_similar ~me_name_trans fmt model

let print_model ?(filter_similar = true) ?(me_name_trans = why_name_trans) ~print_attrs fmt model =
  print_model ~filter_similar ~print_attrs ~me_name_trans fmt model

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
      let f, bl, bc, el, ec = Loc.get hd in
      if bl = line then
        if ec > lc then
          let old_sloc = Loc.user_position f bl bc el lc in
          let newlc = ec - lc in
          let new_sloc = Loc.user_position f (bl + 1) 1 el newlc in
          let rem_loc, new_loc = partition_loc line lc tl in
          ((new_sloc, a) :: rem_loc, (old_sloc, a) :: new_loc)
        else
          let rem_loc, new_loc = partition_loc line lc tl in
          (rem_loc, (hd, a) :: new_loc)
      else (l, [])
  | _ -> (l, [])

(* Change a location so that it points to a different line number *)
let add_offset off (loc, a) =
  let f, bl, bc, el, ec = Loc.get loc in
  (Loc.user_position f (bl + off) bc (el + off) ec, a)

let interleave_line ~filename:_ ~print_attrs start_comment end_comment
    me_name_trans model_file
    (source_code, line_number, offset, remaining_locs, locs) line =
  let remaining_locs, list_loc =
    partition_loc line_number (String.length line) remaining_locs in
  let list_loc = List.map (add_offset offset) list_loc in
  try
    let model_elements = Mint.find line_number model_file in
    let cntexmp_line =
      asprintf "@[<h 0>%s%s%a%s@]" (get_padding line) start_comment
        (print_model_elements ~filter_similar:true ~sep:Pp.semi
           ~print_attrs ~me_name_trans)
        model_elements end_comment in
    (* We need to know how many lines will be taken by the counterexample. This
       is ad hoc as we don't really know how the lines are split in IDE. *)
    let len_cnt = 1 + (String.length cntexmp_line / 80) in
    source_code ^ line ^ cntexmp_line ^ "\n",
    line_number + 1,
    offset + len_cnt,
    remaining_locs,
    list_loc @ locs
  with Not_found ->
    source_code ^ line,
    line_number + 1,
    offset,
    remaining_locs,
    list_loc @ locs

let interleave_with_source ~print_attrs ?(start_comment = "(* ")
    ?(end_comment = " *)") ?(me_name_trans = why_name_trans) model ~rel_filename
    ~source_code ~locations =
  let locations =
    List.sort
      (fun x y -> compare (fst x) (fst y))
      (List.filter
         (fun x ->
           let f, _, _, _,_ = Loc.get (fst x) in
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
(*
***************************************************************
**  Get element kinds
***************************************************************
*)

let loc_starts_le loc1 loc2 =
  loc1 <> Loc.dummy_position && loc2 <> Loc.dummy_position &&
  let f1, l1, b1, _, _ = Loc.get loc1 in
  let f2, l2, b2, _, _ = Loc.get loc2 in
  f1 = f2 && (l1 < l2 || (l1 = l2 && b1 <= b2))

let while_loop_kind vc_attrs var_loc =
  let is_inv_pres a =
    a.attr_string = "expl:loop invariant preservation" ||
    a.attr_string = "expl:loop variant decrease" in
  if Sattr.exists is_inv_pres vc_attrs then
    let loop_loc =
      let is_while a = Strings.has_prefix "loop:" a.attr_string in
      let attr = Sattr.choose (Sattr.filter is_while vc_attrs) in
      Scanf.sscanf attr.attr_string "loop:%[^:]:%d:%d:%d:%d"
        Loc.user_position in
    Some (
      if var_loc = loop_loc then
        Loop_previous_iteration
      else if loc_starts_le loop_loc var_loc then
        Loop_current_iteration
      else
        Loop_before )
  else None

let get_loop_kind vc_attrs oloc () =
  Opt.bind oloc (while_loop_kind vc_attrs)

let get_loc_kind oloc attrs () =
  match oloc with
  | None -> None
  | Some loc ->
      let f,l,_,_,_ = Loc.get loc in
      let search a =
        try
          Scanf.sscanf a.attr_string "at:%[^:]:loc:%[^:]:%d"
            (fun label f' l' ->
               if Filename.basename f = Filename.basename f' && l = l' then
                 Some (if label = "'Old" then Old else At label)
               else
                 None)
        with _ -> None in
      try Some (Lists.first search (Sattr.elements attrs)) with
        Not_found -> None

let get_call_result_kind attrs () =
  Opt.map (fun l -> Call_result l)
    (search_attribute_value get_call_result_loc attrs)

let get_result_kind attrs () =
  match Ident.get_model_trace_attr ~attrs with
  | exception Not_found -> None
  | a ->
      match Strings.(bounded_split '@' a.attr_string 3) with
      | _ :: "result" :: _ -> Some Result
      | _ -> None

let compute_kind vc_attrs oloc attrs =
  try
    Lists.first (fun f -> f ()) [
      get_loc_kind oloc attrs;
      get_call_result_kind attrs;
      get_result_kind attrs;
      get_loop_kind vc_attrs oloc;
    ]
  with Not_found -> Other

(*
***************************************************************
**  Building the model from raw model
***************************************************************
*)

let add_to_model_if_loc ?kind me model =
  match me.me_location with
  | None -> model
  | Some pos ->
      let filename, line_number, _, _, _ = Loc.get pos in
      let model_file = get_model_file model filename in
      let me = match kind with
        | None -> me
        | Some me_kind -> {me with me_kind}
      in
      let elements = me :: get_elements model_file line_number in
      let elements = elements in
      let model_file = Mint.add line_number elements model_file in
      Mstr.add filename model_file model

let recover_name pm fields_projs raw_name =
  let name, attrs =
    try
      let ls,_loc,attrs = Mstr.find raw_name pm.queried_terms in
      (ls.ls_name.id_string, attrs)
    with Not_found ->
      let id = Mstr.find raw_name fields_projs in
      (id.id_string, id.id_attrs) in
  get_model_trace_string ~name ~attrs


(** [replace_projection const_function mv] replaces record names, projections, and application callees
   in [mv] using [const_function] *)
let rec replace_projection (const_function : string -> string) =
  function v -> v
  (* TODO_WIP *)
  (*
  let const_function s = try const_function s with Not_found -> s in
  function
  | Const _ as v -> v
  | Record fs ->
      let aux (f, mv) = const_function f, replace_projection const_function mv in
      Record (List.map aux fs)
  | Proj (f, mv) ->
      Proj (const_function f, replace_projection const_function mv)
  | Array a -> Array (replace_projection_array const_function a)
  | Apply (s, l) ->
      Apply (const_function s, List.map (replace_projection const_function) l)
  | Var _ | Undefined | Unparsed _ as v -> v
  *)

and replace_projection_array const_function a =
  function a -> a
  (* TODO_WIP *)
  (*
  let for_index a =
    let arr_index_value = replace_projection const_function a.arr_index_value in
    {a with arr_index_value} in
  { arr_others= replace_projection const_function a.arr_others;
    arr_indices= List.map for_index a.arr_indices }
  *)

(* Elements that are of record with only one field in the source code, are
   simplified by eval_match in wp generation. So, this allows to reconstruct
   their value (using the "field" attribute that were added). *)
let read_one_fields ~attrs value =
  attrs, value
  (* TODO_WIP *)
  (*
  let field_names =
    let fields = List.filter_map Ident.extract_field (Sattr.elements attrs) in
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
    *)

let remove_field : (Sattr.t * term -> Sattr.t * term) ref = ref (fun x -> x)
let register_remove_field f = remove_field := f

(** Build the model by replacing projections and restore single field records in the model
   elements, and adding the element at all relevant locations *)
let build_model_rec pm (elts: model_element list) : model_files =
  let fields_projs = fields_projs pm and vc_attrs = pm.Printer.vc_term_attrs in
  let process_me me =
    let attrs = Sattr.union me.me_attrs me.me_lsymbol.ls_name.id_attrs in
    Debug.dprintf debug "@[<h>Term attrs for %s at %a:@ %a@]@."
      (why_name_trans me)
      (Pp.print_option_or_default "NO LOC" Loc.pp_position) me.me_location
      Pretty.print_attrs attrs;
    (* Replace projections with their real name *)
    let me_value = replace_projection
        (fun s -> recover_name pm fields_projs s)
        me.me_value in
    (* Remove some specific record field related to the front-end language.
        This function is registered. *)
    let attrs, me_value = !remove_field (attrs, me_value) in
    Some {
      me_kind= Other;
      me_value;
      me_location= me.me_location;
      me_attrs= attrs;
      me_lsymbol= me.me_lsymbol
    } in
  let add_with_loc_set_kind me loc model =
    if loc = None then model else
      let kind = compute_kind vc_attrs loc me.me_attrs in
      add_to_model_if_loc ~kind {me with me_location= loc} model in
  (* Add a model element at the relevant locations *)
  let add_model_elt model me =
    let kind = compute_kind vc_attrs me.me_location me.me_attrs in
    let model = add_to_model_if_loc ~kind me model in
    let oloc = me.me_lsymbol.ls_name.id_loc in
    let model = add_with_loc_set_kind me oloc model in
    let add_written_loc a =
      add_with_loc_set_kind me (get_written_loc a) in
    Sattr.fold add_written_loc me.me_attrs model in
  List.fold_left add_model_elt Mstr.empty (List.filter_map process_me elts)


(*
***************************************************************
**  Filtering the model
***************************************************************
*)

let add_loc orig_model new_model position =
  (* Add a given location from orig_model to new_model *)
  let file_name, line_num, _, _, _ = Loc.get position in
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

type model_parser = printing_info -> string -> model
type raw_model_parser = printing_info -> string -> model_element list

let debug_elements elts =
  let me_name_trans me = get_name me in
  let print_elements = print_model_elements ~sep:Pp.semi ~print_attrs:true
      ~me_name_trans ~filter_similar:false in
  Debug.dprintf debug "@[<v>Elements:@ %a@]@." print_elements elts;
  elts

let debug_files files =
  let me_name_trans me = get_name me in
  let print_file = print_model_file ~filter_similar:false ~print_attrs:true
      ~me_name_trans in
   Debug.dprintf debug "@[<v>Files:@ %a@]@."
     (Pp.print_list Pp.newline print_file) (Mstr.bindings files);
   files

let model_parser (raw: raw_model_parser) : model_parser =
  fun ({Printer.vc_term_loc; vc_term_attrs} as pm) str ->
  raw pm str |> debug_elements |>
  build_model_rec pm |> debug_files |>
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
