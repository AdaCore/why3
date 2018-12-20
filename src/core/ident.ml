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

(** Attributes *)

type attribute = {
  attr_string : string;
  attr_tag    : int;
}

module Attr = MakeMSH (struct
  type t = attribute
  let tag a = a.attr_tag
end)

module Sattr = Attr.S
module Mattr = Attr.M

module Hsattr = Hashcons.Make (struct
  type t = attribute
  let equal a1 a2 = a1.attr_string = a2.attr_string
  let hash a = Hashtbl.hash a.attr_string
  let tag n a = { a with attr_tag = n }
end)

let create_attribute s = Hsattr.hashcons {
  attr_string = s;
  attr_tag    = -1
}

let list_attributes () =
  let acc = ref [] in
  Hsattr.iter (fun a -> acc := a.attr_string :: !acc);
  !acc

let attr_equal : attribute -> attribute -> bool = (==)
let attr_hash a = a.attr_tag
let attr_compare a1 a2 = Pervasives.compare a1.attr_tag a2.attr_tag

(** Naming convention *)

type notation =
  | SNword   of string  (* plus *)
  | SNinfix  of string  (* + *)
  | SNtight  of string  (* ! *)
  | SNprefix of string  (* -_ *)
  | SNget    of string  (* [] *)
  | SNset    of string  (* []<- *)
  | SNupdate of string  (* [<-] *)
  | SNcut    of string  (* [..] *)
  | SNlcut   of string  (* [.._] *)
  | SNrcut   of string  (* [_..] *)

(* current encoding *)

let op_infix  s = "infix " ^ s
let op_prefix s = "prefix " ^ s
let op_get    s = "mixfix []" ^ s
let op_set    s = "mixfix []<-" ^ s
let op_update s = "mixfix [<-]" ^ s
let op_cut    s = "mixfix [..]" ^ s
let op_lcut   s = "mixfix [.._]" ^ s
let op_rcut   s = "mixfix [_..]" ^ s

let op_equ   = op_infix "="
let op_neq   = op_infix "<>"
let op_tight = op_prefix

let print_sn fmt w =
  let lspace p = if p.[0] = '*' then " " else "" in
  let rspace p = if p.[String.length p - 1] = '*' then " " else "" in
  match w with (* infix/prefix never empty, mixfix cannot have stars *)
  | SNinfix  p -> Format.fprintf fmt "(%s%s%s)" (lspace p) p (rspace p)
  | SNtight  p -> Format.fprintf fmt "(%s%s)" p (rspace p)
  | SNprefix p -> Format.fprintf fmt "(%s%s_)" (lspace p) p
  | SNget    p -> Format.fprintf fmt "([]%s)" p
  | SNset    p -> Format.fprintf fmt "([]%s<-)" p
  | SNupdate p -> Format.fprintf fmt "([<-]%s)" p
  | SNcut    p -> Format.fprintf fmt "([..]%s)" p
  | SNlcut   p -> Format.fprintf fmt "([.._]%s)" p
  | SNrcut   p -> Format.fprintf fmt "([_..]%s)" p
  | SNword   p -> Format.pp_print_string fmt p

(* The function below recognizes the following strings as notations:
      "infix " (opchar+ [']* as p) (['_] [^'_] .* as q)
      "prefix " (opchar+ [']* as p) (['_] [^'_] .* as q)
      "mixfix " .* "]" opchar* ([']* as p) (['_] [^'_] .* as q)
   It will fail if you add a mixfix that contains a non-opchar after
   the closing square bracket, or a mixfix that does not use brackets.
   Be careful when working with this code, it may eat your brain. *)

let sn_decode s =
  let len = String.length s in
  if len <= 6 then SNword s else
  if s.[5] <> ' ' && s.[6] <> ' ' then SNword s else
  let k = match String.sub s 0 6 with
    | "infix " -> 6
    | "prefix" -> 7
    | "mixfix" -> (try succ (String.index_from s 7 ']') with Not_found -> 0)
    | _ -> 0 in
  if k = 0 then SNword s else
  let rec skip_opchar i =
    if i = len then i else match s.[i] with
      | '@' | '!' | '^' | '$' | '=' | '%' | '>' | '#'
      | '.' | '<' | '-' | '&' | '/' | '+' | '?' | ':'
      | '*' | '~' | '|' | '\\' -> skip_opchar (succ i)
      | _ -> i in
  let l = skip_opchar k in
  let rec skip_quote i =
    if i = len then i else
    if s.[i] = '\'' then skip_quote (succ i) else
    if i = l || s.[i] = '_' then i else pred i in
  let m = skip_quote l in
  let prefix o =
    if o.[0] <> '!' && o.[0] <> '?' then SNprefix o
    else try for i = 1 to l - 8 do match o.[i] with
      | '!' | '$' | '&' | '?' | '@'
      | '^' | '.' | ':' | '|' | '#' -> ()
      | _ -> raise Exit done; SNtight o
    with Exit -> SNprefix o in
  if l = k && k < 8 then SNword s (* null infix/prefix *) else
  let w = if k = 6 then SNinfix (String.sub s 6 (m - 6)) else
          if k = 7 then prefix (String.sub s 7 (m - 7)) else
          let p = if l < m then String.sub s l (m - l) else "" in
          match String.sub s 8 (l - 8) with
          | "]"   -> SNget p | "]<-"  -> SNset p  | "<-]"  -> SNupdate p
          | "..]" -> SNcut p | ".._]" -> SNlcut p | "_..]" -> SNrcut p
          | _ -> SNword (if m = len then s else String.sub s 0 m) in
  if m = len then w (* no appended suffix *) else
  if s.[m] <> '\'' && s.[m] <> '_' then SNword s else
  let p = print_sn Format.str_formatter w;
          Format.flush_str_formatter () in
  SNword (p ^ String.sub s m (len - m))

let print_decoded fmt s = print_sn fmt (sn_decode s)

(** Identifiers *)

type ident = {
  id_string : string;               (* non-unique name *)
  id_attrs  : Sattr.t;              (* identifier attributes *)
  id_loc    : Loc.position option;  (* optional location *)
  id_tag    : Weakhtbl.tag;         (* unique magical tag *)
}

module Id = MakeMSHW (struct
  type t = ident
  let tag id = id.id_tag
end)

module Sid = Id.S
module Mid = Id.M
module Hid = Id.H
module Wid = Id.W

type preid = {
  pre_name  : string;
  pre_attrs : Sattr.t;
  pre_loc   : Loc.position option;
}

let id_equal : ident -> ident -> bool = (==)
let id_hash id = Weakhtbl.tag_hash id.id_tag
let id_compare id1 id2 = Pervasives.compare (id_hash id1) (id_hash id2)

(* constructors *)

let id_register = let r = ref 0 in fun id -> {
  id_string = id.pre_name;
  id_attrs  = id.pre_attrs;
  id_loc    = id.pre_loc;
  id_tag    = (incr r; Weakhtbl.create_tag !r);
}

let create_ident name attrs loc = {
  pre_name  = name;
  pre_attrs = attrs;
  pre_loc   = loc;
}

let id_fresh ?(attrs = Sattr.empty) ?loc nm =
  create_ident nm attrs loc

let id_user ?(attrs = Sattr.empty) nm loc =
  create_ident nm attrs (Some loc)

let id_attr id attrs =
  create_ident id.id_string attrs id.id_loc

let id_clone ?(attrs = Sattr.empty) id =
  let aa = Sattr.union attrs id.id_attrs in
  create_ident id.id_string aa id.id_loc

let id_derive ?(attrs = Sattr.empty) nm id =
  let aa = Sattr.union attrs id.id_attrs in
  create_ident nm aa id.id_loc

let preid_name id = id.pre_name

(** Unique names for pretty printing *)

type ident_printer = {
  indices   : int Hstr.t;
  values    : string Hid.t;
  sanitizer : string -> string;
  blacklist : string list;
}

(* name is already sanitized *)
let find_unique indices name =
  let specname ind =
    (* If the symbol is infix/prefix *and* the name has not been
       sanitized for provers, we don't want to disambiguate with
       a number but with a quote symbol: "+" becomes "+'" "+''" etc.
       This allows to parse the ident again (for transformations). *)
    if ind <= 0 then name else
    match sn_decode name with
    | SNword _ -> name ^ string_of_int ind
    | _        -> name ^ String.make ind '\'' in
  let testname ind = Hstr.mem indices (specname ind) in
  let rec advance ind =
    if testname ind then advance (succ ind) else ind in
  let rec retreat ind =
    if ind = 1 || testname (pred ind) then ind else retreat (pred ind) in
  let fetch ind =
    if testname ind then advance (succ ind) else retreat ind in
  let name = try
    let ind = fetch (succ (Hstr.find indices name)) in
    Hstr.replace indices name ind;
    specname ind
  with Not_found -> name in
  Hstr.replace indices name 0;
  name

let reserve indices name = ignore (find_unique indices name)

let same x = x

let create_ident_printer ?(sanitizer = same) sl =
  let indices = Hstr.create 1997 in
  List.iter (reserve indices) sl;
  { indices   = indices;
    values    = Hid.create 1997;
    sanitizer = sanitizer;
    blacklist = sl }

let duplicate_ident_printer id_printer =
  {id_printer with
   indices = Hstr.copy id_printer.indices;
   values  = Hid.copy id_printer.values;
  }

let known_id printer id =
  try
    (let _ = Hid.find printer.values id in true)
  with Not_found ->
    false

let id_unique printer ?(sanitizer = same) id =
  try
    Hid.find printer.values id
  with Not_found ->
    let name = sanitizer (printer.sanitizer id.id_string) in
    let name = find_unique printer.indices name in
    Hid.replace printer.values id name;
    name

let string_unique printer s = find_unique printer.indices s

let forget_id printer id =
  try
    let name = Hid.find printer.values id in
    Hstr.remove printer.indices name;
    Hid.remove printer.values id
  with Not_found -> ()

let forget_all printer =
  Hid.clear printer.values;
  Hstr.clear printer.indices;
  List.iter (reserve printer.indices) printer.blacklist

(** Sanitizers *)

let char_to_alpha c = match c with
  | 'a'..'z' | 'A'..'Z' -> String.make 1 c
  | ' ' -> "sp" | '_'  -> "us" | '#' -> "sh"
  | '`' -> "bq" | '~'  -> "tl" | '!' -> "ex"
  | '@' -> "at" | '$'  -> "dl" | '%' -> "pc"
  | '^' -> "cf" | '&'  -> "et" | '*' -> "as"
  | '(' -> "lp" | ')'  -> "rp" | '-' -> "mn"
  | '+' -> "pl" | '='  -> "eq" | '[' -> "lb"
  | ']' -> "rb" | '{'  -> "lc" | '}' -> "rc"
  | ':' -> "cl" | '\'' -> "qt" | '"' -> "dq"
  | '<' -> "ls" | '>'  -> "gt" | '/' -> "sl"
  | '?' -> "qu" | '\\' -> "bs" | '|' -> "br"
  | ';' -> "sc" | ','  -> "cm" | '.' -> "dt"
  | '0' -> "zr" | '1'  -> "un" | '2' -> "du"
  | '3' -> "tr" | '4'  -> "qr" | '5' -> "qn"
  | '6' -> "sx" | '7'  -> "st" | '8' -> "oc"
  | '9' -> "nn" | '\n' -> "nl" |  _  -> "zz"

let char_to_lalpha c = Strings.uncapitalize (char_to_alpha c)
let char_to_ualpha c = Strings.capitalize (char_to_alpha c)

let char_to_alnum c =
  match c with '0'..'9' -> String.make 1 c | _ -> char_to_alpha c

let char_to_lalnum c =
  match c with '0'..'9' -> String.make 1 c | _ -> char_to_lalpha c

let char_to_alnumus c =
  match c with '_' | ' ' -> "_" | _ -> char_to_alnum c

let char_to_lalnumus c =
  match c with '_' | ' ' -> "_" | _ -> char_to_lalnum c

let sanitizer' head rest last n =
  let lst = ref [] in
  let n = if n = "" then "zilch" else n in
  let len = String.length n in
  let code i c = lst :=
    (if i = 0 then head
     else if i = len - 1 then last
     else rest) c :: !lst in
  String.iteri code n;
  String.concat "" (List.rev !lst)

let sanitizer head rest n = sanitizer' head rest rest n

(** {2 functions for working with counterexample attributes} *)

let proxy_attr = create_attribute "mlw:proxy_symbol"

let model_projected_attr = create_attribute "model_projected"
let model_vc_post_attr = create_attribute "model_vc_post"

let create_model_trace_attr s = create_attribute ("model_trace:" ^ s)

let is_model_trace_attr a =
  Strings.has_prefix "model_trace:" a.attr_string

let is_written_attr a =
  Strings.has_prefix "vc:written:" a.attr_string

let create_written_attr loc =
  let f,l,b,e = Loc.get loc in
  let s = Format.sprintf "vc:written:%i:%i:%i:%s" l b e f in
  create_attribute s

let extract_written_loc attr =
  let spl = Strings.bounded_split ':' attr.attr_string 6 in
  match spl with
  | "vc" :: "written" :: line :: col_st :: col_end :: file :: [] ->
      begin try
          let line = int_of_string line in
          let col_st = int_of_string col_st in
          let col_end = int_of_string col_end in
          Some (Loc.user_position file line col_st col_end)
        with _ -> None
      end
  | _ -> None

let is_counterexample_attr a =
  is_model_trace_attr a || attr_equal a model_projected_attr ||
  is_written_attr a

let has_a_model_attr id =
  Sattr.exists is_counterexample_attr id.id_attrs

let relevant_for_counterexample id =
  (id.id_loc <> None && not (Sattr.mem proxy_attr id.id_attrs))
  || has_a_model_attr id

let remove_model_attrs ~attrs =
  Sattr.filter (fun l -> not (is_counterexample_attr l)) attrs

let get_model_trace_attr ~attrs =
  Sattr.choose (Sattr.filter is_model_trace_attr attrs)

let transform_model_trace_attr attrs trans_fun =
  try
    let trace_attr = get_model_trace_attr ~attrs in
    let attrs_without_trace = Sattr.remove trace_attr attrs in
    let new_trace_attr = create_attribute (trans_fun trace_attr.attr_string) in
    Sattr.add new_trace_attr attrs_without_trace
  with Not_found -> attrs

let append_to_model_element_name ~attrs ~to_append =
  let trans attr_str =
    let splitted = Strings.bounded_split '@' attr_str 2 in
    match splitted with
    | [before; after] -> before ^ to_append ^ "@" ^ after
    | _ -> attr_str^to_append
  in
  transform_model_trace_attr attrs trans

let append_to_model_trace_attr ~attrs ~to_append =
    let trans attr_str = attr_str ^ to_append in
    transform_model_trace_attr attrs trans

let get_model_element_name ~attrs =
  let trace_attr = get_model_trace_attr ~attrs in
  let splitted1 = Strings.bounded_split ':' trace_attr.attr_string 2 in
  match splitted1 with
  | [_; content] ->
    begin
      let splitted2 = Strings.bounded_split '@' content 2 in
      match splitted2 with
      | [el_name; _] -> el_name
      | [el_name] -> el_name
      | _ -> raise Not_found
    end;
  | [_] -> ""
  | _ -> assert false

let get_model_trace_string ~name ~attrs =
  match get_model_trace_attr ~attrs with
  | exception Not_found -> name
  | tl ->
      let splitted = Strings.bounded_split ':' tl.attr_string 2 in
      match splitted with
      | [_; t_str] -> t_str
      | _ -> ""

let compute_model_trace_field pj d =
  match pj with
  | None -> Sattr.empty
  | Some pj ->
      let name = get_model_trace_string
          ~name:pj.id_string ~attrs:pj.id_attrs in
      let name = if name = "" then pj.id_string else name in
      let attr = "field:" ^ (string_of_int d) ^ ":" ^ name in
      Sattr.singleton (create_attribute attr)

let extract_field attr =
  try
    match Strings.bounded_split ':' attr.attr_string 3 with
    | "field" :: n :: [field_name] -> Some (int_of_string n, field_name)
    | _ -> None
  with
  | _ -> None

(* Functions for working with ITP attributes *)

let is_name_attr a =
  Strings.has_prefix "name:" a.attr_string

let get_name_attr ~attrs =
  try Some (Sattr.choose (Sattr.filter is_name_attr attrs))
  with Not_found -> None

let get_element_name ~attrs =
  match get_name_attr ~attrs with
  | None -> None
  | Some name_attr ->
    let splitted1 = Strings.bounded_split ':' name_attr.attr_string 2 in
    let correct_word = Str.regexp "^\\([A-Za-z]+\\)\\([A-Za-z0-9_']*\\)$" in
    match splitted1 with
    | ["name"; content] when Str.string_match correct_word content 0 ->
        Some content
    | _ -> None

let id_unique_attr printer ?(sanitizer = same) id =
  try
    Hid.find printer.values id
  with Not_found ->
    let attrs = id.id_attrs in
    let name =
      match (get_element_name ~attrs) with
      | Some x -> x
      | None -> printer.sanitizer id.id_string
    in
    let name = sanitizer name in
    let name = find_unique printer.indices name in
    Hid.replace printer.values id name;
    name
