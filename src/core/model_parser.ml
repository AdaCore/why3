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

type model_value =
 | Integer of string
 | Array of model_array
 | Other of string
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

let rec print_indices fmt indices =
  match indices with
  | [] -> ()
  | index::tail ->
    fprintf fmt "; %d -> " index.arr_index_key;
    print_model_value fmt index.arr_index_value;
    print_indices fmt tail
and
print_array fmt arr = 
  fprintf fmt "{others -> ";
  print_model_value fmt arr.arr_others;
  print_indices fmt arr.arr_indices;
  fprintf fmt "}"
and
print_model_value fmt value =
  (* Prints model value. *)
  match value with
  | Integer s -> fprintf fmt "%s" s  
  | Other s -> fprintf fmt "%s" s
  | Array a -> print_array fmt a

type model_element = { 
  me_name     : string;
  me_value    : model_value;
  me_location : Loc.position option; 
}

let create_model_element ~name ~value ~location =
  {
    me_name = name;
    me_value = value;
    me_location = location;
  }

let print_location fmt m_element =
    match m_element.me_location with
    | None -> fprintf fmt "\"no location\""
    | Some loc -> Loc.report_position fmt loc
      
let rec print_model fmt model =
  match model with
  | [] -> ()
  | m_element::t -> begin
    fprintf fmt  "%s at %a = %a\n" 
      m_element.me_name print_location m_element print_model_value m_element.me_value;
    print_model fmt t
  end

let model_to_string model =
  print_model str_formatter model;
  flush_str_formatter ()

type model_parser =  string -> Printer.printer_mapping -> model_element list

type reg_model_parser = Pp.formatted * model_parser

let model_parsers : reg_model_parser Hstr.t = Hstr.create 17

exception KnownModelParser of string
exception UnknownModelParser of string

let register_model_parser ~desc s p =
  if Hstr.mem model_parsers s then raise (KnownModelParser s);
  Hstr.replace model_parsers s (desc, p)

let lookup_model_parser s =
  try snd (Hstr.find model_parsers s)
  with Not_found -> raise (UnknownModelParser s)

let list_model_parsers () =
  Hstr.fold (fun k (desc,_) acc -> (k,desc)::acc) model_parsers []

let () = register_model_parser
  ~desc:"Model@ parser@ with@ no@ output@ (used@ if@ the@ solver@ does@ not@ support@ models." "no_model"
  (fun _ _ -> [])
