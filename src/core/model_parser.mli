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

(*
*************************************************************** 
**  Counter-example model values
****************************************************************
*)
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

val array_create_constant : 
  value : model_value -> 
  model_array
(** Creates constant array with all indices equal to the parameter value. *)

val array_add_element : 
  array : model_array -> 
  index : model_value -> 
  value : model_value -> 
  model_array
(** Adds an element to the array. 
    @param array : the array to that the element will be added
    
    @param index : the index on which the element will be added.
    Note that the index must be of value model_value.Integer

    @param value : the value of the element to be added
*)

val print_model_value : Format.formatter -> model_value -> unit


(*
*************************************************************** 
**  Model elements
***************************************************************
*)
(** Counter-example model elements. Each element represents
    a counter-example for a single source-code element.*)
type model_element = { 
  me_name     : string;
    (** The name of the source-code element.  *)
  me_value    : model_value;
    (** Counter-example value for the element. *)
  me_location : Loc.position option;
    (** Source-code location of the element. *)
  me_term     : Term.term option;
    (** Why term corresponding to the element.  *)
}

val create_model_element : 
  name     : string -> 
  value    : model_value -> 
  ?location : Loc.position -> 
  ?term     : Term.term ->
  unit ->
  model_element
(** Creates a counter-example model element. 
    @param name : the name of the source-code element

    @param value  : counter-example value for the element

    @param location : source-code location of the element 
    
    @param term : why term corresponding to the element *)

(*
*************************************************************** 
**  Model definitions
***************************************************************
*)   
type model 

val empty_model : model

(*
*************************************************************** 
**  Quering the model
***************************************************************
*)

val print_model : Format.formatter -> model -> unit

val model_to_string : model -> string

val interleave_with_source : model -> string -> string -> string

(*
*************************************************************** 
** Registering model parser
***************************************************************
*)
type model_parser =  string -> Printer.printer_mapping -> model
(** Parses the input string into model elements, estabilishes 
    a mapping between these elements and mapping from printer 
    and builds model data structure.
*)

type raw_model_parser =  string -> model_element list
(** Parses the input string into model elements. *)

val register_model_parser : desc:Pp.formatted -> string -> raw_model_parser -> unit

val lookup_model_parser : string -> model_parser

val list_model_parsers : unit -> (string * Pp.formatted) list
