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
 | Unparsed of string
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

type model_element_type =
| Result
  (* Result of a function call (if the counter-example is for postcondition)  *)
| Old
  (* Old value of function argument (if the counter-example is for postcondition)  *)
| Other


(** Counter-example model elements. Each element represents
    a counter-example for a single source-code element.*)
type model_element = {
  me_name     : string;
    (** The name of the source-code element.  *)
  me_type     : model_element_type;
    (** The type of model element. *)
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

val print_model :
  ?me_name_trans:((string * model_element_type) -> string) ->
  Format.formatter ->
  model ->
  unit
(** Prints the counter-example model

    @param me_name_trans the transformation of the model elements
      names. The input is a pair consisting of the name of model
      element and type of the model element. The output is the
      name of the model element that should be displayed.
    @param model the counter-example model to print
*)

val model_to_string :
  ?me_name_trans:((string * model_element_type) -> string) ->
  model ->
  string
(** See print_model  *)

val print_model_json :
  ?me_name_trans:((string * model_element_type) -> string) ->
  Format.formatter ->
  model:model ->
  unit
(** Prints counter-example model to json format.

    @param me_name_trans see print_model
    @model the counter-example model to print.
*)

val model_to_string_json :
  ?me_name_trans:((string * model_element_type) -> string) ->
  model ->
  string
(** See print_model_json *)

val interleave_with_source :
  ?start_comment:string ->
  ?end_comment:string ->
  ?me_name_trans:((string * model_element_type) -> string) ->
  model ->
  filename:string ->
  source_code:string ->
  string
(** Given a source code and a counter-example model interleaves
    the source code with information in about the counter-example.
    That is, for each location in counter-example trace creates
    a comment in the output source code with information about
    values of counter-example model elements.

    @param start_comment the string that starts a comment
    @param end_comment the string that ends a comment
    @param me_name_trans see print_model
    @param model counter-example model
    @param filename the file name of the source
    @param source_code the input source code

    @return the source code with added comments with information
    about counter-example model
*)

(*
***************************************************************
**  Filtering the model
***************************************************************
*)
val model_for_positions_and_decls : model ->
  positions: Loc.position list -> model
(** Given a model and a list of source-code positions returns model
    that contains only elements from the input model that are on these
    positions plus for every file in the model, elements that are
    in the positions of function declarations. Elements with other
    positions are filtered out.

    Assumes that for each file the element on the first line of the model
    has position of function declaration.

    Only filename and line number is used to identify positions.
*)

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
