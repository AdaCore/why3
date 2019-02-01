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

val interp_float: ?interp:bool -> string -> string -> string -> float_type

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
  arr_index_key : string;
  arr_index_value : model_value;
}
and model_array = {
  arr_others  : model_value;
  arr_indices : arr_index list;
}
and model_proj = (proj_name * model_value)
and proj_name = string
and model_record = (field_name * model_value) list
and field_name = string

val array_create_constant :
  value : model_value ->
  model_array
(** Creates constant array with all indices equal to the parameter value. *)

val array_add_element :
  array : model_array ->
  index : string      ->
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

type model_element_kind =
| Result
  (* Result of a function call (if the counter-example is for postcondition)  *)
| Old
  (* Old value of function argument (if the counter-example is for postcondition) *)
| Error_message
  (* The model element represents error message, not source-code element.
     The error message is saved in the name of the model element.*)
| Other

(** Information about the name of the model element *)
type model_element_name = {
  men_name   : string;
    (** The name of the source-code element.  *)
  men_kind   : model_element_kind;
    (** The kind of model element. *)
  men_attrs : Ident.Sattr.t;
}

(** Counter-example model elements. Each element represents
    a counter-example for a single source-code element.*)
type model_element = {
  me_name       : model_element_name;
    (** Information about the name of the model element  *)
  me_value      : model_value;
    (** Counter-example value for the element. *)
  me_location   : Loc.position option;
    (** Source-code location of the element. *)
  me_term       : Term.term option;
    (** Why term corresponding to the element.  *)
}

val create_model_element :
  name      : string ->
  value     : model_value ->
  attrs     : Ident.Sattr.t ->
  ?location : Loc.position ->
  ?term     : Term.term ->
  unit ->
  model_element
(** Creates a counter-example model element.
    @param name : the name of the source-code element

    @param value  : counter-example value for the element

    @param location : source-code location of the element

    @param term : why term corresponding to the element
*)

(*
***************************************************************
**  Model definitions
***************************************************************
*)
type model

val is_model_empty : model -> bool
val default_model : model

(*
***************************************************************
**  Quering the model
***************************************************************
*)

val print_model :
  ?me_name_trans:(model_element_name -> string) ->
  print_attrs:bool ->
  Format.formatter ->
  model ->
  unit
(** Prints the counter-example model

    @param me_name_trans the transformation of the model elements
      names. The input is information about model element name. The
      output is the name of the model element that should be displayed.
    @param model the counter-example model to print
    @param print_attrs: when set to true, the name is printed together with the
    attrs associated to the specific ident.
*)

val print_model_human :
  ?me_name_trans:(model_element_name -> string) ->
  Format.formatter ->
  model ->
  print_attrs:bool ->
  unit
(** Same as print_model but is intended to be human readable.

*)

val print_model_json :
  ?me_name_trans:(model_element_name -> string) ->
  ?vc_line_trans:(int -> string) ->
  Format.formatter ->
  model ->
  unit
(** Prints counter-example model to json format.

    @param me_name_trans see print_model
    @param vc_line_trans the transformation from the line number corresponding
      to the term that triggers VC before splitting VC to the name of JSON field
      storing counterexample information related to this term. By default, this
      information is stored in JSON field corresponding to this line, i.e.,
      the transformation is string_of_int.
      Note that the exact line of the construct that triggers VC may not be
      known. This can happen if the term that triggers VC spans multiple lines
      and it is splitted.
      This transformation can be used to store the counterexample information
      related to this term in dedicated JSON field.
    @param model the counter-example model to print.
    @param print_attrs if set to true, add attrs associated to the name id to
      the counterexample output

    The format is the following:
    - counterexample is JSON object with fields indexed by names of files
      storing values of counterexample_file
    - counterexample_file is JSON object with fields indexed by line numbers
      storing values of counterexample_line
    - counterexample_line is JSON array (ordered list) with elements
      corresponding to counterexample_element
    - counterexample_element is JSON object with following fields
      - "name": name of counterexample element
      - "value": value of counterexample element
      - "kind": kind of counterexample element:
        - "result": Result of a function call (if the counter-example is for postcondition)
        - "old": Old value of function argument (if the counter-example is for postcondition)
        - "error_message": The model element represents error message, not source-code element.
            The error message is saved in the name of the model element
        - "other"

    Example:
    {
      "records.adb": {
          "84": [
            {
              "name": "A.A",
              "value": "255",
              "kind": "other"
            },
            {
              "name": "B.B",
              "value": "0",
              "kind": "other"
            }
          ]
      }
    }
*)

val interleave_with_source :
  print_attrs:bool ->
  ?start_comment:string ->
  ?end_comment:string ->
  ?me_name_trans:(model_element_name -> string) ->
  model ->
  rel_filename:string ->
  source_code:string ->
  locations:(Loc.position * 'a) list ->
  string * (Loc.position * 'a) list
(** Given a source code and a counter-example model interleaves
    the source code with information in about the counter-example.
    That is, for each location in counter-example trace creates
    a comment in the output source code with information about
    values of counter-example model elements.

    @param start_comment the string that starts a comment
    @param end_comment the string that ends a comment
    @param me_name_trans see print_model
    @param model counter-example model
    @param rel_filename the file name of the source relative to the session
    @param source_code the input source code
    @param locations the source locations that are found in the code

    @return the source code with added comments with information
    about counter-example model. The second part of the pair are
    locations modified so that it takes into account that counterexamples
    were added.
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

type raw_model_parser =
  Ident.ident Wstdlib.Mstr.t -> Ident.ident Wstdlib.Mstr.t -> ((string * string) list) Wstdlib.Mstr.t ->
    string list -> Ident.Sattr.t Wstdlib.Mstr.t -> string -> model_element list
(** Parses the input string into model elements.
    [raw_model_parser: proj->record_map->noarg_cons->s->mel]
    [proj]: is the list of projections
    [list_field]: is the list of field function definition
    [record_map]: is a map associating the name of printed projections to the
      fields (couple of printed field and model_trace name).
    [noarg_cons]: List of constructors with no arguments (collected to avoid
      confusion between variable and constructors)
    [s]: model
    [mel]: collected model
 *)

val register_remove_field:
  (Ident.Sattr.t * model_value -> Ident.Sattr.t * model_value) -> unit

val register_model_parser : desc:Pp.formatted -> string -> raw_model_parser -> unit

val lookup_model_parser : string -> model_parser

val list_model_parsers : unit -> (string * Pp.formatted) list
