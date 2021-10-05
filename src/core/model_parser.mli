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

(** {1 Counter-example model values} *)

type model_int = { int_value: BigInt.t; int_verbatim: string }

type model_dec = { dec_int: BigInt.t; dec_frac: BigInt.t; dec_verbatim: string }

type model_frac = { frac_nom: BigInt.t; frac_den: BigInt.t; frac_verbatim: string }

type model_bv = { bv_value: BigInt.t; bv_length: int; bv_verbatim: string }

type model_float_binary = { sign: model_bv; exp: model_bv; mant: model_bv }

type model_float =
  | Plus_infinity | Minus_infinity | Plus_zero | Minus_zero | Not_a_number
  | Float_number of {hex: string option (* e.g., 0x1.ffp99 *); binary: model_float_binary}

type model_const =
  | Boolean of bool
  | String of string
  | Integer of model_int
  | Float of model_float
  | Bitvector of model_bv
  | Decimal of model_dec
  | Fraction of model_frac

type model_value =
  | Const of model_const
  | Array of model_array
  | Record of model_record
  | Proj of model_proj
  | Apply of string * model_value list
  | Var of string
  | Undefined
  | Unparsed of string

and arr_index = {arr_index_key: model_value; arr_index_value: model_value}

and model_array = {arr_others: model_value; arr_indices: arr_index list}

and model_record = (field_name * model_value) list

and model_proj = proj_name * model_value

and proj_name = string

and field_name = string

val compare_model_value_const : model_value -> model_value -> int

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
    @param array the array to that the element will be added

    @param index the index on which the element will be added.

    @param value the value of the element to be added
*)

val float_of_binary : model_float_binary -> model_float

val print_model_value : Format.formatter -> model_value -> unit
val print_model_value_human : Format.formatter -> model_value -> unit

val print_model_const_human : Format.formatter -> model_const -> unit

val debug_force_binary_floats : Debug.flag
(** Print all floats using bitvectors in JSON output for models *)

(*
***************************************************************
**  Model elements
***************************************************************
*)

type model_element_kind =
  | Result
  (** Result of a function call (if the counter-example is for postcondition) *)
  | Call_result of Loc.position
  (** Result of the function call at the given location *)
  | Old
  (** Old value of function argument (if the counter-example is for
      postcondition) *)
  | At of string
  (** Value at label *)
  | Loop_before
  (** Value from before the loop *)
  | Loop_previous_iteration
  (** Value from before current loop iteration *)
  | Loop_current_iteration
  (** Value from current loop iteration *)
  | Error_message
  (** The model element represents error message, not source-code element. The
     error message is saved in the name of the model element.*)
  | Other

val print_model_kind : Format.formatter -> model_element_kind -> unit

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
  model_element
(** Creates a counter-example model element.
    @param name the name of the source-code element

    @param value counter-example value for the element

    @param location source-code location of the element

    @param term why term corresponding to the element
*)

  (** {2 Model definitions} *)

type model

val map_filter_model_elements :
  (model_element -> model_element option) -> model -> model

val is_model_empty : model -> bool
val empty_model : model
val set_model_files : model -> model_element list Wstdlib.Mint.t Wstdlib.Mstr.t -> model

(** {2 Querying the model} *)

val get_model_elements : model -> model_element list
val get_model_term_loc : model -> Loc.position option
val get_model_term_attrs : model -> Ident.Sattr.t

(** {2 Search model elements} *)

val search_model_element_for_id :
  model -> ?loc:Loc.position -> Ident.ident -> model_element option
(** [search_model_element_for_id m ?loc id] searches for a model element for
    identifier [id], at the location [id.id_loc], or at [loc], when given. *)

val search_model_element_call_result :
  model -> int option -> Loc.position -> model_element option
(** [search_model_element_call_result m oid loc] searches for a model element
   that holds the return value for a call with id [oid] at location [loc]. *)

(** {2 Printing the model} *)

val json_model : model -> Json_base.json

val print_model :
  ?filter_similar:bool ->
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
    @param print_attrs when set to true, the name is printed together with the
    attrs associated to the specific ident.
*)

val print_model_human :
  ?filter_similar:bool ->
  ?me_name_trans:(model_element_name -> string) ->
  Format.formatter ->
  model ->
  print_attrs:bool ->
  unit
(** Same as print_model but is intended to be human readable.*)

val print_model_json : Format.formatter -> model -> unit
(** Prints counter-example model to json format.

    The format is the following:
    - counterexample is JSON object with fields indexed by names of files
      storing values of counterexample_file
    - counterexample_file is JSON object with fields indexed by line numbers
      storing values of counterexample_line
    - counterexample_line is JSON array (ordered list) with elements
      corresponding to counterexample_element
    - counterexample_element is JSON object with following fields
      {ul
      {- "name": name of counterexample element}
      {- "value": value of counterexample element}
      {- "kind": kind of counterexample element:
        {ul
        {- "result": Result of a function call (if the counter-example is for postcondition)}
        {- "old": Old value of function argument (if the counter-example is for postcondition)}
        {- "\@X": Value at label X}
        {- "before_loop": Value before entering the loop}
        {- "previous_iteration": Value in the previous loop iteration}
        {- "current_iteration": Value in the current loop iteration}
        {- "error_message": The model element represents error message, not source-code element.
            The error message is saved in the name of the model element}
        {- "other"}}}}

    Example:
    {[
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
    ]}
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
**  Cleaning the model
***************************************************************
*)

(** Method clean#model cleans a model from unparsed values and handles
   contradictory VCs ("the check fails with all inputs"). *)
class clean : object
  method model : model -> model
  method element : model_element -> model_element option
  method value : model_value -> model_value option
  method const : model_const -> model_value option
  method integer : model_int -> model_value option
  method string : string -> model_value option
  method decimal : model_dec -> model_value option
  method fraction : model_frac -> model_value option
  method float : model_float -> model_value option
  method boolean : bool -> model_value option
  method bitvector : model_bv -> model_value option
  method var : string -> model_value option
  method proj : string -> model_value -> model_value option
  method apply : string -> model_value list -> model_value option
  method array : model_array -> model_value option
  method record : model_record -> model_value option
  method undefined : model_value option
  method unparsed : string -> model_value option
end

val customize_clean : #clean -> unit
(** Customize the class used to clean the values in the model. *)

(*
***************************************************************
** Registering model parser
***************************************************************
*)

type model_parser = Printer.printer_mapping -> string -> model
(** Parses the input string into model elements, estabilishes a mapping between these
   elements and mapping from printer and builds model data structure. The model still has
   to be cleaned using [clean]. *)

type raw_model_parser = Printer.printer_mapping -> string -> model_element list

val register_remove_field:
  (Ident.Sattr.t * model_value -> Ident.Sattr.t * model_value) -> unit

val register_model_parser : desc:Pp.formatted -> string -> raw_model_parser -> unit

val lookup_model_parser : string -> model_parser

val list_model_parsers : unit -> (string * Pp.formatted) list
