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

(* Concrete syntax for model element values
   (used for pretty printing and JSON printing) *)

type concrete_syntax_bv = string

type concrete_syntax_float =
  | Infinity
  | Plus_zero | Minus_zero
  | NaN
  | Float_number of concrete_syntax_bv * concrete_syntax_bv * concrete_syntax_bv

type concrete_syntax_constant =
  | Boolean of bool
  | String of string
  | Integer of string
  | Real of string
  | Float of concrete_syntax_float
  | BitVector of concrete_syntax_bv
  | Fraction of string * string

type concrete_syntax_quant = Forall | Exists
type concrete_syntax_binop = And | Or | Implies | Iff

type concrete_syntax_term =
  | Var of string
  | Const of concrete_syntax_constant
  | Apply of string * concrete_syntax_term list
  | If of concrete_syntax_term * concrete_syntax_term * concrete_syntax_term
  | Epsilon of string * concrete_syntax_term
  | Quant of concrete_syntax_quant * concrete_syntax_term list * concrete_syntax_term
  | Binop of concrete_syntax_binop * concrete_syntax_term * concrete_syntax_term
  | Not of concrete_syntax_term
  | Function of { is_array: bool; args: string list ; body: concrete_syntax_term }
  | Record of (string * concrete_syntax_term) list

val print_concrete_term : Format.formatter -> concrete_syntax_term -> unit

val concrete_var_from_vs : Term.vsymbol -> concrete_syntax_term
val concrete_const_bool : bool -> concrete_syntax_term
val concrete_apply_from_ls : Term.lsymbol -> concrete_syntax_term list -> concrete_syntax_term
val concrete_equ : string
val concrete_apply_equ : concrete_syntax_term -> concrete_syntax_term -> concrete_syntax_term
val subst_concrete_term :
  concrete_syntax_term Wstdlib.Mstr.t -> concrete_syntax_term -> concrete_syntax_term
val t_and_l_concrete : concrete_syntax_term list -> concrete_syntax_term
  
(** Counter-example model elements. Each element represents
    a counter-example for a single source-code element.*)
type model_element = {
  me_kind             : model_element_kind;
    (** The kind of model element. *)
  me_value            : Term.term;
    (** Counter-example value for the element. *)
  me_concrete_value: concrete_syntax_term;
  me_location         : Loc.position option;
    (** Source-code location of the element. *)
  me_attrs            : Ident.Sattr.t;
    (** Attributes of the element. *)
  me_lsymbol          : Term.lsymbol;
    (** Logical symbol corresponding to the element.  *)
}

val create_model_element :
  value           : Term.term ->
  concrete_value  : concrete_syntax_term ->
  oloc            : Loc.position option ->
  attrs           : Ident.Sattr.t ->
  lsymbol         : Term.lsymbol ->
  model_element
(** Creates a counter-example model element.
    @param value counter-example value for the element

    @param attrs location of the element

    @param attrs attributes of the element

    @param lsymbol logical symbol corresponding to the element
*)

val get_name : model_element -> string

  (** {2 Model definitions} *)

type model

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
(** Counter-example model for JSON format.

    The format is the following:
    - counterexample is JSON object with the following fields
      {ul
      {- "filename": name of the file}
      {- "model": JSON list with elements corresponding to
         counterexample_file}}
    - counterexample_file is JSON object with the following fields
      {ul
      {- "loc": line number}
      {- "is_vc_line": true if the current line corresponds to the source
         code element from which the VC originates (this is useful for
         use cases of Why3 as a library)}
      {- "model_elements": JSON list with elements corresponding to
         counterexample_line}}
    - counterexample_line is JSON list with elements corresponding to
      counterexample_element
    - counterexample_element is JSON object with following fields
      {ul
      {- "name": name of counterexample element}
      {- "value": value of counterexample element}
      {- "attrs": attributes of counterexample element}
      {- "kind": kind of counterexample element:
        {ul
        {- "result": Result of a function call (if the counter-example is
           for postcondition)}
        {- "old": Old value of function argument (if the counter-example is
           for postcondition)}
        {- "\@X": Value at label X}
        {- "before_loop": Value before entering the loop}
        {- "previous_iteration": Value in the previous loop iteration}
        {- "current_iteration": Value in the current loop iteration}
        {- "error_message": The model element represents error message,
            not source-code element.
            The error message is saved in the name of the model element}
        {- "other"}}}}

    Example:
    [{"filename": "records.adb",
      "model": [
        { "loc": "84",,
          "is_vc_line": false
          "model_elements": [
            {
              "name": "A.A",
              "value": "255",
              "attrs": ["model_trace:A.A"]
              "kind": "other"
            },
            {
              "name": "B.B",
              "value": "0",
              "attrs": ["model_trace:B.B"]
              "kind": "other"
            }]
        },
        { "loc": "123",,
          "is_vc_line": true
          "model_elements": [
            {
              "name": "C.C",
              "value": "1",
              "attrs": ["model_trace:C.C"]
              "kind": "result"
            }]
        }
      ]
    }]
*)

val print_model :
  ?filter_similar:bool ->
  ?me_name_trans:(model_element -> string) ->
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
  ?me_name_trans:(model_element -> string) ->
  Format.formatter ->
  model ->
  print_attrs:bool ->
  unit
(** Same as print_model but is intended to be human readable.*)

val interleave_with_source :
  print_attrs:bool ->
  ?start_comment:string ->
  ?end_comment:string ->
  ?me_name_trans:(model_element -> string) ->
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

type model_parser = Printer.printing_info -> string -> model
(** Parses the input string into model elements, estabilishes a mapping between these
   elements and mapping from printer and builds model data structure. The model still has
   to be cleaned using [clean]. *)

type raw_model_parser = Printer.printing_info -> string -> model_element list

val register_remove_field:
  ( Ident.Sattr.t * Term.term * concrete_syntax_term ->
    Ident.Sattr.t * Term.term * concrete_syntax_term ) ->
  unit

val register_model_parser : desc:Pp.formatted -> string -> raw_model_parser -> unit

val lookup_model_parser : string -> model_parser

val list_model_parsers : unit -> (string * Pp.formatted) list
