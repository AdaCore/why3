(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** {2 Model} *)

(** For a given VC, a model is a set of model elements representing
    CE values for source code elements. *)

(** {3 Model element kind} *)

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

(** {3 Model element concrete value} *)

(** Concrete syntax for model element values (which are of type [Term.term]),
    used for pretty printing and JSON printing. *)

(** Integers *)
type concrete_syntax_int = {
  int_value: Number.int_constant; (** Integer value *)
  int_verbatim: string (** String verbatim, as given by the SMT solver *)
}

(** Bitvectors *)
type concrete_syntax_bv = {
  bv_value: BigInt.t; (** Bitvector value *)
  bv_length: int; (** Length of the bitvector *)
  bv_verbatim : string (** String verbatim, as given by the SMT solver *)
}

(** Real numbers *)

type concrete_syntax_real = {
  real_value: Number.real_constant; (** Real value *)
  real_verbatim: string (** String verbatim, as given by the SMT solver *)
}

(** Fractions *)
type concrete_syntax_frac = {
  frac_num: concrete_syntax_real; (** Numerator *)
  frac_den: concrete_syntax_real; (** Denominator *)
  frac_verbatim: string (** String verbatim, as given by the SMT solver *)
}

(** Floats *)
type concrete_syntax_float_value =
  | Plus_infinity | Minus_infinity
  | Plus_zero | Minus_zero
  | NaN
  | Float_number of
    {
      float_sign : concrete_syntax_bv; (** Sign bit *)
      float_exp : concrete_syntax_bv; (** Exponent bits *)
      float_mant : concrete_syntax_bv; (** Mantissa (or significand) bits *)
      float_hex : string (** Hexadecimal reprensation *)
    }

type concrete_syntax_float = {
    float_exp_size : int; (** Size of the exponent *)
    float_significand_size : int; (** Size of the significand *)
    float_val : concrete_syntax_float_value (** Value of the constant *)
  }

(** Constants *)
type concrete_syntax_constant =
  | Boolean of bool
  | String of string
  | Integer of concrete_syntax_int
  | Real of concrete_syntax_real
  | Float of concrete_syntax_float
  | BitVector of concrete_syntax_bv
  | Fraction of concrete_syntax_frac

(** Quantifiers *)
type concrete_syntax_quant = Forall | Exists

(** Binary operators *)
type concrete_syntax_binop = And | Or | Implies | Iff

type concrete_syntax_funlit_elts =
  {
    elts_index : concrete_syntax_term;
    elts_value : concrete_syntax_term;
  }

(** Function literal value *)
and concrete_syntax_funlit =
  {
    elts : concrete_syntax_funlit_elts list;
    others : concrete_syntax_term;
  }

(** Function arguments and body *)
and concrete_syntax_fun = { args : string list; body : concrete_syntax_term; }

(** Concrete term *)
and concrete_syntax_term =
  | Var of string
  (** Variable of the given name *)
  | Const of concrete_syntax_constant
  (** Constant *)
  | Apply of string * concrete_syntax_term list
  (** Application of the given function symbol to the given list of concrete terms *)
  | If of concrete_syntax_term * concrete_syntax_term * concrete_syntax_term
  (** [If (cb,ct1,ct2)] stands for [if cb then t1 else ct2] *)
  | Epsilon of string * concrete_syntax_term
  (** [Epsilon (x,ct)] stands for [eps x. ct] *)
  | Quant of concrete_syntax_quant * string list * concrete_syntax_term
  (** [Quant (q,vars,ct)] stands for [q vars. ct] *)
  | Binop of concrete_syntax_binop * concrete_syntax_term * concrete_syntax_term
  (** [If (op,ct1,ct2)] stands for [ct1 op ct2] *)
  | Not of concrete_syntax_term
  (** Negation of a concrete term *)
  | Function of concrete_syntax_fun
  (** Function defined by the given list of arguments and the given body *)
  | FunctionLiteral of concrete_syntax_funlit
  (** Special case for function literals, also used for arrays *)
  | Record of (string * concrete_syntax_term) list
  (** Record defined by the given list of (field_name,field_value) elements *)
  | Proj of (string * concrete_syntax_term)
  (** Projections represent values that are defined by a type coercion:
     the value [eps x. ty'int x = 0] is represented by
     the concrete syntax term [Proj ty'int (Const (Integer 0))] *)
  | Let of (string * concrete_syntax_term) list * concrete_syntax_term
  (** A list of let bindings in a term *)

val print_concrete_term : Format.formatter -> concrete_syntax_term -> unit

(** Helper functions to create concrete terms *)

val concrete_var_from_vs : Term.vsymbol -> concrete_syntax_term
val concrete_const_bool : bool -> concrete_syntax_term
val concrete_apply_from_ls : Term.lsymbol -> concrete_syntax_term list -> concrete_syntax_term
val concrete_apply_equ : concrete_syntax_term -> concrete_syntax_term -> concrete_syntax_term
val subst_concrete_term :
  concrete_syntax_term Wstdlib.Mstr.t -> concrete_syntax_term -> concrete_syntax_term
val t_and_l_concrete : concrete_syntax_term list -> concrete_syntax_term

(** {3 Model elements} *)

(** Counter-example model elements. Each element represents
    a counterexample value for a single source code element.*)
type model_element = {
  me_kind             : model_element_kind;
    (** The kind of model element. *)
  me_value            : Term.term;
    (** Counterexample value for the element. *)
  me_concrete_value: concrete_syntax_term;
    (** Concrete syntax of the counterexample value. *)
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
(** Creates a counterexample model element.
    @param value counterexample value for the element
    @param concrete_value concrete syntax of the counterexample value
    @param oloc (optional) location of the element
    @param attrs attributes of the element
    @param lsymbol logical symbol corresponding to the element
*)

val get_lsymbol_or_model_trace_name : model_element -> string
(** Given a model element [me], returns the model_trace attribute if it
    exists in [me.me_attrs], otherwise returns the name of the
    [me.me_lsymbol]. *)

(** {3 Model} *)

type model

val is_model_empty : model -> bool
val empty_model : model
val set_model_files : model -> model_element list Wstdlib.Mint.t Wstdlib.Mstr.t -> model

(** {2 Querying the model} *)

val get_model_elements : model -> model_element list
val get_model_term_loc : model -> Loc.position option
val get_model_term_attrs : model -> Ident.Sattr.t

(** {2 Searching model elements} *)

val search_model_element_for_id :
  model -> ?loc:Loc.position -> Ident.ident -> model_element option
(** [search_model_element_for_id m ?loc id] searches for a model element for
    identifier [id], at the location [id.id_loc], or at [loc], when given. *)

val search_model_element_call_result :
  model -> Expr.expr_id option -> model_element option
(** [search_model_element_call_result m oid] searches for a model element
   that holds the return value for a call with id [oid]. *)

(** {2 Printing the model} *)

val json_model : model -> Json_base.json
(** Counterexample model in JSON format.
    The format is documented in [share/ce-models.json]. *)

val print_model :
  print_attrs:bool ->
  Format.formatter ->
  model ->
  unit
(** Prints the counterexample model.
    @param model the counter-example model to print
    @param print_attrs when set to true, each element is printed together with the
    attrs associated to it.
*)

(** {2 Interleaving source code and model} *)

val interleave_with_source :
  print_attrs:bool ->
  ?start_comment:string ->
  ?end_comment:string ->
  model ->
  rel_filename:string ->
  source_code:string ->
  locations:(Loc.position * 'a) list ->
  string * (Loc.position * 'a) list
(** Given a source code and a counterexample model, interleaves
    the source code with information about the counterexample.
    That is, for each location in counterexample trace creates
    a comment in the output source code with information about
    values of counterexample model elements.

    @param start_comment the string that starts a comment
    @param end_comment the string that ends a comment
    @param model counterexample model
    @param rel_filename the file name of the source relative to the session
    @param source_code the input source code
    @param locations the source locations that are found in the code

    @return the source code with added comments with information
    about counter-example model. The second part of the pair are
    locations modified so that it takes into account that counterexamples
    were added.
*)

(** {2 Filtering the model} *)

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

(** {2 Cleaning the model} *)

(** Helper class which can be inherited by API users to clean a model,
    for example by removing elements that do not match a given condition,
    or removing some "useless" fields in records, etc. *)
class clean : object
  method model : model -> model
  method element : model_element -> model_element option
  method value : concrete_syntax_term -> concrete_syntax_term option
  method var : string -> concrete_syntax_term option
  method const : concrete_syntax_constant -> concrete_syntax_term option
  method integer : concrete_syntax_int -> concrete_syntax_term option
  method string : string -> concrete_syntax_term option
  method real : concrete_syntax_real -> concrete_syntax_term option
  method fraction : concrete_syntax_frac -> concrete_syntax_term option
  method float : concrete_syntax_float -> concrete_syntax_term option
  method boolean : bool -> concrete_syntax_term option
  method bitvector : concrete_syntax_bv -> concrete_syntax_term option
  method apply : string -> concrete_syntax_term list -> concrete_syntax_term option
  method cond : concrete_syntax_term -> concrete_syntax_term -> concrete_syntax_term -> concrete_syntax_term option
  method epsilon : string -> concrete_syntax_term -> concrete_syntax_term option
  method lett : (string * concrete_syntax_term) list -> concrete_syntax_term -> concrete_syntax_term option
  method neg : concrete_syntax_term -> concrete_syntax_term option
  method quant : concrete_syntax_quant -> string list -> concrete_syntax_term -> concrete_syntax_term option
  method binop : concrete_syntax_binop -> concrete_syntax_term -> concrete_syntax_term -> concrete_syntax_term option
  method func : string list -> concrete_syntax_term -> concrete_syntax_term option
  method funliteral : concrete_syntax_funlit_elts list -> concrete_syntax_term -> concrete_syntax_term option
  method record : (string * concrete_syntax_term) list -> concrete_syntax_term option
  method proj : string -> concrete_syntax_term -> concrete_syntax_term option
end

val clean_model : #clean -> model -> model

(** {2 Registering model parser} *)

type model_parser = Printer.printing_info -> string -> model
(** Parses the input string (i.e. the output of the SMT solver)
    into a model (i.e. a mapping of files and source code lines to
    model elements). *)

type raw_model_parser = Printer.printing_info -> string -> model_element list

val register_remove_field:
  ( Ident.Sattr.t * Term.term * concrete_syntax_term ->
    Ident.Sattr.t * Term.term * concrete_syntax_term ) ->
  unit

val register_model_parser : desc:Pp.formatted -> string -> raw_model_parser -> unit

val lookup_model_parser : string -> model_parser

val list_model_parsers : unit -> (string * Pp.formatted) list
