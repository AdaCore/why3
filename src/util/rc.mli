(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** {1 Configuration file management} *)

type rc_value =
  | RCint of int
  | RCbool of bool
  | RCfloat of float
  | RCstring of string * bool (** escape eol *)
  | RCident of string

(** {2 Exceptions} *)

(* exception SyntaxError *)
exception ExtraParameters of string
(** [ExtraParameters name] is raised when a section named [name] has a
    parameter or when a family named [name] has more than one
    parameter. *)

exception MissingParameters of string
(** [MissingParameters name] is raised if a family named [name] has no
    parameters. *)

(* exception UnknownSection of string *)

exception UnknownField of string
(** [UnknownField key] is raised when an unexpected field [key]
    appears in a section. *)

(* exception MissingSection of string *)

exception MissingField of string
(** [MissingField key] is raised if the field [key] is required but
    not given. *)

exception DuplicateSection of string
(** [DuplicateSection name] is raised if there are more than one section named [name]. *)

exception DuplicateField of string * rc_value * rc_value
(** [DuplicateField key] is raised if the field [key] appears more than once. *)

exception StringExpected of string * rc_value
(** [StringExpected key value] is raised if a string was expected. *)

(* exception IdentExpected of string * rc_value *)
(* (\** [IdentExpected key value] string expected *\) *)

exception IntExpected of string * rc_value
(** [IntExpected key value] is raised if an integer was expected. *)

exception BoolExpected of string * rc_value
(** [BoolExpected key value] is raised if a boolean was expected. *)

val warn_missing_field: Loc.warning_id

(** {2 RC API} *)


type t
(** A parsed configuration file. *)

type section
(** A section in a configuration file. *)

type family = (string * section) list
(** A family of parameterized sections in a configuration file. *)

type simple_family = section list
(** A family of sections without parameters. *)

val empty : t
(** An empty configuration. *)

val empty_section : section
(** An empty section. *)

val get_section : t -> string -> section option
(** [get_section rc name]
    @return None if the section is not in the rc file.
    @raise DuplicateSection if multiple sections have the name [name].
    @raise ExtraParameters if [name] is a family in [rc] instead of a section.
*)

val get_family : t -> string -> family
(** [get_family rc name] returns all the sections of the family [name] in [rc].
    @raise MissingParameters if [name] also corresponds to a section in [rc].
*)

val get_simple_family : t -> string -> simple_family
(** [get_simple_family rc name] returns all the sections of the simple
    family [name] in [rc].
    @return [[]] if none are present.
    @raise ExtraParameters if [name] also corresponds to family in [rc].
*)

val set_section : t -> string -> section -> t
(** [set_section rc name section] adds a section [section] with name [name]
    in [rc]. It overwrites any former section named [name]. *)

val set_family : t -> string -> family -> t
(** [set_family rc name family] adds all the sections in [family] using
    the associated [string] as argument of the family [name] in [rc].
    It overwrites any former section of family [name]. *)

val set_simple_family : t -> string -> simple_family -> t
(** [set_simple_family rc name family] adds all the section in [family]
    using the associated [string] as argument of the family [name] in [rc].
    It overwrites any former section of family [name]. *)

val get_float : ?default:float -> section -> string -> float

val set_float : ?default:float -> section -> string -> float -> section

val get_int : ?default:int -> section -> string -> int
(** [get_int ?default section key] returns the integer value associated to key [key].

    @raise Bad_value_type if the value associated to [key] is not an integer.

    @raise Key_not_found if [default] is not given and no value is
    associated to [key].

    @raise Multiple_value if the key appears multiple time.
*)

val get_into : section -> string -> int option
(** [get_into section key] returns the integer value associated to key
    [key] if present, and [None] if missing. *)

val get_intl : section -> string -> int list
(** [get_intl section key] returns all the integer values associated to key [key].

    @raise Bad_value_type if any value associated to [key] is not an integer.
*)

val set_int : ?default:int -> section -> string -> int -> section
(** [set_int ?default section key value] associates [value] to [key]
    in the section, unless [value] is equal to [default].
    It removes all the former associations to this [key]. *)

val set_intl : section -> string -> int list -> section
(** [set_intl section key lvalue] associates to [key] all the values
    of [lvalue]. It removes all the former associations to this [key]. *)

val set_into : section -> string -> int option -> section
(** [set_int section key value] associates [value] to [key]
    in the section if it is not [None]. It removes all the former
    associations to this [key]. *)

val get_bool : ?default:bool -> section -> string -> bool
(** Same as {!get_int} but on bool. *)

val get_booll : section -> string -> bool list
(** Same as {!get_intl} but on bool. *)

val get_boolo : section -> string -> bool option
(** Same as {!get_into} but on bool. *)

val set_bool : ?default:bool -> section -> string -> bool -> section
(** Same as {!set_int} but on bool. *)

val set_booll : section -> string -> bool list -> section
(** Same as {!set_intl} but on bool. *)

val set_boolo : section -> string -> bool option -> section
(** Same as {!set_into} but on bool. *)


val get_string : ?default:string -> section -> string -> string
(** Same as {!get_int} but on string. *)

val get_stringl : section -> string -> string list
(** Same as {!get_intl} but on string. *)

val get_stringo : section -> string -> string option
(** Same as {!get_into} but on string. *)

val set_string : ?escape_eol:bool -> ?default:string -> section -> string -> string -> section
(** Same as {!set_int} but on string. [escape_eol] indicates if special
    characters should be escaped. *)

val set_stringl : ?escape_eol:bool -> section -> string -> string list -> section
(** Same as {!set_intl} but on string. *)

val set_stringo : ?escape_eol:bool -> section -> string -> string option -> section

(* val ident  : ?default:string      -> section -> string -> string *)
(*   (\** raise Bad_value_type *)
(*       raise Key_not_found *)
(*       raise Multiple_value *)
(*   *\) *)

(* val identl : ?default:string list -> section -> string -> string list *)
(*   (\** raise Bad_value_type *)
(*       raise Key_not_found *\) *)

(* val set_ident : section -> string -> string -> section *)
(*   (\** raise Yet_defined_key *)
(*       raise Bad_value_type *)
(*   *\) *)

(* val set_identl : section -> string -> string list -> section *)
(*   (\** raise Yet_defined_key *)
(*       raise Bad_value_type *)
(*   *\) *)

val check_exhaustive : section -> Wstdlib.Sstr.t -> unit
(** [check_exhaustive section keys] checks that only the keys in [keys]
    appear inside the section [section].

    @raise UnknownField if it is not the case.
*)

exception CannotOpen of string * string
exception SyntaxErrorFile of string * string

val from_channel : in_channel -> t
(** [from_channel cin] returns the Rc of the input channel [cin].
    @raise SyntaxErrorFile in case of incorrect syntax.
    @raise ExtraParameters if a section header has more than one argument.
*)

val from_file : string -> t
(** [from_file filename] returns the Rc of the file [filename].
    @raise CannotOpen if [filename] does not exist.
    @raise SyntaxErrorFile in case of incorrect syntax.
    @raise ExtraParameters if a section header has more than one argument.
*)

val to_formatter : Format.formatter -> t -> unit
(** [to_formatter fmt rc] writes the Rc [rc] to the formatter [fmt]. *)

val to_channel : out_channel -> t -> unit
(** [to_channel cout rc] writes the Rc [rc] to the output channel [out]. *)

val to_file : string -> t -> unit
(** [to_file filename rc] writes the Rc [rc] to the file [filename]. *)
