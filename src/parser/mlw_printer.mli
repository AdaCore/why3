(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** {1 Pretty printing of Why3 parse trees as Why3 source code} *)

(** {2 Printers} *)

val pp_pattern : Ptree.pattern Pp.pp
(** Printer for patterns *)

val pp_expr : Ptree.expr Pp.pp
(** Printer for expressions *)

val pp_term : Ptree.term Pp.pp
(** Printer for terms *)

val pp_pty : Ptree.pty Pp.pp
(** Printer for types *)

val pp_decl : Ptree.decl Pp.pp
(** Printer for declarations *)

val pp_mlw_file : Ptree.mlw_file Pp.pp
(** Printer for mlw files *)

(** {2 Markers}

    When [Ptree] elements are generated (instead of being parsed from a
    whyml file), locations of typing errors are useless, because they do not
    correspond to any concrete syntax.

    Alternatively, we can give every [Ptree] element a unique location,
    for example using the function {!val:Mlw_printer.next_pos}. When a
    located error is encountered, the function {!val:with_marker} can
    then be used to instruct the mlw-printer to insert a message as a
    comment just before an expression, term, or pattern with the given
    location.

    For example, this can be used to indicate and show a typing error in
    the printed mlw-file:

    {[
      try
        let mm = Typing.type_mlw_file env path filename mlw_file in
        (* ... well typed mlw_file ... *)
      with Loc.Located (loc, e) -> (* A located exception [e] *)
        let msg = Format.asprintf "%a" Exn_printer.exn_printer e in
        Format.fprintf fmt "%a@."
          (Mlw_printer.with_marker ~msg loc Mlw_printer.pp_mlw_file)
          mlw_file
    ]}
*)

val next_pos : unit -> Loc.position
(** Generate a unique location. *)

val with_marker : ?msg:string -> Loc.position -> 'a Pp.pp -> 'a Pp.pp
(** Inform a printer to include the message (default: ["XXX"]) as a comment
   before the expression, term, or pattern with the given location.

    NOTE: This is currently implemented by a global reference and is
    therefore unsafe in threaded programs. *)
