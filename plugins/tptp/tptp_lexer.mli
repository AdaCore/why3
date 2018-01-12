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

exception FileNotFound of string

val load: string -> Tptp_ast.tptp_file
(** [load filename] loads and parses the file named [filename]. It
    also expands other included files in that file. As specified by
    the TPTP standard
    (http://www.cs.miami.edu/~tptp/TPTP/TR/TPTPTR.shtml), files
    included with relative path names are searched first under the
    directory of the main file, and if not found there then searched
    under the directory specified in the $TPTP environment variable.

    If the file, or one of its included file, is not found in the
    file system, then exception [FileNotFound s] is raised, where
    [s] is the name of the file not found.  *)
