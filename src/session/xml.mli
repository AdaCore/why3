(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

type attributes = (string * string) list

type element =
    { name : string;
      attributes : attributes;
      elements : element list;
    }

type t =
    { version : string;
      encoding : string;
      doctype : string;
      dtd : string;
      content : element;
    }

exception Parse_error of string

val from_file : 
  ?fixattrs:(string -> attributes -> attributes) -> string -> t
  (** returns the list of XML elements from the given file.
      raise [Sys_error] if the file cannot be opened.
      raise [Parse_error] if the file does not follow XML syntax
  *)

