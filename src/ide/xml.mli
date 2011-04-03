

type element =
    { name : string;
      attributes : (string * string) list;
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

val from_file : string -> t
  (** returns the list of XML elements from the given file.
      raise [Sys_error] if the file cannot be opened.
      raise [Parse_error] if the file does not follow XML syntax
  *)

