(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

{

  type attributes = (string * string) list

  type element =
    { name : string;
      attributes : (string * string) list;
      elements : element list;
    }

  let mk_element name attrs elems =
    { name = name;
      attributes = attrs;
      elements = List.rev elems;
    }

  type t =
      { version : string;
        encoding : string;
        doctype : string;
        dtd : string;
        content : element;
      }

  let buf = Buffer.create 17

  let rec pop_all group_stack element_stack =
    match group_stack with
      | [] -> element_stack
      | (elem,att,elems)::g ->
          let e = mk_element elem att element_stack in
          pop_all g (e::elems)

  exception Parse_error of string

  let parse_error s = raise (Parse_error s)

  let debug = Debug.register_info_flag "xml"
    ~desc:"Print@ the@ XML@ parser@ debugging@ messages."
}

let space = [' ' '\t' '\r' '\n']
let digit = ['0'-'9']
let letter = ['a'-'z' 'A'-'Z']
let ident = (letter | digit | '_') +
let sign = '-' | '+'
let integer = sign? digit+
let mantissa = ['e''E'] sign? digit+
let real = sign? digit* '.' digit* mantissa?
let escape = ['\\''"''n''t''r']

rule xml_prolog fixattrs = parse
| space+
    { xml_prolog fixattrs lexbuf }
| "<?xml" space+ "version=\"1.0\"" space+ "?>"
    { xml_doctype fixattrs "1.0" "" lexbuf }
| "<?xml" space+ "version=\"1.0\"" space+ "encoding=\"UTF-8\"" space+ "?>"
    { xml_doctype fixattrs "1.0" "" lexbuf }
| "<?xml" ([^'?']|'?'[^'>'])* "?>"
    { Debug.dprintf debug "[Xml warning] prolog ignored@.";
      xml_doctype fixattrs "1.0" "" lexbuf }
| _
    { parse_error "wrong prolog" }

and xml_doctype fixattrs version encoding = parse
| space+
    { xml_doctype fixattrs version encoding lexbuf }
| "<!DOCTYPE" space+ (ident as doctype) space+ [^'>']* ">"
    { match elements fixattrs [] [] lexbuf with
         | [x] ->
            { version = version;
              encoding = encoding;
              doctype = doctype;
              dtd = "";
              content = x;
            }
         | _ -> parse_error "there should be exactly one root element"
    }
| _
    { parse_error "wrong DOCTYPE" }

and elements fixattrs group_stack element_stack = parse
  | space+
      { elements fixattrs group_stack element_stack lexbuf }
  | '<' (ident as elem)
      { attributes fixattrs group_stack element_stack elem [] lexbuf }
  | "</" (ident as celem) space* '>'
      { match group_stack with
         | [] ->
             Debug.dprintf debug
               "[Xml warning] unexpected closing Xml element `%s'@."
               celem;
             elements fixattrs group_stack element_stack lexbuf
         | (elem,att,stack)::g ->
             if celem <> elem then
               Debug.dprintf debug
                 "[Xml warning] Xml element `%s' closed by `%s'@."
                 elem celem;
             let e = mk_element elem att element_stack in
             elements fixattrs g (e::stack) lexbuf
       }
  | '<'
      { Debug.dprintf debug "[Xml warning] unexpected '<'@.";
        elements fixattrs group_stack element_stack lexbuf }
  | eof
      { match group_stack with
         | [] -> element_stack
         | (elem,_,_)::_ ->
             Debug.dprintf debug "[Xml warning] unclosed Xml element `%s'@." elem;
             pop_all group_stack element_stack
      }
  | _ as c
      { parse_error ("invalid element starting with " ^ String.make 1 c) }

and attributes fixattrs groupe_stack element_stack elem acc = parse
  | space+
      { attributes fixattrs groupe_stack element_stack elem acc lexbuf }
  | (ident as key) space* '='
      { let v = value lexbuf in
        attributes fixattrs groupe_stack element_stack elem ((key,v)::acc) lexbuf }
  | '>'
      { let acc = fixattrs elem acc in
        elements fixattrs ((elem,acc,element_stack)::groupe_stack) [] lexbuf }
  | "/>"
      { let acc = fixattrs elem acc in
        let e = mk_element elem acc [] in
        elements fixattrs groupe_stack (e::element_stack) lexbuf }
  | _ as c
      { parse_error ("'>' expected, got " ^ String.make 1 c) }
  | eof
      { parse_error "unclosed element, `>' expected" }

and value = parse
  | space+
      { value lexbuf }
  | '"'
      { Buffer.clear buf;
        string_val lexbuf }
  | _ as c
      { parse_error ("invalid value starting with " ^ String.make 1 c) }
  | eof
      { parse_error "unterminated keyval pair" }

and string_val = parse
  | '"'
      { Buffer.contents buf }
  | "&lt;"
      { Buffer.add_char buf '<';
        string_val lexbuf }
  | "&gt;"
      { Buffer.add_char buf '>';
        string_val lexbuf }
  | "&quot;"
      { Buffer.add_char buf '"';
        string_val lexbuf }
  | "&apos;"
      { Buffer.add_char buf '\'';
        string_val lexbuf }
  | "&amp;"
      { Buffer.add_char buf '&';
        string_val lexbuf }
  | [^ '"'] as c
      { Buffer.add_char buf c;
        string_val lexbuf }
  | eof
      { parse_error "unterminated string" }

{

  let from_file ?(fixattrs=fun _ a -> a) f =
      let c = open_in f in
      let lb = Lexing.from_channel c in
      let t = xml_prolog fixattrs lb in
      close_in c;
      t

}
