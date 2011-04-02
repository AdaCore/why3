

{

  open Lexing

  type element =
    { name : string;
      attributes : (string * string) list;
      elements : element list;
    }

  let buf = Buffer.create 17

  let rec pop_all group_stack element_stack =
    match group_stack with
      | [] -> element_stack
      | (elem,att,elems)::g ->
	  let e = {
	    name = elem;
	    attributes = att;
	    elements = List.rev element_stack;
	  }
	  in pop_all g (e::elems)
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

rule xml_header = parse
| "<?xml version=\"1.0\" encoding=\"UTF-8\"?>" 
    { elements [] [] lexbuf }
| _ 
    { failwith "[Xml error] wrong header" }
      
and elements group_stack element_stack = parse
  | space+ 
      { elements group_stack element_stack lexbuf }
  | '<' (ident as elem)   
      { attributes group_stack element_stack elem [] lexbuf }
  | "</" (ident as celem) space* '>'
      { match group_stack with
         | [] -> 
             Format.eprintf "[Xml warning] unexpected closing Xml element `%s'@." celem;
             elements group_stack element_stack lexbuf
         | (elem,att,stack)::g ->
             if celem <> elem then
               Format.eprintf "[Xml warning] Xml element `%s' closed by `%s'@." elem celem;
	     let e = {
	        name = elem;
	        attributes = att;
	        elements = List.rev element_stack;
	     }
             in elements g (e::stack) lexbuf            
       }
  | '<'
      { Format.eprintf "[Xml warning] unexpected '<'@.";
        elements group_stack element_stack lexbuf }      
  | eof 
      { match group_stack with
         | [] -> element_stack
         | (elem,_,_)::_ ->
             Format.eprintf "[Xml warning] unclosed Xml element `%s'@." elem;
             pop_all group_stack element_stack
      }
  | _ as c
      { failwith ("[Xml error] invalid element starting with " ^ String.make 1 c) }

and attributes groupe_stack element_stack elem acc = parse
  | space+
      { attributes groupe_stack element_stack elem acc lexbuf }
  | (ident as key) space* '=' 
      { let v = value lexbuf in
        attributes groupe_stack element_stack elem ((key,v)::acc) lexbuf }
  | '>' 
      { elements ((elem,acc,element_stack)::groupe_stack) [] lexbuf }
  | "/>"
      { let e = { name = elem ; 
                  attributes = acc;
                  elements = [] }
        in
        elements groupe_stack (e::element_stack) lexbuf }
  | _ as c
      { failwith ("[Xml error] `>' expected, got " ^ String.make 1 c) }
  | eof
      { failwith ("[Xml error] unclosed element, `>' expected") }

and value = parse
  | space+ 
      { value lexbuf }
(*
  | integer as i
      { RCint (int_of_string i) }
  | real as r
      { RCfloat (float_of_string r) }
*)
  | '"' 
      { Buffer.clear buf;
	string_val lexbuf } 
(*
  | "true"
      { RCbool true }
  | "false"
      { RCbool false }
  | ident as id
      { RCident id }
*)
  | _ as c
      { failwith ("[Xml error] invalid value starting with " 
		  ^ String.make 1 c) }
  | eof
      { failwith "[Xml error] unterminated keyval pair" }

and string_val = parse 
  | '"' 
      { Buffer.contents buf }
  | [^ '\\' '"'] as c
      { Buffer.add_char buf c;
        string_val lexbuf }
  | '\\' (['\\''\"'] as c)   
      { Buffer.add_char buf c;
        string_val lexbuf }
  | '\\' 'n'
      { Buffer.add_char buf '\n';
        string_val lexbuf }
  | '\\' (_ as c)
      { Buffer.add_char buf '\\';
        Buffer.add_char buf c;
        string_val lexbuf }
  | eof
      { failwith "[Xml error] unterminated string" }


{

  let from_file f =
      let c = 
(*
	try 
*)
	open_in f 
(*
	with Sys_error _ -> 
	  Format.eprintf "Cannot open file %s@." f;
	  exit 1
*)
      in
      let lb = Lexing.from_channel c in
      let l = xml_header lb in
      close_in c;
      List.rev l

}
