(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2007-2012                                               *)
(*    CEA   (Commissariat à l'énergie atomique et aux énergies            *)
(*           alternatives)                                                *)
(*    INRIA (Institut National de Recherche en Informatique et en         *)
(*           Automatique)                                                 *)
(*                                                                        *)
(*  you can redistribute it and/or modify it under the terms of the GNU   *)
(*  Lesser General Public License as published by the Free Software       *)
(*  Foundation, version 2.1.                                              *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU Lesser General Public License for more details.                   *)
(*                                                                        *)
(*  See the GNU Lesser General Public License version 2.1                 *)
(*  for more details (enclosed in the file licenses/LGPLv2.1).            *)
(*                                                                        *)
(**************************************************************************)

{

  open Why3

(*
  let int_of_digit chr =
    match chr with
        '0'..'9' -> (Char.code chr) - (Char.code '0')
      | 'a'..'f' -> (Char.code chr) - (Char.code 'a') + 10
      | 'A'..'F' -> (Char.code chr) - (Char.code 'A') + 10
      | _ -> assert false
*)


  let remove_leading_plus s =
    let n = String.length s in
    if n > 0 && s.[0] = '+' then String.sub s 1 (n-1) else s

}

let rD = ['0'-'9']
let rO = ['0'-'7']
let rH = ['a'-'f' 'A'-'F' '0'-'9']
let rFS	= ('f'|'F'|'l'|'L')?
let rIS = ('u'|'U'|'l'|'L')*

(*
let hex_escape = '\\' ['x' 'X'] rH+
let oct_escape = '\\' rO rO? rO?
*)

(* integer literals, both decimal, hexadecimal and octal *)
rule integer_literal = parse
  (* hexadecimal *)
  | '0'['x''X'] (rH+ as d) rIS eof { Number.int_literal_hex d }
  (* octal *)
  | '0' (rO+ as d)         rIS eof { Number.int_literal_oct d }
  (* decimal *)
  | (rD+ as d)             rIS eof { Number.int_literal_dec d }
(* TODO: character literals
  | ('L'? "'" as prelude) (([^ '\\' '\'' '\n']|("\\"[^ '\n']))+ as content) "'"
      {
        let b = Buffer.create 5 in
        Buffer.add_string b prelude;
        let lbf = Lexing.from_string content in
        CONSTANT (IntConstant (chr b lbf ^ "'"))
      }
*)
  | eof { invalid_arg "integer_literal: empty string" }
  | _ as c  { invalid_arg ("integer_literal: character '" ^
                              String.make 1 c ^ "'") }

(* floating-point literals, both decimal and hexadecimal *)
and floating_point_literal = parse
  (* decimal *)
  | ( (rD+ as i) ("" as f) ['e' 'E'] (['-' '+']? rD+ as e)
    | (rD+ as i) '.' (rD* as f) (['e' 'E'] (['-' '+']? rD+ as e))?
    | (rD* as i) '.' (rD+ as f) (['e' 'E'] (['-' '+']? rD+ as e))? )
    rFS eof
      { Number.real_const_dec i f (Opt.map remove_leading_plus e) }

  (* hexadecimal *)
  | '0'['x''X'] ( (rH* as i) '.' (rH+ as f)
                | (rH+ as i) '.' (rH* as f)
                | (rH+ as i) ("" as f) )
    ['p''P'] (('-' rD+) as e | '+'? (rD+ as e) )
    rFS eof
      { Number.real_const_hex i f (Some e) }

  | eof { invalid_arg "floating_point_literal: empty string" }
  | _ as c  { invalid_arg ("floating_point_literal: character '" ^
                              String.make 1 c ^ "'") }


(* TODO ?
and string_literal = parse
  | 'L'? '"' as prelude (([^ '\\' '"' '\n']|("\\"[^ '\n']))* as content) '"'
      { STRING_LITERAL (prelude.[0] = 'L',content) }
*)

(*
and chr buffer = parse
  | hex_escape
      { let s = lexeme lexbuf in
        let real_s = String.sub s 2 (String.length s - 2) in
        let rec add_one_char s =
          let l = String.length s in
          if l = 0 then ()
          else
          let h = int_of_digit s.[0] in
          let c,s =
            if l = 1 then (h,"")
            else
              (16*h + int_of_digit s.[1],
               String.sub s 2 (String.length s - 2))
          in
          Buffer.add_char buffer (Char.chr c); add_one_char s
        in add_one_char real_s; chr buffer lexbuf
      }
  | oct_escape
      { let s = lexeme lexbuf in
        let real_s = String.sub s 1 (String.length s - 1) in
        let rec value i s =
          if s = "" then i
          else value (8*i+int_of_digit s.[0])
            (String.sub s 1 (String.length s -1))
        in let c = value 0 real_s in
        Buffer.add_char buffer (Char.chr c); chr buffer lexbuf
      }
  | escape
      { Buffer.add_char buffer
          (match (lexeme lexbuf).[1] with
               'a' -> '\007'
             | 'b' -> '\b'
             | 'f' -> '\012'
             | 'n' -> '\n'
             | 'r' -> '\r'
             | 't' -> '\t'
             | '\'' -> '\''
             | '"' -> '"'
             | '?' -> '?'
             | '\\' -> '\\'
             | _ -> assert false
          ); chr buffer lexbuf}
  | eof { Buffer.contents buffer }
  | _  { Buffer.add_string buffer (lexeme lexbuf); chr buffer lexbuf }
*)


{

let integer s =
  let b = Lexing.from_string s in integer_literal b

let floating_point s =
  let b = Lexing.from_string s in floating_point_literal b


}

(*
Local Variables:
compile-command: "make -C ."
End:
*)
