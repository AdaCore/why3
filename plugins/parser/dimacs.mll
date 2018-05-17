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

(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2013                                                    *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
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
open Wstdlib

type vars = Term.term array
let get_indice i =
  if i > 0 then (i-1)*2
  else if i < 0 then (-i-1)*2+1
  else assert false

let init_vars th_uc nb_var =
  let a = Array.make (nb_var*2) Term.t_true in
  let th = ref th_uc in
  for i = nb_var downto -nb_var do
    if i <> 0 then
      if i > 0 then
        let id = Ident.id_fresh (Printf.sprintf "x%i" i) in
        let ls = Term.create_psymbol id [] in
        th := Theory.add_param_decl !th ls;
        a.(get_indice i) <- (Term.ps_app ls [])
      else if i < 0 then
        a.(get_indice i) <- Term.t_not a.(get_indice (-i))
  done;
  !th,a


let get_lit vars i =
  let i = int_of_string i in
  vars.(get_indice i)

exception SyntaxError of string

let syntax_error s = raise (SyntaxError s)

let () = Exn_printer.register (fun fmt e -> match e with
  | SyntaxError s -> Format.pp_print_string fmt s
  | _ -> raise e)

}

let newline = '\n'
let space = [' ' '\t' '\r']+
let digit = ['0'-'9']
let sign = '-' | '+'
let integer = sign? digit+

rule find_header = parse
| newline  { Lexing.new_line lexbuf; find_header lexbuf }
| space    { find_header lexbuf }
| 'p'
    space+ "cnf"
    space+ (digit+ as nb_var)
    space+ (digit+ as nb_cls) { int_of_string nb_var,
                                int_of_string nb_cls }
| 'c' [^'\n']* '\n'  { Lexing.new_line lexbuf; find_header lexbuf }
| _
      { syntax_error "Can't find header" }

and clause vars acc = parse
| newline  { Lexing.new_line lexbuf; clause vars acc lexbuf }
| space { clause vars acc lexbuf }
| '0'  { List.rev acc }
| integer as i { clause vars ((get_lit vars i)::acc) lexbuf }
| _ { syntax_error "Bad clause" }

and file th_uc vars n = parse
| newline  { Lexing.new_line lexbuf; file th_uc vars n lexbuf }
| space { file th_uc vars n lexbuf }
| '0'  { file th_uc vars n lexbuf }
| integer as i { let l = clause vars [get_lit vars i] lexbuf in
                 let t = List.fold_left (fun acc t ->
                   Term.t_or acc t
                 ) Term.t_false l in
                 let pr = Decl.create_prsymbol
                   (Ident.id_fresh ("Cl"^(string_of_int n))) in
                 let th_uc = Theory.add_prop_decl th_uc Decl.Paxiom pr t in
                 file th_uc vars (n+1) lexbuf
               }
| 'c' [^'\n']* ('\n' | eof)  { Lexing.new_line lexbuf;
                               file th_uc vars n lexbuf }
| eof { th_uc }
| _ { syntax_error "Bad clauses" }

{

let parse th_uc filename cin =
  let lb = Lexing.from_channel cin in
  Loc.set_file filename lb;
  Loc.with_location (fun lexbuf ->
    let nb_vars, _ = find_header lexbuf in
    let th_uc, vars = init_vars th_uc nb_vars in
    file th_uc vars 0 lexbuf) lb

let parse _env _path filename cin =
  let th_uc = Theory.create_theory (Ident.id_fresh "Cnf") in
  let th_uc = parse th_uc filename cin in
  let pr = Decl.create_prsymbol (Ident.id_fresh "false") in
  let th_uc = Theory.add_prop_decl th_uc Decl.Pgoal pr Term.t_false in
  Mstr.singleton "Cnf" (Theory.close_theory th_uc)

let () = Env.register_format Env.base_language "dimacs" ["cnf"] parse
  ~desc:"@[<hov>Parser for dimacs format.@]"
}

(*
Local Variables:
compile-command: "unset LANG; make -C ../.."
End:
*)
