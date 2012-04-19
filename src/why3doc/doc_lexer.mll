(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(* Why3 to HTML *)

{

  open Format
  open Lexing
  open Why3

  let output_comments = ref true

  let newline lexbuf fmt =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum };
    fprintf fmt "\n"

  let make_table l =
    let ht = Hashtbl.create 97 in
    List.iter (fun s -> Hashtbl.add ht s ()) l;
    Hashtbl.mem ht

  let is_keyword1 = make_table
    [ "theory"; "end";
      "type"; "constant"; "function"; "predicate"; "inductive";
      "clone"; "use";
      "import"; "export"; "axiom"; "goal"; "lemma"; ]

  let is_keyword2 = make_table
    [ "match"; "with"; "let"; "in"; "if"; "then"; "else";
      "forall"; "exists";
      (* programs *)
      "as"; "assert"; "begin";
      "do"; "done"; "downto"; "else";
      "exception"; "val"; "for"; "fun";
      "if"; "in";
      "module"; "mutable";
      "rec"; "then"; "to";
      "try"; "while"; "invariant"; "variant"; "raise"; "label"; ]

  let get_loc lb =
    let p = Lexing.lexeme_start_p lb in
    p.pos_fname, p.pos_lnum, p.pos_cnum - p.pos_bol

}

let ident = ['A'-'Z' 'a'-'z' '_'] ['A'-'Z' 'a'-'z' '0'-'9' '_']*

rule scan fmt = parse
  | "(*)"  { fprintf fmt "(*)"; scan fmt lexbuf }
  | "(**"  { fprintf fmt "</pre>@\n";
             doc fmt [] lexbuf;
             fprintf fmt "<pre>@\n";
             scan fmt lexbuf }
  | "(*i"  { comment fmt false lexbuf;
             scan fmt lexbuf }
  | "(*"   { fprintf fmt "<font class=\"comment\">(*";
             comment fmt true lexbuf;
             fprintf fmt "</font>";
             scan fmt lexbuf }
  | eof    { () }
  | ident as s
    { if is_keyword1 s then
        fprintf fmt "<font class=\"keyword1\">%s</font>" s
      else if is_keyword2 s then
        fprintf fmt "<font class=\"keyword2\">%s</font>" s
      else begin
        let (* f,l,c as *) loc = get_loc lexbuf in
        (* Format.eprintf "  IDENT %s/%d/%d@." f l c; *)
        (* is this a def point? *)
        try
          let t = Doc_def.is_def loc in
          fprintf fmt "<a name=\"%s\">%s</a>" t s
        with Not_found ->
        (* is this a use point? *)
        try
          let id = Glob.locate loc in
          let fn, t = Doc_def.locate id in
          fprintf fmt "<a href=\"%s#%s\">%s</a>" fn t s
        with Not_found ->
        (* otherwise, just print it *)
          fprintf fmt "%s" s
      end;
      scan fmt lexbuf }
  | "<"    { fprintf fmt "&lt;"; scan fmt lexbuf }
  | ">"    { fprintf fmt "&gt;"; scan fmt lexbuf }
  | "&"    { fprintf fmt "&amp;"; scan fmt lexbuf }
  | "\n"   { newline lexbuf fmt; scan fmt lexbuf }
  | '"'    { fprintf fmt "&quot;"; string fmt true lexbuf;
             scan fmt lexbuf }
  | "'\"'"
  | _ as s { fprintf fmt "%s" s; scan fmt lexbuf }

and comment fmt do_output = parse
  | "(*"   { if do_output then fprintf fmt "(*";
             comment fmt do_output lexbuf;
             comment fmt do_output lexbuf }
  | "*)"   { if do_output then fprintf fmt "*)" }
  | eof    { () }
  | "\n"   { if do_output then newline lexbuf fmt;
             comment fmt do_output lexbuf }
  | '"'    { if do_output then fprintf fmt "&quot;";
             string fmt do_output lexbuf;
             comment fmt do_output lexbuf }
  | "<"    { if do_output then fprintf fmt "&lt;";
             comment fmt do_output lexbuf }
  | "&"    { if do_output then fprintf fmt "&amp;";
             comment fmt do_output lexbuf }
  | "'\"'"
  | _ as s { if do_output then fprintf fmt "%s" s;
             comment fmt do_output lexbuf }

and string fmt do_output = parse
  | "\n"   { if do_output then newline lexbuf fmt;
             string fmt do_output lexbuf }
  | '"'    { if do_output then fprintf fmt "&quot;" }
  | "<"    { if do_output then fprintf fmt "&lt;";
             string fmt do_output lexbuf }
  | ">"    { if do_output then fprintf fmt "&gt;";
             string fmt do_output lexbuf }
  | "&"    { if do_output then fprintf fmt "&amp;";
             string fmt do_output lexbuf }
  | "\\" _
  | _ as s { if do_output then fprintf fmt "%s" s;
             string fmt do_output lexbuf }

and doc fmt headings = parse
  | "*)"   { () }
  | eof    { () }
  | '{' (['1''2''3'] as c)
           { let n = Char.code c - Char.code '0' + 1 in
             fprintf fmt "<h%d>" n;
             doc fmt (n::headings) lexbuf }
  | '{' { fprintf fmt "{"; doc fmt (0::headings) lexbuf }
  | '}'    { match headings with
      | [] -> fprintf fmt "}"; doc fmt headings lexbuf
      | n :: r ->
        if n >= 2 then fprintf fmt "</h%d>" n else fprintf fmt "}";
        doc fmt r lexbuf
  }
  | '"'    { fprintf fmt "&quot;"; doc fmt headings lexbuf }
  | '\''   { fprintf fmt "&apos;"; doc fmt headings lexbuf }
  | '&'    { fprintf fmt "&amp;"; doc fmt headings lexbuf }
  | "<"    { fprintf fmt "&lt;"; doc fmt headings lexbuf }
  | ">"    { fprintf fmt "&gt;"; doc fmt headings lexbuf }
  | _ as c { fprintf fmt "%c" c; doc fmt headings lexbuf }
{

  let do_file fmt fname =
    (* input *)
    let cin = open_in fname in
    let lb = Lexing.from_channel cin in
    lb.Lexing.lex_curr_p <-
      { lb.Lexing.lex_curr_p with Lexing.pos_fname = fname };
    (* output *)
    fprintf fmt "<h1>File %s</h1>" fname;
    fprintf fmt "<pre>@\n";
    scan fmt lb;
    fprintf fmt "</pre>@\n";
    close_in cin

}

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3doc.opt"
End:
*)

