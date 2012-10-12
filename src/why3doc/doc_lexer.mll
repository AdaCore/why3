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

  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

  let make_table l =
    let ht = Hashtbl.create 97 in
    List.iter (fun s -> Hashtbl.add ht s ()) l;
    Hashtbl.mem ht

  let is_keyword1 = make_table
    [ "theory"; "end"; "meta";
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

  let html_char fmt c =
    pp_print_string fmt (match c with
      | '<' -> "&lt;"
      | '>' -> "&gt;"
      | '&' -> "&amp;"
      | _ -> assert false)

  let current_file = ref ""

  let print_ident fmt lexbuf s =
    if is_keyword1 s then
      fprintf fmt "<span class=\"keyword1\">%s</span>" s
    else if is_keyword2 s then
      fprintf fmt "<span class=\"keyword2\">%s</span>" s
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
        let fn, url, t = Doc_def.locate id in
        let url = if fn = !current_file then "" else url in
        fprintf fmt "<a href=\"%s#%s\">%s</a>" url t s
      with Not_found ->
        (* otherwise, just print it *)
        pp_print_string fmt s
    end

}

let space = [' ' '\t']
let ident = ['A'-'Z' 'a'-'z' '_'] ['A'-'Z' 'a'-'z' '0'-'9' '_']*
let special = ['<' '>' '&']

rule scan fmt = parse
  | "(*)" as s
          { pp_print_string fmt s;
            scan fmt lexbuf }
  | ' '* "(***"
          { comment fmt false lexbuf;
            scan fmt lexbuf }
  | ' '* "(**"
          { fprintf fmt "</pre>@\n";
            doc fmt false [] lexbuf;
            fprintf fmt "<pre>";
            scan fmt lexbuf }
  | "(*"
          { fprintf fmt "<span class=\"comment\">(*";
            comment fmt true lexbuf;
            fprintf fmt "</span>";
            scan fmt lexbuf }
  | eof   { () }
  | ident as s
          { print_ident fmt lexbuf s;
            scan fmt lexbuf }
  | special as c
           { html_char fmt c;
             scan fmt lexbuf }
  | "\n"   { newline lexbuf;
             fprintf fmt "\n";
             scan fmt lexbuf }
  | '"'    { fprintf fmt "&quot;";
             string fmt true lexbuf;
             scan fmt lexbuf }
  | "'\"'"
  | _ as s { pp_print_string fmt s;
             scan fmt lexbuf }

and scan_embedded fmt depth = parse
  | '['   { pp_print_char fmt '[';
            scan_embedded fmt (depth + 1) lexbuf }
  | ']'   { if depth > 0 then begin
              pp_print_char fmt ']';
              scan_embedded fmt (depth - 1) lexbuf
            end }
  | eof   { () }
  | ident as s
          { print_ident fmt lexbuf s;
            scan_embedded fmt depth lexbuf }
  | special as c
           { html_char fmt c;
             scan_embedded fmt depth lexbuf }
  | "\n"   { newline lexbuf;
             fprintf fmt "\n";
             scan_embedded fmt depth lexbuf }
  | '"'    { fprintf fmt "&quot;";
             string fmt true lexbuf;
             scan_embedded fmt depth lexbuf }
  | "'\"'"
  | _ as s { pp_print_string fmt s;
             scan_embedded fmt depth lexbuf }

and comment fmt do_output = parse
  | "(*"   { if do_output then fprintf fmt "(*";
             comment fmt do_output lexbuf;
             comment fmt do_output lexbuf }
  | "*)"   { if do_output then fprintf fmt "*)" }
  | eof    { () }
  | "\n"   { newline lexbuf;
             if do_output then fprintf fmt "\n";
             comment fmt do_output lexbuf }
  | '"'    { if do_output then fprintf fmt "&quot;";
             string fmt do_output lexbuf;
             comment fmt do_output lexbuf }
  | special as c
           { if do_output then html_char fmt c;
             comment fmt do_output lexbuf }
  | "'\"'"
  | _ as s { if do_output then pp_print_string fmt s;
             comment fmt do_output lexbuf }

and string fmt do_output = parse
  | "\n"   { newline lexbuf;
             if do_output then fprintf fmt "\n";
             string fmt do_output lexbuf }
  | '"'    { if do_output then fprintf fmt "&quot;" }
  | special as c
           { if do_output then html_char fmt c;
             string fmt do_output lexbuf }
  | "\\" _
  | _ as s { if do_output then pp_print_string fmt s;
             string fmt do_output lexbuf }

and doc fmt block headings = parse
  | ' '* "*)"   { if block then fprintf fmt "</p>@\n" }
  | eof    { () }
  | "\n\n" { newline lexbuf;
             newline lexbuf;
             if block then pp_print_string fmt "</p>";
             fprintf fmt "@\n";
             doc fmt false headings lexbuf }
  | "\n"   { newline lexbuf;
             fprintf fmt "\n";
             doc fmt block headings lexbuf }
  | '{' (['1'-'6'] as c) ' '*
           { if block then fprintf fmt "</p>@\n";
             let n = Char.code c - Char.code '0' in
             fprintf fmt "<h%d>" n;
             doc fmt true (n::headings) lexbuf }
  | '{''h' { if not block then pp_print_string fmt "<p>";
             raw_html fmt 0 lexbuf; doc fmt true headings lexbuf }
  | '{'    { if not block then pp_print_string fmt "<p>";
             pp_print_char fmt '{';
             doc fmt true (0::headings) lexbuf }
  | '}'    { let brace r =
               if not block then pp_print_string fmt "<p>";
               fprintf fmt "}";
               doc fmt true r lexbuf 
             in
             match headings with
              | [] -> brace headings
              | n :: r ->
                if n >= 1 then begin
                  fprintf fmt "</h%d>" n;
                  doc fmt (r <> []) r lexbuf
                end else brace r
           }
  | '['    { if not block then pp_print_string fmt "<p>";
             pp_print_string fmt "<code>";
             scan_embedded fmt 0 lexbuf;
             pp_print_string fmt "</code>";
             doc fmt true headings lexbuf }
  | ' '    { if block then pp_print_char fmt ' ';
             doc fmt block headings lexbuf }
  | special as c
           { if not block then pp_print_string fmt "<p>";
             html_char fmt c;
             doc fmt true headings lexbuf }
  | _ as c { if not block then pp_print_string fmt "<p>";
             pp_print_char fmt c;
             doc fmt true headings lexbuf }


and raw_html fmt depth = parse
  | eof    { () }
  | "\n"   { newline lexbuf;
             fprintf fmt "\n";
             raw_html fmt depth lexbuf }
  | '{'    { fprintf fmt "{"; raw_html fmt (succ depth) lexbuf }
  | '}'    { if depth = 0 then () else
               begin
                 fprintf fmt "{";
                 raw_html fmt (pred depth) lexbuf
               end }
  | _ as c { pp_print_char fmt c; raw_html fmt depth lexbuf }


and extract_header = parse
  | "(**" space* "{" ['1'-'6'] ([^ '}']* as header) "}"
      { header }
  | space+ | "\n"
      { extract_header lexbuf }
  | "(*"
      { skip_comment lexbuf; extract_header lexbuf }
  | eof | _
      { "" }

and skip_comment = parse
  | "*)" { () }
  | "(*" { skip_comment lexbuf; skip_comment lexbuf }
  | eof  { () }
  | _    { skip_comment lexbuf }

{

  let do_file fmt fname =
    current_file := fname;
    (* input *)
    let cin = open_in fname in
    let lb = Lexing.from_channel cin in
    lb.Lexing.lex_curr_p <-
      { lb.Lexing.lex_curr_p with Lexing.pos_fname = fname };
    (* output *)
    fprintf fmt "<span class=\"why3doc\">@\n";
    fprintf fmt "<pre>@\n";
    scan fmt lb;
    fprintf fmt "</pre>@\n";
    fprintf fmt "</span>@\n";
    close_in cin

  let extract_header fname =
    let cin = open_in fname in
    let lb = Lexing.from_channel cin in
    let h = extract_header lb in
    close_in cin;
    h

}

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3doc.opt"
End:
*)

