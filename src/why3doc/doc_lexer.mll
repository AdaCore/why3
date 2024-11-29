(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* Why3 to HTML *)

{

  open Format
  open Lexing
  open Why3

  let backtrack lexbuf =
    lexbuf.lex_curr_pos <- lexbuf.lex_start_pos;
    lexbuf.lex_curr_p <- lexbuf.lex_start_p

  let make_table l =
    let ht = Hashtbl.create 97 in
    List.iter (fun s -> Hashtbl.add ht s ()) l;
    Hashtbl.mem ht

  let is_keyword = make_table Keywords.keywords

  let get_loc lb =
    Loc.extract (Lexing.lexeme_start_p lb, Lexing.lexeme_end_p lb)

  let print_ident ?(parentheses=false) fmt lexbuf s =
    if is_keyword s then
      fprintf fmt "<span class=\"keyword\">%s</span>" s
    else begin
      let loc =
        let loc = get_loc lexbuf in
        if parentheses then
          let (f,bl,bc,el,ec) = Loc.get loc in
          Loc.user_position f bl (bc + 1) el (ec - 1)
        else loc in
      try
        (* note that Doc_def.pp_{anchor,locate} might raise Not_found,
           so they need to be executed before anything is printed *)
        match Glob.find loc with
        | (id, Glob.Def, kind) ->
            let anchor = asprintf "%a" (Doc_def.pp_anchor ~kind) id in
            fprintf fmt "<a name=\"%s\">%a</a>" anchor Pp.html_string s
        | (id, Glob.Use, kind) ->
            let loc =
              match id.Ident.id_loc with
              | None -> raise Not_found
              | Some loc -> loc in
            (* several identifiers might be defined at the same location,
               so try to find the one with an anchor *)
            let id =
              match Glob.find loc with
              | ({ Ident.id_loc = Some _ } as id, Glob.Def, _) -> id
              | _ -> id
              | exception Not_found -> id in
            let target = asprintf "%a" (Doc_def.pp_locate ~kind) id in
            fprintf fmt "<a href=\"%s\">%a</a>" target Pp.html_string s
      with Not_found ->
        (* otherwise, just print it *)
        Pp.html_string fmt s
    end

}

let op_char_1 = ['=' '<' '>' '~']
let op_char_2 = ['+' '-']
let op_char_3 = ['*' '/' '%']
let op_char_4 = ['!' '$' '&' '?' '@' '^' '.' ':' '|' '#']
let op_char_34 = op_char_3 | op_char_4
let op_char_234 = op_char_2 | op_char_34
let op_char_1234 = op_char_1 | op_char_234
let op_char_pref = ['!' '?']
let prefix_op =
    op_char_1234* op_char_1 op_char_1234*
  | op_char_234*  op_char_2 op_char_234*
  | op_char_34* op_char_3 op_char_34*
  | op_char_4+
let operator =
    op_char_pref op_char_4*
  | prefix_op
  | prefix_op '_'
  | "[]"
  | "[<-]"
  | "[]<-"

let space = [' ' '\t']
let ident = ['A'-'Z' 'a'-'z' '_'] ['A'-'Z' 'a'-'z' '0'-'9' '_' '\'']* | operator
let special = ['\'' '"' '<' '>' '&']

rule scan fmt empty delayed = parse
  | "(*)" { pp_print_char fmt '(';
            print_ident ~parentheses:true fmt lexbuf "*";
            pp_print_char fmt ')';
            scan fmt false delayed lexbuf }
  | space* "(***"
          { comment fmt false lexbuf;
            scan fmt empty delayed lexbuf }
  | space* "(**"
          { pp_print_string fmt "</pre>\n<div class=\"info\">";
            if delayed <> "" then pp_print_string fmt delayed;
            doc fmt false [] lexbuf;
            pp_print_string fmt "</div>";
            scan_isolated fmt empty false "" lexbuf }
  | "(**)"
          { pp_print_string fmt "<span class=\"comment\">(**)</span>";
            scan fmt false delayed lexbuf }
  | "(*"
          { pp_print_string fmt "<span class=\"comment\">(*";
            comment fmt true lexbuf;
            pp_print_string fmt "</span>";
            scan fmt false delayed lexbuf }
  | ("[@" space* ([^ ' ' '\n' ']']+ (' '+ [^ ' ' '\n' ']']+)*) space* ']') as s
          { pp_print_string fmt "<span class=\"attribute\">";
            pp_print_string fmt s;
            pp_print_string fmt "</span>";
            scan fmt false delayed lexbuf }
  | eof   { pp_print_string fmt "</pre>\n";
            if delayed <> "" then
              fprintf fmt "<div class=\"info\">%s</div>" delayed }
  | ident as s
          { print_ident fmt lexbuf s;
            scan fmt false delayed lexbuf }
  | space* '\n'
          { new_line lexbuf;
            match empty, delayed with
            | false, d ->
              pp_print_char fmt '\n';
              scan fmt true d lexbuf
            | true, "" ->
              pp_print_char fmt '\n';
              scan_isolated fmt true true "" lexbuf
            | true, s ->
              fprintf fmt "</pre>\n<div class=\"info\">%s</div>" s;
              scan_isolated fmt true false "" lexbuf }
  | '"'   { pp_print_string fmt "<span class=\"string\">&quot;";
            string fmt true lexbuf;
            pp_print_string fmt "</span>";
            scan fmt false delayed lexbuf }
  | special as c
          { Pp.html_char fmt c;
            scan fmt false delayed lexbuf }
  | _ as c
          { pp_print_char fmt c;
            scan fmt false delayed lexbuf }

and scan_isolated fmt empty in_pre delayed = parse
  | space* "(***"
          { comment fmt false lexbuf;
            scan_isolated fmt empty in_pre delayed lexbuf }
  | space* "(**"
          { let d = asprintf "%s%a" delayed (fun fmt -> doc fmt false []) lexbuf in
            scan_isolated fmt false in_pre d lexbuf }
  | eof   { if in_pre then pp_print_string fmt "</pre>\n";
            if delayed <> "" then pp_print_string fmt delayed }
  | space* '\n'
          { new_line lexbuf;
            match empty, delayed with
            | false, d | true, ("" as d) ->
              scan_isolated fmt true in_pre d lexbuf
            | true, d ->
              if in_pre then pp_print_string fmt "</pre>\n";
              pp_print_string fmt d;
              scan_isolated fmt true false "" lexbuf }
  | ""    { if not in_pre then pp_print_string fmt "<pre>";
            scan fmt empty delayed lexbuf }

and scan_embedded fmt ldelim = parse
  | ' '* ('`' '`'* as delim) as s
          { if String.length delim <> ldelim then begin
              pp_print_string fmt s;
              scan_embedded fmt ldelim lexbuf
            end }
  | "(*"
  | "*)"  { backtrack lexbuf }
  | eof   { () }
  | "\n"  { new_line lexbuf;
            pp_print_char fmt '\n';
            scan_embedded fmt ldelim lexbuf }
  | special as c
          { Pp.html_char fmt c;
            scan_embedded fmt ldelim lexbuf }
  | "(*)"
  | _ as s
          { pp_print_string fmt s;
            scan_embedded fmt ldelim lexbuf }

and comment fmt do_output = parse
  | "(*"   { if do_output then pp_print_string fmt "(*";
             comment fmt do_output lexbuf;
             comment fmt do_output lexbuf }
  | "*)"   { if do_output then pp_print_string fmt "*)" }
  | eof    { () }
  | "\n"   { new_line lexbuf;
             if do_output then pp_print_char fmt '\n';
             comment fmt do_output lexbuf }
  | special as c
           { if do_output then Pp.html_char fmt c;
             comment fmt do_output lexbuf }
  | "(*)"
  | _ as s { if do_output then pp_print_string fmt s;
             comment fmt do_output lexbuf }

and string fmt do_output = parse
  | "\n"   { new_line lexbuf;
             if do_output then pp_print_char fmt '\n';
             string fmt do_output lexbuf }
  | '"'    { if do_output then pp_print_string fmt "&quot;" }
  | special as c
           { if do_output then Pp.html_char fmt c;
             string fmt do_output lexbuf }
  | "\\" _
  | _ as s { if do_output then pp_print_string fmt s;
             string fmt do_output lexbuf }

and doc fmt block headings = parse
  | ' '* "*)"
           { if block then pp_print_string fmt "</p>\n" }
  | eof    { () }
  | "\n" space* "\n" { new_line lexbuf;
             new_line lexbuf;
             if block then pp_print_string fmt "</p>";
             pp_print_char fmt '\n';
             doc fmt false headings lexbuf }
  | "\n"   { new_line lexbuf;
             pp_print_char fmt '\n';
             doc fmt block headings lexbuf }
  | '{' (['1'-'6'] as c) ' '*
           { if block then pp_print_string fmt "</p>\n";
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
               pp_print_char fmt '}';
               doc fmt true r lexbuf
             in
             match headings with
              | [] -> brace headings
              | n :: r ->
                if n >= 1 then begin
                  fprintf fmt "</h%d>\n" n;
                  doc fmt (r <> []) r lexbuf
                end else brace r
           }
  | "\\`"  { pp_print_char fmt '`';
             doc fmt true headings lexbuf }
  | ('`' '`'* as delim) ' '*
           { if not block then pp_print_string fmt "<p>";
             pp_print_string fmt "<code>";
             scan_embedded fmt (String.length delim) lexbuf;
             pp_print_string fmt "</code>";
             doc fmt true headings lexbuf }
  | ' '    { if block then pp_print_char fmt ' ';
             doc fmt block headings lexbuf }
  | special as c
           { if not block then pp_print_string fmt "<p>";
             Pp.html_char fmt c;
             doc fmt true headings lexbuf }
  | "(*"   { if not block then pp_print_string fmt "<p>";
             pp_print_string fmt "(*";
             comment fmt true lexbuf;
             doc fmt true headings lexbuf }
  | "(*)"
  | _ as s { if not block then pp_print_string fmt "<p>";
             pp_print_string fmt s;
             doc fmt true headings lexbuf }


and raw_html fmt depth = parse
  | "*)"  { backtrack lexbuf }
  | eof    { () }
  | "\n"   { new_line lexbuf;
             pp_print_char fmt '\n';
             raw_html fmt depth lexbuf }
  | '{'    { pp_print_char fmt '{'; raw_html fmt (succ depth) lexbuf }
  | '}'    { if depth = 0 then () else
               begin
                 pp_print_char fmt '}';
                 raw_html fmt (pred depth) lexbuf
               end }
  | _ as c { pp_print_char fmt c; raw_html fmt depth lexbuf }


and extract_header = parse
  | "(**" space* "{" ['1'-'6'] ([^ '}']* as header) "}"
      { header }
  | space+ | "\n"
      { extract_header lexbuf }
  | "(*)"
      { extract_header lexbuf }
  | "(*"
      { skip_comment lexbuf; extract_header lexbuf }
  | eof | _
      { "" }

and skip_comment = parse
  | "(*)" { skip_comment lexbuf }
  | "(*" { skip_comment lexbuf; skip_comment lexbuf }
  | "*)" { () }
  | eof  { () }
  | _    { skip_comment lexbuf }

{

  let do_file fmt fname =
    (* input *)
    let cin = open_in fname in
    let lb = Lexing.from_channel cin in
    lb.Lexing.lex_curr_p <-
      { lb.Lexing.lex_curr_p with Lexing.pos_fname = fname };
    (* output *)
    pp_print_string fmt "<div class=\"why3doc\">\n";
    scan_isolated fmt true false "" lb;
    pp_print_string fmt "\n</div>\n";
    close_in cin

  let extract_header fname =
    let cin = open_in fname in
    let lb = Lexing.from_channel cin in
    let h = extract_header lb in
    close_in cin;
    h

}
