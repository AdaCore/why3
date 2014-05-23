(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
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

  let output_comments = ref true

  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

  let make_table l =
    let ht = Hashtbl.create 97 in
    List.iter (fun s -> Hashtbl.add ht s ()) l;
    Hashtbl.mem ht

  let is_keyword1 = make_table [ "as"; "axiom"; "clone"; "coinductive";
    "constant"; "else"; "end"; "epsilon"; "exists"; "export"; "false";
    "forall"; "function"; "goal"; "if"; "import"; "in"; "inductive";
    "lemma"; "let"; "match"; "meta"; "namespace"; "not"; "predicate";
    "prop"; "then"; "theory"; "true"; "type"; "use"; "with";
    (* programs *) "abstract"; "any";
    "begin"; "do"; "done"; "downto"; "exception";
    "for"; "fun"; "ghost"; "loop"; "model"; "module";
    "mutable"; "private"; "raise"; "rec";
    "to"; "try"; "val"; "while"; ]

  let is_keyword2 = make_table [ "absurd"; "assert"; "assume";
    "ensures"; "check"; "invariant"; "raises"; "reads"; "requires";
    "returns"; "variant"; "writes"; "diverges"; ]

  let get_loc lb =
    Loc.extract (Lexing.lexeme_start_p lb, Lexing.lexeme_end_p lb)

  let html_char fmt c =
    pp_print_string fmt (match c with
      | '<' -> "&lt;"
      | '>' -> "&gt;"
      | '&' -> "&amp;"
      | _ -> assert false)

  let html_escape s =
    let len = ref 0 in
    String.iter (function '<' | '>' -> len := !len + 4
      | '&' -> len := !len + 5 | _ -> incr len) s;
    let len' = !len in
    let len = String.length s in
    if len = len' then s else begin
      let t = String.create len' in
      let j = ref 0 in
      let app u =
        let l = String.length u in
        String.blit u 0 t !j l;
        j := !j + l in
      for i = 0 to len - 1 do
        match s.[i] with
        | '<' -> app "&lt;"
        | '>' -> app "&gt;"
        | '&' -> app "&amp;"
        | c -> t.[!j] <- c; incr j
      done;
      t
    end

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
      let s = html_escape s in
      try
        match Glob.find loc with
        | id, Glob.Def ->
          let t = Doc_def.anchor id in
          fprintf fmt "<a name=\"%s\">%s</a>" t s
        | id, Glob.Use ->
          let url = Doc_def.locate id in
          fprintf fmt "<a href=\"%s\">%s</a>" url s
      with Not_found ->
        (* otherwise, just print it *)
        pp_print_string fmt s
    end

  type empty_line = PrevEmpty | CurrEmpty | NotEmpty

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
let ident = ['A'-'Z' 'a'-'z' '_'] ['A'-'Z' 'a'-'z' '0'-'9' '_']* | operator
let special = ['<' '>' '&']

rule scan fmt empty = parse
  | "(*)" as s
          { pp_print_string fmt s;
            scan fmt NotEmpty lexbuf }
  | space* "(***"
          { comment fmt false lexbuf;
            scan fmt empty lexbuf }
  | space* "(**"
          { pp_print_string fmt "</pre>\n";
            if empty <> PrevEmpty then
              pp_print_string fmt "<div class=\"info\">";
            doc fmt false [] lexbuf;
            if empty <> PrevEmpty then pp_print_string fmt "</div>";
            pp_print_string fmt "<pre>";
            scan fmt CurrEmpty lexbuf }
  | "(**)"
          { pp_print_string fmt "<span class=\"comment\">(**)</span>";
            scan fmt NotEmpty lexbuf }
  | "(*"
          { pp_print_string fmt "<span class=\"comment\">(*";
            comment fmt true lexbuf;
            pp_print_string fmt "</span>";
            scan fmt NotEmpty lexbuf }
  | eof   { () }
  | ident as s
          { print_ident fmt lexbuf s;
            scan fmt NotEmpty lexbuf }
  | space* '\n'
          { newline lexbuf;
            if empty <> PrevEmpty then pp_print_char fmt '\n';
            let e = if empty = NotEmpty then CurrEmpty else PrevEmpty in
            scan fmt e lexbuf }
  | '"'   { pp_print_string fmt "&quot;";
            string fmt true lexbuf;
            scan fmt NotEmpty lexbuf }
  | "'\"'"
  | _ as s
          { pp_print_string fmt s;
            scan fmt NotEmpty lexbuf }

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
  | "\n"   { newline lexbuf;
             pp_print_char fmt '\n';
             scan_embedded fmt depth lexbuf }
  | '"'    { pp_print_string fmt "&quot;";
             string fmt true lexbuf;
             scan_embedded fmt depth lexbuf }
  | "'\"'"
  | _ as s { pp_print_string fmt s;
             scan_embedded fmt depth lexbuf }

and comment fmt do_output = parse
  | "(*"   { if do_output then pp_print_string fmt "(*";
             comment fmt do_output lexbuf;
             comment fmt do_output lexbuf }
  | "*)"   { if do_output then pp_print_string fmt "*)" }
  | eof    { () }
  | "\n"   { newline lexbuf;
             if do_output then pp_print_char fmt '\n';
             comment fmt do_output lexbuf }
  | '"'    { if do_output then pp_print_string fmt "&quot;";
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
             if do_output then pp_print_char fmt '\n';
             string fmt do_output lexbuf }
  | '"'    { if do_output then pp_print_string fmt "&quot;" }
  | special as c
           { if do_output then html_char fmt c;
             string fmt do_output lexbuf }
  | "\\" _
  | _ as s { if do_output then pp_print_string fmt s;
             string fmt do_output lexbuf }

and doc fmt block headings = parse
  | ' '* "*)"
           { if block then pp_print_string fmt "</p>\n" }
  | eof    { () }
  | "\n\n" { newline lexbuf;
             newline lexbuf;
             if block then pp_print_string fmt "</p>";
             pp_print_char fmt '\n';
             doc fmt false headings lexbuf }
  | "\n"   { newline lexbuf;
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
    pp_print_string fmt "<div class=\"why3doc\">\n<pre>";
    scan fmt PrevEmpty lb;
    pp_print_string fmt "</pre>\n</div>\n";
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

