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

  let newline fmt () = fprintf fmt "\n"

  let make_table l =
    let ht = Hashtbl.create 97 in
    List.iter (fun s -> Hashtbl.add ht s ()) l;
    Hashtbl.mem ht

  let is_keyword1 = make_table
    [ "theory"; "end";
      "type"; "constant"; "function"; "predicate"; "inductive";
      "clone"; "use";
      "import"; "export"; "axiom"; "goal"; "lemma";]
  let is_keyword2 = make_table
    [ "match"; "with"; "let"; "in"; "if"; "then"; "else";
      "forall"; "exists";

      "as"; "assert"; "begin";
      "do"; "done"; "downto"; "else";
      "exception"; "val"; "for"; "fun";
      "if"; "in";
      "module"; "mutable";
      "rec"; "then"; "to";
      "try"; "while"; "invariant"; "variant"; "raise"; "label";
    ]

}

let ident = ['A'-'Z' 'a'-'z' '_'] ['A'-'Z' 'a'-'z' '0'-'9' '_']*

rule scan fmt = parse
  | "(*)"  { fprintf fmt "(*)"; scan fmt lexbuf }
  | "(*"   { fprintf fmt "<font class=\"comment\">(*";
             comment fmt lexbuf;
             fprintf fmt "</font>";
             scan fmt lexbuf }
  | eof    { () }
  | ident as s
    { if is_keyword1 s then
        fprintf fmt "<font class=\"keyword1\">%s</font>" s
      else if is_keyword2 s then
        fprintf fmt "<font class=\"keyword2\">%s</font>" s
      else begin
        (* let loc = get_loc lexbuf in *)
        fprintf fmt "%s" s
      end;
      scan fmt lexbuf }
  | "<"    { fprintf fmt "&lt;"; scan fmt lexbuf }
  | "&"    { fprintf fmt "&amp;"; scan fmt lexbuf }
  | "\n"   { newline fmt (); scan fmt lexbuf }
  | '"'    { fprintf fmt "\""; string fmt lexbuf; scan fmt lexbuf }
  | "'\"'"
  | _ as s { fprintf fmt "%s" s; scan fmt lexbuf }

and comment fmt = parse
  | "(*"   { fprintf fmt "(*"; comment fmt lexbuf; comment fmt lexbuf }
  | "*)"   { fprintf fmt "*)" }
  | eof    { () }
  | "\n"   { newline fmt (); comment fmt lexbuf }
  | '"'    { fprintf fmt "\""; string fmt lexbuf; comment fmt lexbuf }
  | "<"    { fprintf fmt "&lt;"; comment fmt lexbuf }
  | "&"    { fprintf fmt "&amp;"; comment fmt lexbuf }
  | "'\"'"
  | _ as s { fprintf fmt "%s" s; comment fmt lexbuf }

and string fmt = parse
  | '"'    { fprintf fmt "\"" }
  | "<"    { fprintf fmt "&lt;"; string fmt lexbuf }
  | "&"    { fprintf fmt "&amp;"; string fmt lexbuf }
  | "\\" _
  | _ as s { fprintf fmt "%s" s; string fmt lexbuf }

{

  let do_file fmt fname =
    (* input *)
    let cin = open_in fname in
    let lb = Lexing.from_channel cin in
    (* output *)
    fprintf fmt "<pre>@\n";
    scan fmt lb;
    fprintf fmt "</pre>@\n";
    close_in cin

(*
  let () =
    Queue.iter do_file opt_queue
*)
}

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3doc.opt"
End:
*)

