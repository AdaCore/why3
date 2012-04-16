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

open Format

let print_header fmt ?(title="") ?css () =
  fprintf fmt "<html>@\n<head>@\n";
  begin match css with
    | None -> ()
    | Some f -> fprintf fmt
        "<link rel=\"stylesheet\" href=\"%s\" type=\"text/css\">@\n" f
  end;
  fprintf fmt "<title>%s</title>@\n" title;
  fprintf fmt "</head>@\n<body>@\n<pre>@\n"

let print_footer fmt () =
  fprintf fmt "</pre></body>@."

let style_css fname =
  let c = open_out fname in
  output_string c
"a:visited {color : #416DFF; text-decoration : none; }
a:link {color : #416DFF; text-decoration : none;}
a:hover {color : Red; text-decoration : none; background-color: #5FFF88}
a:active {color : Red; text-decoration : underline; }
.comment { color : #990000 }
.keyword1 { color : purple }
.keyword2 { color : green }
.superscript { font-size : 4 }
.subscript { font-size : 4 }
.warning { color : Red ; font-weight : bold }
.info { margin-left : 3em; margin-right : 3em }
.code { color : #465F91 ; }
h1 { font-size : 20pt ; text-align: center; }
h2 { font-size : 20pt ; border: 1px solid #000000; margin-top: 5px; margin-bottom: 2px;text-align: center; background-color: #90BDFF ;padding: 2px; }
h3 { font-size : 20pt ; border: 1px solid #000000; margin-top: 5px; margin-bottom: 2px;text-align: center; background-color: #90DDFF ;padding: 2px; }
h4 { font-size : 20pt ; border: 1px solid #000000; margin-top: 5px; margin-bottom: 2px;text-align: center; background-color: #90EDFF ;padding: 2px; }
h5 { font-size : 20pt ; border: 1px solid #000000; margin-top: 5px; margin-bottom: 2px;text-align: center; background-color: #90FDFF ;padding: 2px; }
h6 { font-size : 20pt ; border: 1px solid #000000; margin-top: 5px; margin-bottom: 2px;text-align: center; background-color: #90BDFF ; padding: 2px; }
div.h7 { font-size : 20pt ; border: 1px solid #000000; margin-top: 5px; margin-bottom: 2px;text-align: center; background-color: #90DDFF ; padding: 2px; }
div.h8 { font-size : 20pt ; border: 1px solid #000000; margin-top: 5px; margin-bottom: 2px;text-align: center; background-color: #F0FFFF ; padding: 2px; }
div.h9 { font-size : 20pt ; border: 1px solid #000000; margin-top: 5px; margin-bottom: 2px;text-align: center; background-color: #FFFFFF ; padding: 2px; }
.typetable { border-style : hidden }
.indextable { border-style : hidden }
.paramstable { border-style : hidden ; padding: 5pt 5pt}
body { background-color : White }
tr { background-color : White }
td.typefieldcomment { background-color : #FFFFFF }
pre { margin-bottom: 4px }
div.sig_block {margin-left: 2em}";
  close_out c

