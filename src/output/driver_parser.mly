/**************************************************************************/
/*                                                                        */
/*  Copyright (C) 2010-                                                   */
/*    Francois Bobot                                                      */
/*    Jean-Christophe Filliatre                                           */
/*    Johannes Kanig                                                      */
/*    Andrei Paskevich                                                    */
/*                                                                        */
/*  This software is free software; you can redistribute it and/or        */
/*  modify it under the terms of the GNU Library General Public           */
/*  License version 2.1, with the special exception on linking            */
/*  described in file LICENSE.                                            */
/*                                                                        */
/*  This software is distributed in the hope that it will be useful,      */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  */
/*                                                                        */
/**************************************************************************/

%{
  open Driver_ast
  open Parsing
  let loc () = (symbol_start_pos (), symbol_end_pos ())
  let infix s = "infix " ^ s
  let prefix s = "prefix " ^ s
%}

%token <string> IDENT
%token <string> STRING
%token <string> OPERATOR
%token THEORY END SYNTAX REMOVE TAG
%token UNDERSCORE LEFTPAR RIGHTPAR STAR DOT EOF

%type <Driver_ast.file> file
%start file

%%

file:
| string_option list0_theory EOF
    { { f_prelude = $1; f_rules = $2 } }
;

string_option:
| /* epsilon */ { None }
| STRING        { Some $1 }
;

list0_theory:
| /* epsilon */       { [] }
| theory list0_theory { $1 :: $2 }
;

theory:
| THEORY qualid string_option list0_trule END
    { { th_name = $2; th_prelude = $3; th_rules = $4 } }
;

list0_trule:
| /* epsilon */     { [] }
| trule list0_trule { $1 :: $2 }
;

trule:
| REMOVE star qualid   { Rremove ($2, $3) }
| SYNTAX qualid STRING { Rsyntax ($2, $3) }
;

star:
| /* epsilon */ { false }
| STAR          { true  }
;

qualid:
| ident            { Qident $1 }
| qualid DOT ident { Qdot ($1, $3) }
;

ident:
| IDENT  
    { { id = $1; loc = loc () } }
| STRING 
    { { id = $1; loc = loc () } }
| LEFTPAR UNDERSCORE OPERATOR UNDERSCORE RIGHTPAR 
    { { id = infix $3; loc = loc () } }
| LEFTPAR OPERATOR UNDERSCORE RIGHTPAR 
    { { id = prefix $2; loc = loc () } }
;

