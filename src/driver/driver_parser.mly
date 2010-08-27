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
  let loc_i i = (rhs_start_pos i, rhs_end_pos i)
  let infix s = "infix " ^ s
  let prefix s = "prefix " ^ s
%}

%token <int> INTEGER
%token <string> IDENT
%token <string> STRING
%token <string> OPERATOR
%token THEORY END SYNTAX REMOVE META PRELUDE PRINTER
%token VALID INVALID TIMEOUT UNKNOWN FAIL
%token UNDERSCORE LEFTPAR RIGHTPAR CLONED DOT EOF
%token LOGIC TYPE PROP FILENAME TRANSFORM PLUGIN
%token LEFTPAR_STAR_RIGHTPAR COMMA

%type <Driver_ast.file> file
%start file

%%

file:
| list0_global list0_theory EOF
    { { f_global = $1; f_rules = $2 } }
;

list0_global:
| /* epsilon */       { [] }
| global list0_global { (loc_i 1, $1) :: $2 }
;

global:
| PRELUDE STRING { Prelude $2 }
| PRINTER STRING { Printer $2 }
| VALID STRING { RegexpValid $2 }
| INVALID STRING { RegexpInvalid $2 }
| TIMEOUT STRING { RegexpTimeout $2 }
| UNKNOWN STRING STRING { RegexpUnknown ($2, $3) }
| FAIL STRING STRING { RegexpFailure ($2, $3) }
| VALID INTEGER { ExitCodeValid $2 }
| INVALID INTEGER { ExitCodeInvalid $2 }
| TIMEOUT INTEGER { ExitCodeTimeout $2 }
| UNKNOWN INTEGER STRING { ExitCodeUnknown ($2, $3) }
| FAIL INTEGER STRING { ExitCodeFailure ($2, $3) }
| FILENAME STRING { Filename $2 }
| TRANSFORM STRING { Transform $2 }
| PLUGIN STRING STRING { Plugin ($2,$3) }
;

list0_theory:
| /* epsilon */       { [] }
| theory list0_theory { $1 :: $2 }
;

theory:
| THEORY tqualid list0_trule END
    { { thr_name = $2; thr_rules = $3 } }
;

list0_trule:
| /* epsilon */     { [] }
| trule list0_trule { (loc_i 1, $1) :: $2 }
;

trule:
| PRELUDE STRING                      { Rprelude  ($2) }
| SYNTAX cloned TYPE qualid STRING    { Rsyntaxts ($2, $4, $5) }
| SYNTAX cloned LOGIC qualid STRING   { Rsyntaxls ($2, $4, $5) }
| REMOVE cloned PROP qualid           { Rremovepr ($2, $4) }
| META cloned ident meta_args         { Rmeta     ($2, $3, $4) }
| META cloned STRING meta_args        { Rmeta     ($2, $3, $4) }
;

meta_args:
| meta_arg                 { [$1] }
| meta_arg COMMA meta_args { $1 :: $3 }
;

meta_arg:
| TYPE  qualid { PMAts  $2 }
| LOGIC qualid { PMAls  $2 }
| PROP  qualid { PMApr  $2 }
| STRING       { PMAstr $1 }
| INTEGER      { PMAint $1 }
;

cloned:
| /* epsilon */ { false }
| CLONED        { true  }
;

tqualid:
| ident             { loc (), [$1] }
| ident DOT tqualid { loc (), ($1 :: snd $3) }
;

qualid:
| ident_rich        { loc (), [$1] }
| ident DOT qualid  { loc (), ($1 :: snd $3) }
;

ident:
| IDENT     { $1 }
| SYNTAX    { "syntax" }
| REMOVE    { "remove" }
/*
| CLONED    { "cloned" }
*/
| PRELUDE   { "prelude" }
| PRINTER   { "printer" }
| VALID     { "valid" }
| INVALID   { "invalid" }
| TIMEOUT   { "timeout" }
| UNKNOWN   { "unknown" }
| FAIL      { "fail" }
| FILENAME  { "filename" }
| TRANSFORM { "transformation" }
| PLUGIN    { "plugin" }
;

ident_rich:
| ident                                 { $1 }
| LEFTPAR_STAR_RIGHTPAR                 { infix "*" }
| LEFTPAR OPERATOR RIGHTPAR             { infix  $2 }
| LEFTPAR OPERATOR UNDERSCORE RIGHTPAR  { prefix $2 }
;

