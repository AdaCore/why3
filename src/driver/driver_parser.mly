/********************************************************************/
/*                                                                  */
/*  The Why3 Verification Platform   /   The Why3 Development Team  */
/*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  */
/*                                                                  */
/*  This software is distributed under the terms of the GNU Lesser  */
/*  General Public License version 2.1, with the special exception  */
/*  on linking described in file LICENSE.                           */
/*                                                                  */
/********************************************************************/

%{
  open Driver_ast

  let loc () = Loc.extract (symbol_start_pos (), symbol_end_pos ())
  let loc_i i = Loc.extract (rhs_start_pos i, rhs_end_pos i)
  let infix s = "infix " ^ s
  let prefix s = "prefix " ^ s
  let mixfix s = "mixfix " ^ s
%}

%token <string> INPUT /* never reaches the parser */

%token <int> INTEGER
%token <string> IDENT
%token <string> STRING
%token <string> OPERATOR
%token THEORY END SYNTAX REMOVE META PRELUDE PRINTER
%token VALID INVALID TIMEOUT OUTOFMEMORY UNKNOWN FAIL TIME
%token UNDERSCORE LEFTPAR RIGHTPAR DOT QUOTE EOF
%token BLACKLIST
%token MODULE EXCEPTION VAL
%token FUNCTION PREDICATE TYPE PROP FILENAME TRANSFORM PLUGIN
%token LEFTPAR_STAR_RIGHTPAR COMMA CONSTANT
%token LEFTSQ RIGHTSQ LARROW

%nonassoc SYNTAX REMOVE PRELUDE
%nonassoc prec_pty

%type <Driver_ast.file> file
%start file
%type <Driver_ast.file_extract> file_extract
%start file_extract

%%

file:
| list0_global_theory EOF
    { $1 }
;

list0_global_theory:
| /* epsilon */      { { f_global = []; f_rules = [] } }
| global list0_global_theory
    { {$2 with f_global = (loc_i 1, $1) :: ($2.f_global)} }
| theory list0_global_theory
    { {$2 with f_rules = $1 :: ($2.f_rules)} }
;

global:
| PRELUDE STRING { Prelude $2 }
| PRINTER STRING { Printer $2 }
| VALID STRING { RegexpValid $2 }
| INVALID STRING { RegexpInvalid $2 }
| TIMEOUT STRING { RegexpTimeout $2 }
| OUTOFMEMORY STRING { RegexpOutOfMemory $2 }
| TIME STRING  { TimeRegexp $2 }
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
| BLACKLIST list1_string_list { Blacklist $2 }
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
| PRELUDE STRING                   { Rprelude  ($2) }
| SYNTAX TYPE      qualid STRING   { Rsyntaxts ($3, $4) }
| SYNTAX CONSTANT  qualid STRING   { Rsyntaxfs ($3, $4) }
| SYNTAX FUNCTION  qualid STRING   { Rsyntaxfs ($3, $4) }
| SYNTAX PREDICATE qualid STRING   { Rsyntaxps ($3, $4) }
| REMOVE PROP qualid               { Rremovepr ($3) }
| META ident meta_args             { Rmeta     ($2, $3) }
| META STRING meta_args            { Rmeta     ($2, $3) }
;

meta_args:
| meta_arg                 { [$1] }
| meta_arg COMMA meta_args { $1 :: $3 }
;

meta_arg:
| TYPE primitive_type_top { PMAty $2 }
| FUNCTION  qualid { PMAfs  $2 }
| PREDICATE qualid { PMAps  $2 }
| PROP      qualid { PMApr  $2 }
| STRING           { PMAstr $1 }
| INTEGER          { PMAint $1 }
;

tqualid:
| ident              { loc (), [$1] }
| ident DOT tqualid  { loc (), ($1 :: snd $3) }
| STRING DOT tqualid { loc (), ($1 :: snd $3) }
;

qualid:
| ident_rich        { loc (), [$1] }
| ident DOT qualid  { loc (), ($1 :: snd $3) }
;

ident:
| IDENT     { $1 }
| SYNTAX    { "syntax" }
| REMOVE    { "remove" }
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
| ident                     { $1 }
| LEFTPAR_STAR_RIGHTPAR     { infix "*" }
| LEFTPAR operator RIGHTPAR { $2 }
;

operator:
| OPERATOR              { infix $1 }
| OPERATOR UNDERSCORE   { prefix $1 }
| LEFTSQ RIGHTSQ        { mixfix "[]" }
| LEFTSQ LARROW RIGHTSQ { mixfix "[<-]" }
| LEFTSQ RIGHTSQ LARROW { mixfix "[]<-" }
;

list1_string_list:
| STRING                   { [$1] }
| list1_string_list STRING { $2 :: $1 }
;

/* Types */

primitive_type_top:
| qualid primitive_type_args_top  { PTyapp ($1, $2) }
| primitive_type_arg_common       { $1 }
;

primitive_type_args_top:
| /* epsilon */ %prec prec_pty                { [] }
| primitive_type_arg primitive_type_args_top  { $1 :: $2 }
;

primitive_type:
| qualid primitive_type_args  { PTyapp ($1, $2) }
| primitive_type_arg          { $1 }
;

primitive_type_args:
| primitive_type_arg                      { [$1] }
| primitive_type_arg primitive_type_args  { $1 :: $2 }
;

primitive_type_arg:
| qualid                    { PTyapp ($1, []) }
| primitive_type_arg_common { $1 }
;

primitive_type_arg_common:
| type_var                          { PTyvar $1 }
| LEFTPAR primitive_types RIGHTPAR  { PTuple $2 }
| LEFTPAR RIGHTPAR                  { PTuple [] }
| LEFTPAR primitive_type RIGHTPAR   { $2 }
;

primitive_types:
| primitive_type COMMA primitive_type  { [$1; $3] }
| primitive_type COMMA primitive_types { $1 :: $3 }
;

type_var:
| QUOTE ident { $2 }
;

/* WhyML */

file_extract:
| list0_global_theory_module EOF
{ $1 }
;

list0_global_theory_module:
| /* epsilon */
    { { fe_global = []; fe_th_rules = []; fe_mo_rules = [] } }
| global_extract list0_global_theory_module
    { {$2 with fe_global = (loc_i 1, $1) :: ($2.fe_global)} }
| theory list0_global_theory_module
    { {$2 with fe_th_rules = $1 :: ($2.fe_th_rules)} }
| module_ list0_global_theory_module
    { {$2 with fe_mo_rules = $1 :: ($2.fe_mo_rules)} }
;

global_extract:
| PRELUDE STRING { EPrelude $2 }
| PRINTER STRING { EPrinter $2 }
| BLACKLIST list1_string_list { EBlacklist $2 }
;

module_:
| MODULE tqualid list0_mrule END
    { { mor_name = $2; mor_rules = $3 } }
;

list0_mrule:
| /* epsilon */     { [] }
| mrule list0_mrule { (loc_i 1, $1) :: $2 }
;

mrule:
| trule                          { MRtheory $1 }
| SYNTAX EXCEPTION qualid STRING { MRexception ($3, $4) }
| SYNTAX VAL qualid STRING       { MRval ($3, $4) }
;

