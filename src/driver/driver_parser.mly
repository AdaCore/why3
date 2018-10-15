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

%{
  open Driver_ast

%}

%token <int> INTEGER
%token <string> IDENT
%token <string> STRING
%token <string> OPERATOR
%token <string> RIGHTSQ_QUOTE
%token <string> RIGHTPAR_QUOTE
%token <string> INPUT (* never reaches the parser *)
%token THEORY END SYNTAX REMOVE META PRELUDE PRINTER MODEL_PARSER OVERRIDING USE
%token INTERFACE
%token VALID INVALID UNKNOWN FAIL
%token TIMEOUT OUTOFMEMORY STEPLIMITEXCEEDED TIME STEPS
%token UNDERSCORE LEFTPAR RIGHTPAR DOT DOTDOT QUOTE EOF
%token BLACKLIST
%token MODULE EXCEPTION VAL LITERAL
%token FUNCTION PREDICATE TYPE PROP ALL FILENAME TRANSFORM PLUGIN
%token COMMA CONSTANT
%token LEFTSQ RIGHTSQ LARROW

%nonassoc SYNTAX REMOVE PRELUDE INTERFACE
%nonassoc prec_pty

%start <Driver_ast.file> file
%start <Driver_ast.file_extract> file_extract
%%

file: list0_global_theory EOF { $1 }

list0_global_theory:
| (* epsilon *)
    { { f_global = []; f_rules = [] } }
| loc(global) list0_global_theory
    { {$2 with f_global = $1 :: ($2.f_global)} }
| theory list0_global_theory
    { {$2 with f_rules = $1 :: ($2.f_rules)} }

global:
| PRELUDE STRING { Prelude $2 }
| PRINTER STRING { Printer $2 }
| MODEL_PARSER STRING { ModelParser $2 }
| VALID STRING { RegexpValid $2 }
| INVALID STRING { RegexpInvalid $2 }
| TIMEOUT STRING { RegexpTimeout $2 }
| OUTOFMEMORY STRING { RegexpOutOfMemory $2 }
| STEPLIMITEXCEEDED STRING { RegexpStepLimitExceeded $2 }
| TIME STRING  { TimeRegexp $2 }
| STEPS STRING INTEGER { StepRegexp ($2, $3) }
| UNKNOWN STRING STRING { RegexpUnknown ($2, $3) }
| FAIL STRING STRING { RegexpFailure ($2, $3) }
| VALID INTEGER { ExitCodeValid $2 }
| INVALID INTEGER { ExitCodeInvalid $2 }
| TIMEOUT INTEGER { ExitCodeTimeout $2 }
| STEPLIMITEXCEEDED INTEGER { ExitCodeStepLimitExceeded $2 }
| UNKNOWN INTEGER STRING { ExitCodeUnknown ($2, $3) }
| FAIL INTEGER STRING { ExitCodeFailure ($2, $3) }
| FILENAME STRING { Filename $2 }
| TRANSFORM STRING { Transform $2 }
| PLUGIN STRING STRING { Plugin ($2,$3) }
| BLACKLIST STRING+ { Blacklist $2 }
| INPUT { assert false }

theory:
| THEORY loc(tqualid) list(loc(trule)) END
    { { thr_name = $2; thr_rules = $3 } }

syntax:
| OVERRIDING SYNTAX { true }
| SYNTAX            { false }

trule:
| PRELUDE STRING                 { Rprelude   ($2) }
| syntax TYPE      qualid STRING { Rsyntaxts  ($3, $4, $1) }
| syntax CONSTANT  qualid STRING { Rsyntaxfs  ($3, $4, $1) }
| syntax FUNCTION  qualid STRING { Rsyntaxfs  ($3, $4, $1) }
| syntax PREDICATE qualid STRING { Rsyntaxps  ($3, $4, $1) }
| syntax LITERAL   qualid STRING { Rliteral   ($3, $4, $1) }
| REMOVE PROP qualid             { Rremovepr  ($3) }
| REMOVE ALL                     { Rremoveall }
| META ident meta_args           { Rmeta      ($2, $3) }
| META STRING meta_args          { Rmeta      ($2, $3) }
| USE qualid                     { Ruse       ($2)     }

meta_args: separated_nonempty_list(COMMA,meta_arg) { $1 }

meta_arg:
| TYPE   meta_type { PMAty  $2 }
| FUNCTION  qualid { PMAfs  $2 }
| PREDICATE qualid { PMAps  $2 }
| PROP      qualid { PMApr  $2 }
| STRING           { PMAstr $1 }
| INTEGER          { PMAint $1 }

tqualid:
| ident              { [$1] }
| ident DOT tqualid  { $1 :: $3 }
| STRING DOT tqualid { $1 :: $3 }

qualid:  loc(qualid_)  { $1 }

qualid_:
| ident_rich         { [$1] }
| ident DOT qualid_  { ($1 :: $3) }

ident:
| IDENT        { $1 }
| SYNTAX       { "syntax" }
| REMOVE       { "remove" }
| PRELUDE      { "prelude" }
| INTERFACE    { "interface" }
| BLACKLIST    { "blacklist" }
| PRINTER      { "printer" }
| STEPS        { "steps" }
| MODEL_PARSER { "model_parser" }
| VALID        { "valid" }
| INVALID      { "invalid" }
| TIMEOUT      { "timeout" }
| UNKNOWN      { "unknown" }
| FAIL         { "fail" }
| FILENAME     { "filename" }
| TRANSFORM    { "transformation" }
| PLUGIN       { "plugin" }

ident_rich:
| ident                             { $1 }
| LEFTPAR operator RIGHTPAR         { $2 }
| LEFTPAR operator RIGHTPAR_QUOTE   { $2 ^ $3 }

operator:
| o = OPERATOR                      { if o.[0] <> '!' && o.[0] <> '?' then
                                      Ident.op_infix o else Ident.op_prefix o }
| OPERATOR UNDERSCORE               { Ident.op_prefix $1 }
| LEFTSQ rightsq                    { Ident.op_get $2 }
| LEFTSQ rightsq LARROW             { Ident.op_set $2 }
| LEFTSQ LARROW rightsq             { Ident.op_update $3 }
| LEFTSQ DOTDOT rightsq             { Ident.op_cut $3 }
| LEFTSQ UNDERSCORE DOTDOT rightsq  { Ident.op_rcut $4 }
| LEFTSQ DOTDOT UNDERSCORE rightsq  { Ident.op_lcut $4 }

rightsq:
| RIGHTSQ         { "" }
| RIGHTSQ_QUOTE   { $1 }

(* Types *)

meta_type:
| qualid meta_type_args       { PTyapp ($1, $2) }
| primitive_type_arg_common   { $1 }

meta_type_args:
| (* epsilon *) %prec prec_pty        { [] }
| primitive_type_arg meta_type_args   { $1 :: $2 }

primitive_type:
| qualid primitive_type_arg+  { PTyapp ($1, $2) }
| primitive_type_arg          { $1 }

primitive_type_arg:
| qualid                    { PTyapp ($1, []) }
| primitive_type_arg_common { $1 }

primitive_type_arg_common:
| QUOTE ident                       { PTyvar $2 }
| LEFTPAR primitive_types RIGHTPAR  { PTuple $2 }
| LEFTPAR RIGHTPAR                  { PTuple [] }
| LEFTPAR primitive_type RIGHTPAR   { $2 }

primitive_types:
| primitive_type COMMA primitive_type  { [$1; $3] }
| primitive_type COMMA primitive_types { $1 :: $3 }

(* WhyML *)

file_extract:
| list0_global_theory_module EOF { $1 }

list0_global_theory_module:
| (* epsilon *)
    { { fe_global = []; fe_th_rules = []; fe_mo_rules = [] } }
| loc(global_extract) list0_global_theory_module
    { {$2 with fe_global = $1 :: ($2.fe_global)} }
| theory list0_global_theory_module
    { {$2 with fe_th_rules = $1 :: ($2.fe_th_rules)} }
| module_ list0_global_theory_module
    { {$2 with fe_mo_rules = $1 :: ($2.fe_mo_rules)} }

global_extract:
| PRELUDE STRING    { EPrelude $2 }
| PRINTER STRING    { EPrinter $2 }
| BLACKLIST STRING+ { EBlacklist $2 }

module_:
| MODULE loc(tqualid) list(loc(mrule)) END
    { { mor_name = $2; mor_rules = $3 } }

mrule:
| trule                          { MRtheory $1 }
| INTERFACE STRING               { MRinterface ($2) }
| SYNTAX EXCEPTION qualid STRING { MRexception ($3, $4) }
| SYNTAX VAL qualid STRING       { MRval ($3, $4) }

loc(X): X { Loc.extract ($startpos,$endpos), $1 }
