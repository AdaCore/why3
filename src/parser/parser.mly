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

  open Ptree
  open Parsing

  let loc () = (symbol_start_pos (), symbol_end_pos ())
  let loc_i i = (rhs_start_pos i, rhs_end_pos i)
  let loc_ij i j = (rhs_start_pos i, rhs_end_pos j)

  let mk_ppl loc d = { pp_loc = loc; pp_desc = d }
  let mk_pp d = mk_ppl (loc ()) d
  let mk_pp_i i d = mk_ppl (loc_i i) d
		    
  let mk_pat p = { pat_loc = loc (); pat_desc = p }

  let infix_ppl loc a i b = mk_ppl loc (PPinfix (a, i, b))
  let infix_pp a i b = infix_ppl (loc ()) a i b

  let prefix_ppl loc p a = mk_ppl loc (PPprefix (p, a))
  let prefix_pp p a = prefix_ppl (loc ()) p a

  let infix s = "infix " ^ s
  let prefix s = "prefix " ^ s
  let postfix s = "postfix " ^ s

%}

/* Tokens */ 

%token <string> LIDENT UIDENT
%token <string> INTEGER
%token <string> OP0 OP1 OP2 OP3
%token <Ptree.real_constant> FLOAT
%token <string> STRING

/* keywords */

%token AND AS AXIOM 
%token CLONE 
%token ELSE END EXISTS EXPORT FALSE FORALL  
%token GOAL
%token IF IMPORT IN INDUCTIVE LEMMA 
%token LET LOGIC MATCH 
%token NAMESPACE NOT OR  
%token THEN THEORY TRUE TYPE
%token USE WITH

/* symbols */

%token ARROW AT
%token BANG BAR 
%token COLON COMMA  
%token DOT EQUAL
%token LEFTB LEFTPAR LEFTSQ 
%token LRARROW
%token QUOTE RIGHTB 
%token RIGHTPAR RIGHTSQ 
%token UNDERSCORE

%token EOF


/* Precedences */

%left LEFTB 

%left COLON 

%left IN

%left ELSE

%right prec_named
%right prec_quant
%right ARROW LRARROW
%right OR 
%right AND 
%right NOT
%right prec_if
%left EQUAL OP0
%left OP1
%left OP2
%left OP3
%right unary_op
%left LEFTSQ

%nonassoc prec_decls
%nonassoc LOGIC TYPE INDUCTIVE

/* Entry points */

%type <Ptree.lexpr> lexpr
%start lexpr
%type <Ptree.decl list> list0_decl
%start list0_decl
%type <Ptree.logic_file> logic_file
%start logic_file
%%

logic_file:
| list1_theory EOF
   { $1 }
| EOF 
   { [] }
;

list1_decl:
| decl 
   { [$1] }
| decl list1_decl 
   { $1 :: $2 }
;

list0_decl:
| /* epsilon */
   { [] }
| list1_decl 
   { $1 }
;

ident:
| uident { $1 }
| lident { $1 }
;

ident_rich:
| uident      { $1 }
| lident_rich { $1 }
;

lident:
| LIDENT
    { { id = $1; id_loc = loc () } }
;

lident_rich:
| lident
    { $1 }
| LEFTPAR UNDERSCORE lident_op UNDERSCORE RIGHTPAR 
    { { id = infix $3; id_loc = loc () } }
| LEFTPAR lident_op UNDERSCORE RIGHTPAR 
    { { id = prefix $2; id_loc = loc () } }
/*
| LEFTPAR UNDERSCORE lident_op RIGHTPAR 
    { { id = postfix $3; id_loc = loc () } }
*/
;

lident_op:
| OP0   { $1 }
| OP2   { $1 }
| OP3   { $1 }
| EQUAL { "=" }
;

any_op:
| OP0   { $1 }
| OP2   { $1 }
| OP3   { $1 }
;

uident:
| UIDENT { { id = $1; id_loc = loc () } }
;

lqualid:
| lident             { Qident $1 }
| uqualid DOT lident { Qdot ($1, $3) }
;

uqualid:
| uident             { Qident $1 }
| uqualid DOT uident { Qdot ($1, $3) }
;

any_qualid:
| ident                { Qident $1 }
| any_qualid DOT ident { Qdot ($1, $3) }
;

tqualid:
| uident                { Qident $1 }
| any_qualid DOT uident { Qdot ($1, $3) }

qualid:
| ident_rich             { Qident $1 }
| uqualid DOT ident_rich { Qdot ($1, $3) }

params:
| /* epsilon */                          { [] }
| LEFTPAR list1_param_sep_comma RIGHTPAR { $2 }
;

param:
| primitive_type              { None, $1 }
| lident COLON primitive_type { Some $1, $3 }
;

list1_param_sep_comma:
| param                             { [$1] }
| param COMMA list1_param_sep_comma { $1 :: $3 }
;

primitive_types:
| /* epsilon */                                   { [] }
| LEFTPAR list1_primitive_type_sep_comma RIGHTPAR { $2 }

logic_type_option:
| /* epsilon */        { None }
| COLON primitive_type { Some $2 }
;

logic_def_option:
| /* epsilon */ { None }
| EQUAL lexpr   { Some $2 }
;

logic_decl:
| LOGIC lident_rich params logic_type_option logic_def_option
  { { ld_loc = loc (); ld_ident = $2; ld_params = $3; 
      ld_type = $4; ld_def = $5; } }
;

list1_logic_decl:
| logic_decl                  %prec prec_decls { [$1] }
| logic_decl list1_logic_decl                  { $1 :: $2 }
;

type_decl:
| TYPE type_args lident typedefn
  { { td_loc = loc (); td_ident = $3; td_params = $2; td_def = $4 } }
;

list1_type_decl:
| type_decl                  %prec prec_decls { [$1] }
| type_decl list1_type_decl                   { $1 :: $2 }
;

inductive_decl:
| INDUCTIVE lident_rich primitive_types inddefn
  { { in_loc = loc (); in_ident = $2; in_params = $3; in_def = $4 } }

list1_inductive_decl:
| inductive_decl                      %prec prec_decls { [$1] }
| inductive_decl list1_inductive_decl                  { $1 :: $2 }
;

decl:
| list1_type_decl
    { TypeDecl $1 }
| list1_logic_decl
    { LogicDecl $1 }
| list1_inductive_decl
    { IndDecl $1 }
| AXIOM uident COLON lexpr
    { PropDecl (loc (), Kaxiom, $2, $4) }
| LEMMA uident COLON lexpr
    { PropDecl (loc (), Klemma, $2, $4) }
| GOAL uident COLON lexpr
    { PropDecl (loc (), Kgoal, $2, $4) }
| USE use
    { UseClone (loc (), $2, None) }
| CLONE use clone_subst
    { UseClone (loc (), $2, Some $3) }
| NAMESPACE uident list0_decl END
    { Namespace (loc (), false, Some $2, $3) }
| NAMESPACE UNDERSCORE list0_decl END
    { Namespace (loc (), false, None, $3) }
| NAMESPACE IMPORT uident list0_decl END
    { Namespace (loc (), false, Some $3, $4) }
| NAMESPACE IMPORT UNDERSCORE list0_decl END
    { Namespace (loc (), false, None, $4) }
;

list1_theory:
| theory 
   { [$1] }
| theory list1_theory 
   { $1 :: $2 }
;

theory:
| THEORY uident list0_decl END 
   { { pt_loc = loc (); pt_name = $2; pt_decl = $3 } }
;

type_args:
| /* epsilon */                                             { [] }
| type_var                                                  { [$1] }
| LEFTPAR type_var COMMA list1_type_var_sep_comma RIGHTPAR  { $2 :: $4 }
;

typedefn:
| /* epsilon */
    { TDabstract }
| EQUAL primitive_type
    { TDalias $2 }
| EQUAL typecases
    { TDalgebraic $2 }
| EQUAL BAR typecases
    { TDalgebraic $3 }
;

typecases:
| typecase                { [$1] }
| typecase BAR typecases  { $1::$3 }
;

typecase:
| uident params { (loc_i 1,$1,$2) }
;

inddefn:
| /* epsilon */       { [] }
| EQUAL bar_ indcases { $3 }
;

indcases:
| indcase               { [$1] }
| indcase BAR indcases  { $1::$3 }
;

indcase:
| uident COLON lexpr { ($1,$3) }
;

primitive_type:
| type_var 
   { PPTtyvar $1 }
| lqualid
   { PPTtyapp ([], $1) }
| primitive_type lqualid
   { PPTtyapp ([$1], $2) }
| LEFTPAR primitive_type COMMA list1_primitive_type_sep_comma RIGHTPAR lqualid
   { PPTtyapp ($2 :: $4, $6) }
;

list1_primitive_type_sep_comma:
| primitive_type                                      { [$1] }
| primitive_type COMMA list1_primitive_type_sep_comma { $1 :: $3 }
;

lexpr:
| lexpr ARROW lexpr 
   { infix_pp $1 PPimplies $3 }
| lexpr LRARROW lexpr 
   { infix_pp $1 PPiff $3 }
| lexpr OR lexpr 
   { infix_pp $1 PPor $3 }
| lexpr AND lexpr 
   { infix_pp $1 PPand $3 }
| NOT lexpr 
   { prefix_pp PPnot $2 }
| lexpr EQUAL lexpr 
   { let id = { id = infix "="; id_loc = loc_i 2 } in
     mk_pp (PPapp (Qident id, [$1; $3])) }
| lexpr OP0 lexpr 
   { let id = { id = infix $2; id_loc = loc_i 2 } in
     mk_pp (PPapp (Qident id, [$1; $3])) }
| lexpr OP1 lexpr 
   { let id = { id = infix $2; id_loc = loc_i 2 } in
     mk_pp (PPapp (Qident id, [$1; $3])) }
| lexpr OP2 lexpr 
   { let id = { id = infix $2; id_loc = loc_i 2 } in
     mk_pp (PPapp (Qident id, [$1; $3])) }
| lexpr OP3 lexpr 
   { let id = { id = infix $2; id_loc = loc_i 2 } in
     mk_pp (PPapp (Qident id, [$1; $3])) }
| any_op lexpr %prec unary_op
   { let id = { id = prefix $1; id_loc = loc_i 2 } in
     mk_pp (PPapp (Qident id, [$2])) }
/*
| lexpr any_op %prec unary_op
   { let id = { id = postfix $2; id_loc = loc_i 2 } in
     mk_pp (PPapp (Qident id, [$1])) }
*/
| qualid
   { mk_pp (PPvar $1) }
| qualid LEFTPAR list1_lexpr_sep_comma RIGHTPAR
   { mk_pp (PPapp ($1, $3)) }
| IF lexpr THEN lexpr ELSE lexpr %prec prec_if 
   { mk_pp (PPif ($2, $4, $6)) }
| FORALL list1_uquant_sep_comma triggers DOT lexpr %prec prec_quant
   { mk_pp (PPquant (PPforall, $2, $3, $5)) }
| EXISTS list1_uquant_sep_comma triggers DOT lexpr %prec prec_quant
   { mk_pp (PPquant (PPexists, $2, $3, $5)) }
| INTEGER
   { mk_pp (PPconst (Term.ConstInt $1)) }
| FLOAT
   { mk_pp (PPconst (Term.ConstReal $1)) }
| TRUE
   { mk_pp PPtrue }
| FALSE
   { mk_pp PPfalse }    
| LEFTPAR lexpr RIGHTPAR
   { $2 }
| STRING lexpr %prec prec_named
   { mk_pp (PPnamed ($1, $2)) }
| LET lident EQUAL lexpr IN lexpr 
   { mk_pp (PPlet ($2, $4, $6)) }
| MATCH lexpr WITH bar_ match_cases END
   { mk_pp (PPmatch ($2, $5)) }
| lexpr COLON primitive_type
   { mk_pp (PPcast ($1, $3)) }
;

list1_uquant_sep_comma:
| uquant                              { [$1] }
| uquant COMMA list1_uquant_sep_comma { $1::$3 }

uquant:
| list1_lident_sep_comma COLON primitive_type { $1,$3 }

match_cases:
| match_case                  { [$1] }
| match_case BAR match_cases  { $1::$3 }
;

match_case:
| pattern ARROW lexpr { ($1,$3) }
;

list1_pat_sep_comma:
| pattern                           { [$1] }
| pattern COMMA list1_pat_sep_comma { $1::$3 }

pattern:
| UNDERSCORE                                    { mk_pat (PPpwild) }
| lident                                        { mk_pat (PPpvar $1) }
| uqualid                                       { mk_pat (PPpapp ($1, [])) }
| uqualid LEFTPAR list1_pat_sep_comma RIGHTPAR  { mk_pat (PPpapp ($1, $3)) }
| pattern AS lident                             { mk_pat (PPpas ($1,$3)) }
;

triggers:
| /* epsilon */                         { [] }
| LEFTSQ list1_trigger_sep_bar RIGHTSQ  { $2 }
;

list1_trigger_sep_bar:
| trigger                           { [$1] }
| trigger BAR list1_trigger_sep_bar { $1 :: $3 }
;

trigger:
  list1_lexpr_sep_comma { $1 }
;

list1_lexpr_sep_comma:
| lexpr                             { [$1] }
| lexpr COMMA list1_lexpr_sep_comma { $1 :: $3 }
;

type_var:
| QUOTE ident { $2 }
;

list1_type_var_sep_comma:
| type_var                                { [$1] }
| type_var COMMA list1_type_var_sep_comma { $1 :: $3 }
;

bar_:
| /* epsilon */ { () }
| BAR           { () }
;

list1_lident_sep_comma:
| lident                              { [$1] }
| lident COMMA list1_lident_sep_comma { $1 :: $3 }
;

use:
| imp_exp tqualid              
    { { use_theory = $2; use_as = None; use_imp_exp = $1 } }
| imp_exp tqualid AS uident
    { { use_theory = $2; use_as = Some (Some $4); use_imp_exp = $1 } }
| imp_exp tqualid AS UNDERSCORE
    { { use_theory = $2; use_as = Some None; use_imp_exp = $1 } }
;

imp_exp:
| IMPORT        { Import }
| EXPORT        { Export }
| /* epsilon */ { Nothing }
;

clone_subst:
| /* epsilon */          { [] } 
| WITH list1_comma_subst { $2 }
;

list1_comma_subst:
| subst                         { [$1] }
| subst COMMA list1_comma_subst { $1 :: $3 } 
;

subst:
| TYPE  qualid EQUAL qualid { CStsym ($2, $4) }
| LOGIC qualid EQUAL qualid { CSlsym ($2, $4) }
| LEMMA qualid              { CSlemma $2 }
| GOAL  qualid              { CSgoal  $2 }
;

