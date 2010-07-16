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

  let infix_ppl loc a i b = mk_ppl loc (PPbinop (a, i, b))
  let infix_pp a i b = infix_ppl (loc ()) a i b

  let prefix_ppl loc p a = mk_ppl loc (PPunop (p, a))
  let prefix_pp p a = prefix_ppl (loc ()) p a

  let infix s = "infix " ^ s
  let prefix s = "prefix " ^ s

  let () = Exn_printer.register
    (fun fmt exn -> match exn with
      | Parsing.Parse_error -> Format.fprintf fmt "syntax error"
      | _ -> raise exn
    )

%}

/* Tokens */

%token <string> LIDENT UIDENT
%token <string> INTEGER
%token <string> OP1 OP2 OP3 OP4 OPPREF
%token <Ptree.real_constant> FLOAT
%token <string> STRING

/* keywords */

%token AND AS AXIOM CLONE
%token ELSE END EPSILON EXISTS EXPORT FALSE FORALL
%token GOAL IF IMPORT IN INDUCTIVE LEMMA
%token LET LOGIC MATCH META NAMESPACE NOT PROP OR
%token THEN THEORY TRUE TYPE USE WITH

/* symbols */

%token ARROW ASYM_AND ASYM_OR
%token BAR
%token COLON COMMA
%token DOT EQUAL
%token LEFTPAR LEFTPAR_STAR_RIGHTPAR LEFTSQ
%token LRARROW
%token QUOTE
%token RIGHTPAR RIGHTSQ
%token UNDERSCORE

%token EOF


/* Precedences */

%nonassoc prec_decls
%nonassoc LOGIC TYPE INDUCTIVE

%nonassoc DOT ELSE IN
%nonassoc COLON

%nonassoc prec_named
%right ARROW LRARROW
%right OR ASYM_OR
%right AND ASYM_AND
%nonassoc NOT
%left EQUAL OP1
%left OP2
%left OP3
%left OP4
%nonassoc prefix_op
%nonassoc OPPREF

/* Entry points */

%type <Ptree.lexpr> lexpr
%start lexpr
%type <Ptree.decl list> list0_decl
%start list0_decl
%type <Ptree.logic_file> logic_file
%start logic_file
%%

/* File, theory, declaration */

logic_file:
| list1_theory EOF  { $1 }
| EOF               { [] }
;

list1_theory:
| theory                { [$1] }
| theory list1_theory   { $1 :: $2 }
;

theory:
| THEORY uident list0_decl END
   { { pt_loc = loc (); pt_name = $2; pt_decl = $3 } }
;

list0_decl:
| /* epsilon */    { [] }
| decl list0_decl  { $1 :: $2 }
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
    { Namespace (loc (), true, Some $3, $4) }
| NAMESPACE IMPORT UNDERSCORE list0_decl END
    { Namespace (loc (), true, None, $4) }
| META ident list1_meta_arg_sep_comma
    { Meta (loc (), $2, $3) }
| META STRING list1_meta_arg_sep_comma
    { Meta (loc (), { id = $2; id_loc = loc_i 2 }, $3) }
;

/* Use and clone */

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

/* Meta args */

list1_meta_arg_sep_comma:
| meta_arg                                { [$1] }
| meta_arg COMMA list1_meta_arg_sep_comma { $1 :: $3 }
;

meta_arg:
| TYPE  qualid { PMAts  $2 }
| LOGIC qualid { PMAls  $2 }
| PROP  qualid { PMApr  $2 }
| STRING       { PMAstr $1 }
| INTEGER      { PMAint $1 }
;

/* Type declarations */

list1_type_decl:
| type_decl                  %prec prec_decls { [$1] }
| type_decl list1_type_decl                   { $1 :: $2 }
;

type_decl:
| TYPE lident type_args typedefn
  { { td_loc = loc (); td_ident = $2; td_params = $3; td_def = $4 } }
;

type_args:
| /* epsilon */      { [] }
| type_var type_args { $1 :: $2 }
;

typedefn:
| /* epsilon */           { TDabstract }
| EQUAL primitive_type    { TDalias $2 }
| EQUAL typecases         { TDalgebraic $2 }
| EQUAL BAR typecases     { TDalgebraic $3 }
;

typecases:
| typecase                { [$1] }
| typecase BAR typecases  { $1::$3 }
;

typecase:
| uident params   { (loc_i 1,$1,$2) }
;

/* Logic declarations */

list1_logic_decl:
| logic_decl                  %prec prec_decls { [$1] }
| logic_decl list1_logic_decl                  { $1 :: $2 }
;

logic_decl:
| LOGIC lident_rich params logic_type_option logic_def_option
  { { ld_loc = loc (); ld_ident = $2; ld_params = $3;
      ld_type = $4; ld_def = $5; } }
;

logic_type_option:
| /* epsilon */        { None }
| COLON primitive_type { Some $2 }
;

logic_def_option:
| /* epsilon */ { None }
| EQUAL lexpr   { Some $2 }
;

/* Inductive declarations */

list1_inductive_decl:
| inductive_decl                      %prec prec_decls { [$1] }
| inductive_decl list1_inductive_decl                  { $1 :: $2 }
;

inductive_decl:
| INDUCTIVE lident_rich params inddefn
  { { in_loc = loc (); in_ident = $2; in_params = $3; in_def = $4 } }

inddefn:
| /* epsilon */       { [] }
| EQUAL bar_ indcases { $3 }
;

indcases:
| indcase               { [$1] }
| indcase BAR indcases  { $1::$3 }
;

indcase:
| uident COLON lexpr { (loc (),$1,$3) }
;

/* Type expressions */

primitive_type:
| primitive_type_arg           { $1 }
| lqualid primitive_type_args  { PPTtyapp ($2, $1) }
;

primitive_type_non_lident:
| primitive_type_arg_non_lident  { $1 }
| lq_uident primitive_type_args  { PPTtyapp ($2, $1) }
;

primitive_type_args:
| primitive_type_arg                      { [$1] }
| primitive_type_arg primitive_type_args  { $1 :: $2 }
;

primitive_type_arg:
| lq_lident                      { PPTtyapp ([], $1) }
| primitive_type_arg_non_lident  { $1 }
;

primitive_type_arg_non_lident:
| lq_uident
   { PPTtyapp ([], $1) }
| type_var
   { PPTtyvar $1 }
| LEFTPAR primitive_type COMMA list1_primitive_type_sep_comma RIGHTPAR
   { PPTtuple ($2 :: $4) }
| LEFTPAR RIGHTPAR
   { PPTtuple [] }
| LEFTPAR primitive_type RIGHTPAR
   { $2 }
;

list1_primitive_type_sep_comma:
| primitive_type                                      { [$1] }
| primitive_type COMMA list1_primitive_type_sep_comma { $1 :: $3 }
;

type_var:
| QUOTE ident { $2 }
;

/* Logic expressions */

lexpr:
| lexpr ARROW lexpr
   { infix_pp $1 PPimplies $3 }
| lexpr LRARROW lexpr
   { infix_pp $1 PPiff $3 }
| lexpr OR lexpr
   { infix_pp $1 PPor $3 }
| lexpr ASYM_OR lexpr
   { mk_pp (PPnamed ("asym_split", infix_pp $1 PPor $3)) }
| lexpr AND lexpr
   { infix_pp $1 PPand $3 }
| lexpr ASYM_AND lexpr
   { mk_pp (PPnamed ("asym_split", infix_pp $1 PPand $3)) }
| NOT lexpr
   { prefix_pp PPnot $2 }
| lexpr EQUAL lexpr
   { let id = { id = infix "="; id_loc = loc_i 2 } in
     mk_pp (PPinfix ($1, id, $3)) }
| lexpr OP1 lexpr
   { let id = { id = infix $2; id_loc = loc_i 2 } in
     mk_pp (PPinfix ($1, id, $3)) }
| lexpr OP2 lexpr
   { let id = { id = infix $2; id_loc = loc_i 2 } in
     mk_pp (PPinfix ($1, id, $3)) }
| lexpr OP3 lexpr
   { let id = { id = infix $2; id_loc = loc_i 2 } in
     mk_pp (PPinfix ($1, id, $3)) }
| lexpr OP4 lexpr
   { let id = { id = infix $2; id_loc = loc_i 2 } in
     mk_pp (PPinfix ($1, id, $3)) }
| any_op lexpr %prec prefix_op
   { let id = { id = prefix $1; id_loc = loc_i 2 } in
     mk_pp (PPapp (Qident id, [$2])) }
| qualid list1_lexpr_arg
   { mk_pp (PPapp ($1, $2)) }
| IF lexpr THEN lexpr ELSE lexpr
   { mk_pp (PPif ($2, $4, $6)) }
| FORALL list1_param_var_sep_comma triggers DOT lexpr
   { mk_pp (PPquant (PPforall, $2, $3, $5)) }
| EXISTS list1_param_var_sep_comma triggers DOT lexpr
   { mk_pp (PPquant (PPexists, $2, $3, $5)) }
| STRING lexpr %prec prec_named
   { mk_pp (PPnamed ($1, $2)) }
| LET pattern EQUAL lexpr IN lexpr
   { match $2.pat_desc with
       | PPpvar id -> mk_pp (PPlet (id, $4, $6))
       | _ -> mk_pp (PPmatch ([$4], [[$2], $6])) }
| MATCH list1_lexpr_sep_comma WITH bar_ match_cases END
   { mk_pp (PPmatch ($2, $5)) }
| EPSILON lident COLON primitive_type DOT lexpr
   { mk_pp (PPeps ($2, $4, $6)) }
| lexpr COLON primitive_type
   { mk_pp (PPcast ($1, $3)) }
| lexpr_arg
   { $1 }
;

list1_lexpr_arg:
| lexpr_arg                 { [$1] }
| lexpr_arg list1_lexpr_arg { $1::$2 }

lexpr_arg:
| qualid
   { mk_pp (PPvar $1) }
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
| LEFTPAR RIGHTPAR
   { mk_pp (PPtuple []) }
| LEFTPAR lexpr COMMA list1_lexpr_sep_comma RIGHTPAR
   { mk_pp (PPtuple ($2 :: $4)) }
| OPPREF lexpr_arg
   { let id = { id = prefix $1; id_loc = loc_i 2 } in
     mk_pp (PPapp (Qident id, [$2])) }

/* Triggers */

triggers:
| /* epsilon */                         { [] }
| LEFTSQ list1_trigger_sep_bar RIGHTSQ  { $2 }
;

list1_trigger_sep_bar:
| trigger                           { [$1] }
| trigger BAR list1_trigger_sep_bar { $1 :: $3 }
;

trigger:
| list1_lexpr_sep_comma { $1 }
;

list1_lexpr_sep_comma:
| lexpr                             { [$1] }
| lexpr COMMA list1_lexpr_sep_comma { $1 :: $3 }
;

/* Match expressions */

match_cases:
| match_case                  { [$1] }
| match_case BAR match_cases  { $1::$3 }
;

match_case:
| list1_pat_sep_comma ARROW lexpr { ($1,$3) }
;

list1_pat_sep_comma:
| pattern                           { [$1] }
| pattern COMMA list1_pat_sep_comma { $1::$3 }

pattern:
| pat_arg               { $1 }
| uqualid list1_pat_arg { mk_pat (PPpapp ($1, $2)) }
| pattern AS lident     { mk_pat (PPpas ($1,$3)) }

list1_pat_arg:
| pat_arg               { [$1] }
| pat_arg list1_pat_arg { $1::$2 }

pat_arg:
| UNDERSCORE
   { mk_pat (PPpwild) }
| lident
   { mk_pat (PPpvar $1) }
| uqualid
   { mk_pat (PPpapp ($1, [])) }
| LEFTPAR pattern RIGHTPAR
   { $2 }
| LEFTPAR RIGHTPAR
   { mk_pat (PPptuple []) }
| LEFTPAR pattern COMMA list1_pat_sep_comma RIGHTPAR
   { mk_pat (PPptuple ($2 :: $4)) }
;

/* Parameters */

params:
| /* epsilon */   { [] }
| param params    { $1 @ $2 }
;

param:
| LEFTPAR param_var RIGHTPAR
   { $2 }
| LEFTPAR param_type RIGHTPAR
   { [None, $2] }
| LEFTPAR param_type COMMA list1_primitive_type_sep_comma RIGHTPAR
   { [None, PPTtuple ($2::$4)] }
| LEFTPAR RIGHTPAR
   { [None, PPTtuple []] }
| type_var
   { [None, PPTtyvar $1] }
| lqualid
   { [None, PPTtyapp ([], $1)] }
;

param_type:
| lident param_type_cont
   { PPTtyapp ($2, Qident $1) }
| lident list1_lident param_type_cont
   { let id2ty i = PPTtyapp ([], Qident i) in
     PPTtyapp (List.map id2ty $2 @ $3, Qident $1) }
| primitive_type_non_lident
   { $1 }
;

param_type_cont:
| /* epsilon */                                      { [] }
| primitive_type_arg_non_lident                      { [$1] }
| primitive_type_arg_non_lident primitive_type_args  { $1 :: $2 }
;

list1_param_var_sep_comma:
| param_var                                  { $1 }
| param_var COMMA list1_param_var_sep_comma  { $1 @ $3 }
;

param_var:
| list1_lident COLON primitive_type
   { List.map (fun id -> (Some id, $3)) $1 }
;

list1_lident:
| lident               { [$1] }
| lident list1_lident  { $1 :: $2 }
;

/* Idents */

ident:
| uident { $1 }
| lident { $1 }
;

ident_rich:
| uident      { $1 }
| lident_rich { $1 }
;

lident_rich:
| lident
    { $1 }
| LEFTPAR lident_op RIGHTPAR
    { { id = infix $2; id_loc = loc () } }
| LEFTPAR_STAR_RIGHTPAR
    { { id = infix "*"; id_loc = loc () } }
| LEFTPAR lident_op UNDERSCORE RIGHTPAR
    { { id = prefix $2; id_loc = loc () } }
| LEFTPAR OPPREF RIGHTPAR
    { { id = prefix $2; id_loc = loc () } }
;

lident:
| LIDENT  { { id = $1; id_loc = loc () } }
;

lident_op:
| OP1   { $1 }
| OP2   { $1 }
| OP3   { $1 }
| OP4   { $1 }
| EQUAL { "=" }
;

any_op:
| OP1   { $1 }
| OP2   { $1 }
| OP3   { $1 }
| OP4   { $1 }
;

uident:
| UIDENT { { id = $1; id_loc = loc () } }
;

lq_lident:
| lident             { Qident $1 }
;

lq_uident:
| uqualid DOT lident { Qdot ($1, $3) }
;

lqualid:
| lq_lident { $1 }
| lq_uident { $1 }
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

/* Misc */

bar_:
| /* epsilon */ { () }
| BAR           { () }
;

