/**************************************************************************/
/*                                                                        */
/*  Copyright (C) 2010-2011                                               */
/*    François Bobot                                                      */
/*    Jean-Christophe Filliâtre                                           */
/*    Claude Marché                                                       */
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
open Parsing
open Tptp_ast

let loc () = (symbol_start_pos (), symbol_end_pos ())
let floc () = Loc.extract (loc ())

let loc_i i = (rhs_start_pos i, rhs_end_pos i)
let floc_i i = Loc.extract (loc_i i)
let loc_ij i j = (rhs_start_pos i, rhs_end_pos j)
let floc_ij i j = Loc.extract (loc_ij i j)

let mk_ty n = { ty_node = n ; ty_loc = floc () }
let mk_term n = { t_node = n ; t_loc = floc () }
let mk_formula n = { f_node = n ; f_loc = floc () }
let mk_binding n = { b_node = n ; b_loc = floc () }

let () = Exn_printer.register (fun fmt exn -> match exn with
  | Parsing.Parse_error -> Format.fprintf fmt "syntax error"
  | _ -> raise exn)
%}

/* tokens */

%token <string> LWORD UWORD DWORD
%token <string> SINGLE_QUOTED DISTINCT_OBJECT
%token <num_integer> INTNUM
%token <num_rational> RATNUM
%token <num_real> REALNUM

/* keywords */

%token ASSUMPTION AXIOM CNF CONJECTURE DEFINITION FOF
%token HYPOTHESIS INCLUDE LEMMA NEGATED_CONJECTURE TFF
%token THEOREM TYPE

/* symbols */

%token DOT COMMA COLON LEFTPAR RIGHTPAR LEFTSQ RIGHTSQ
%token LONGARROW LARROW RARROW LRARROW NLRARROW NAMP NBAR
%token TILDE EQUAL NEQUAL STAR GT PI BANG QUES

%token SLASH_STAR_SLASH EOF

/* entry points */

%type <tptp_file> tptp_file
%start tptp_file
%%

tptp_file:
| list0_input EOF { $1 }
;

list0_input:
| /* epsilon */     { [] }
| input list0_input { $1 :: $2 }
;

input:
| kind LEFTPAR name COMMA role COMMA top_formula annotation RIGHTPAR DOT
  { Formula ($1, $3, $5, $7, floc ()) }
| INCLUDE LEFTPAR SINGLE_QUOTED formula_selection RIGHTPAR DOT
  { Include ($3, $4, floc ()) }
;

kind:
| TFF { TFF }
| FOF { FOF }
| CNF { CNF }
;

role:
| AXIOM               { Axiom }
| HYPOTHESIS          { Hypothesis }
| DEFINITION          { Definition }
| ASSUMPTION          { Assumption }
| LEMMA               { Lemma }
| THEOREM             { Theorem }
| CONJECTURE          { Conjecture }
| NEGATED_CONJECTURE  { Negated_conjecture }
| TYPE                { Type }
| LWORD               { Unknown $1 }
;

top_formula:
| logic_formula { $1 }
| typed_atom    { $1 }
| sequent       { $1 }
;

/* typed_atom */

typed_atom:
| untyped_atom COLON top_type { TypedAtom ($1,$3) }
| LEFTPAR typed_atom RIGHTPAR { $2 }
;

untyped_atom:
| atomic_word { $1 }
/*
| DDWORD      { $1 }
*/
;

top_type:
| atomic_type     { [],[],$1 }
| mapping_type    { let l,r = $1 in [],l,r }
| quantified_type { $1 } 
;

quantified_type:
| PI LEFTSQ varlist RIGHTSQ COLON monotype  { let l,r = $6 in $3,l,r }
| LEFTPAR quantified_type RIGHTPAR          { $2 }
;

monotype:
| atomic_type                   { [],$1 }
| LEFTPAR mapping_type RIGHTPAR { $2 }
;

mapping_type:
| unitary_type GT atomic_type   { $1,$2 }
| LEFTPAR mapping_type RIGHTPAR { $2 }
;

unitary_type:
| atomic_type                 { [1] }
| LEFTPAR xprod_type RIGHTPAR { $2 }
;

xprod_type:
| atomic_type STAR atomic_type  { [$1;$2] }
| xprod_type STAR atomic_type   { $1 @ [$2] }
| LEFTPAR xprod_type RIGHTPAR   { $2 }
;

/* atomic type */

atomic_type:
| variable                                        { mk_ty (TVar $1) } 
| atomic_word                                     { mk_ty (TConstr ($1,[])) }
| atomic_word LEFTPAR list1_atomic_type RIGHTPAR  { mk_ty (TConstr ($1,$3)) }
| defined_type                                    { mk_ty (TDef $1) }
;

list1_atomic_type:
| atomic_type                         { [$1] }
| atomic_type COMMA list1_atomic_type { $1 :: $3 }
;

defined_type

/* sequent */

sequent:
| tuple LONGARROW tuple     { Sequent ($1,$3) }
| LEFTPAR sequent RIGHTPAR  { $2 }
;

tuple:
| LEFTSQ RIGHTSQ                      { [] }
| LEFTSQ list1_logic_formula RIGHTSQ  { $2 }
;

list1_logic_formula:
| logic_formula                           { [$1] }
| logic_formula COMMA list1_logic_formula { $1 :: $3 }
;

/* misc */

number:
| INTNUM  { Nint $1 }
| RATNUM  { Nrat $1 }
| REALNUM { Nreal $1 }
;

atomic_word:
| LWORD         { $1 }
| SINGLE_QUOTED { $1 }
;

/* TODO: add support for annotations */
annotation:
| /* epsilon */ { () }
;

formula_selection:
| /* epsilon */                   { [] }
| COMMA LEFTSQ list1_name RIGHTSQ { $3 }
;

list1_name:
| name                  { [$1] }
| name COMMA list1_name { $1 :: $3 }
;

name:
| atomic_word   { $1 }
| INTNUM        { $1 }
;

%

/* File, theory, namespace */

list0_theory:
| /* epsilon */         { () }
| theory list0_theory   { () }
;

theory_head:
| THEORY uident labels  { Incremental.open_theory (add_lab $2 $3) }
;

theory:
| theory_head list0_decl END  { Incremental.close_theory (floc_i 1) }
;

list0_decl:
| /* epsilon */        { () }
| new_decl list0_decl  { () }
;

new_decl:
| decl
   { Incremental.new_decl $1 }
| namespace_head namespace_import namespace_name list0_decl END
   { Incremental.close_namespace (floc_i 3) $2 $3 }
;

namespace_head:
| NAMESPACE  { Incremental.open_namespace () }
;

namespace_import:
| /* epsilon */  { false }
| IMPORT         { true }
;

namespace_name:
| uident      { Some $1 }
| UNDERSCORE  { None }
;

/* Declaration */

decl:
| TYPE list1_type_decl
    { TypeDecl $2 }
| FUNCTION list1_logic_decl_function
    { LogicDecl $2 }
| PREDICATE list1_logic_decl_predicate
    { LogicDecl $2 }
| INDUCTIVE list1_inductive_decl
    { IndDecl $2 }
| AXIOM ident labels COLON lexpr
    { PropDecl (floc (), Kaxiom, add_lab $2 $3, $5) }
| LEMMA ident labels COLON lexpr
    { PropDecl (floc (), Klemma, add_lab $2 $3, $5) }
| GOAL ident labels COLON lexpr
    { PropDecl (floc (), Kgoal, add_lab $2 $3, $5) }
| USE use
    { UseClone (floc (), $2, None) }
| CLONE use clone_subst
    { UseClone (floc (), $2, Some $3) }
| META sident list1_meta_arg_sep_comma
    { Meta (floc (), $2, $3) }
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
| NAMESPACE ns     EQUAL ns     { CSns   ($2, $4) }
| TYPE      qualid EQUAL qualid { CStsym ($2, $4) }
| FUNCTION  qualid EQUAL qualid { CSfsym ($2, $4) }
| PREDICATE qualid EQUAL qualid { CSpsym ($2, $4) }
| LEMMA     qualid              { CSlemma $2 }
| GOAL      qualid              { CSgoal  $2 }
;

ns:
| uqualid { Some $1 }
| DOT     { None }
;

/* Meta args */

list1_meta_arg_sep_comma:
| meta_arg                                { [$1] }
| meta_arg COMMA list1_meta_arg_sep_comma { $1 :: $3 }
;

meta_arg:
| TYPE      qualid { PMAts  $2 }
| FUNCTION  qualid { PMAfs  $2 }
| PREDICATE qualid { PMAps  $2 }
| PROP      qualid { PMApr  $2 }
| STRING           { PMAstr $1 }
| INTEGER          { PMAint (small_integer $1) }
;

/* Type declarations */

list1_type_decl:
| type_decl                       { [$1] }
| type_decl WITH list1_type_decl  { $1 :: $3 }
;

type_decl:
| lident labels type_args typedefn
  { let model, def = $4 in
    { td_loc = floc (); td_ident = add_lab $1 $2;
      td_params = $3; td_model = model; td_def = def } }
;

type_args:
| /* epsilon */             { [] }
| type_var labels type_args { add_lab $1 $2 :: $3 }
;

typedefn:
| /* epsilon */                 { false, TDabstract }
| equal_model primitive_type    { $1, TDalias $2 }
| equal_model typecases         { $1, TDalgebraic $2 }
| equal_model BAR typecases     { $1, TDalgebraic $3 }
| equal_model record_type       { $1, TDrecord $2 }
;

equal_model:
| EQUAL { false }
| MODEL { true }
;

record_type:
| LEFTREC list1_record_field opt_semicolon RIGHTREC { List.rev $2 }
;

list1_record_field:
| record_field                              { [$1] }
| list1_record_field SEMICOLON record_field { $3 :: $1 }
;

record_field:
| opt_mutable lident labels COLON primitive_type
   { floc (), $1, add_lab $2 $3, $5 }
;

typecases:
| typecase                { [$1] }
| typecase BAR typecases  { $1::$3 }
;

typecase:
| uident labels params   { (floc (), add_lab $1 $2, $3) }
;

/* Logic declarations */

list1_logic_decl_function:
| logic_decl_function                        { [$1] }
| logic_decl_function WITH list1_logic_decl  { $1 :: $3 }
;

list1_logic_decl_predicate:
| logic_decl_predicate                        { [$1] }
| logic_decl_predicate WITH list1_logic_decl  { $1 :: $3 }
;

list1_logic_decl:
| logic_decl                        { [$1] }
| logic_decl WITH list1_logic_decl  { $1 :: $3 }
;

logic_decl_function:
| lident_rich labels params COLON primitive_type logic_def_option
  { { ld_loc = floc (); ld_ident = add_lab $1 $2;
      ld_params = $3; ld_type = Some $5; ld_def = $6 } }
;

logic_decl_predicate:
| lident_rich labels params logic_def_option
  { { ld_loc = floc (); ld_ident = add_lab $1 $2;
      ld_params = $3; ld_type = None; ld_def = $4 } }
;

logic_decl:
| lident_rich labels params logic_type_option logic_def_option
  { { ld_loc = floc (); ld_ident = add_lab $1 $2;
      ld_params = $3; ld_type = $4; ld_def = $5 } }
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
| inductive_decl                            { [$1] }
| inductive_decl WITH list1_inductive_decl  { $1 :: $3 }
;

inductive_decl:
| lident_rich labels params inddefn
  { { in_loc = floc (); in_ident = add_lab $1 $2;
      in_params = $3; in_def = $4 } }
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
| ident labels COLON lexpr { (floc (), add_lab $1 $2, $4) }
;

/* Type expressions */

primitive_type:
| primitive_type_arg           { $1 }
| lqualid primitive_type_args  { PPTtyapp ($2, $1) }
;

primitive_type_non_lident:
| primitive_type_arg_non_lident           { $1 }
| uqualid DOT lident primitive_type_args  { PPTtyapp ($4, Qdot ($1, $3)) }
;

primitive_type_args:
| primitive_type_arg                      { [$1] }
| primitive_type_arg primitive_type_args  { $1 :: $2 }
;

primitive_type_arg:
| lident                         { PPTtyapp ([], Qident $1) }
| primitive_type_arg_non_lident  { $1 }
;

primitive_type_arg_non_lident:
| uqualid DOT lident
   { PPTtyapp ([], Qdot ($1, $3)) }
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
| QUOTE lident { $2 }
;

/* Logic expressions */

lexpr:
| lexpr ARROW lexpr
   { infix_pp $1 PPimplies $3 }
| lexpr LRARROW lexpr
   { infix_pp $1 PPiff $3 }
| lexpr OR lexpr
   { infix_pp $1 PPor $3 }
| lexpr BARBAR lexpr
   { mk_pp (PPnamed (Lstr Term.asym_label, infix_pp $1 PPor $3)) }
| lexpr AND lexpr
   { infix_pp $1 PPand $3 }
| lexpr AMPAMP lexpr
   { mk_pp (PPnamed (Lstr Term.asym_label, infix_pp $1 PPand $3)) }
| NOT lexpr
   { prefix_pp PPnot $2 }
| lexpr EQUAL lexpr
   { mk_l_infix $1 "=" $3 }
| lexpr LTGT lexpr
   { prefix_pp PPnot (mk_l_infix $1 "=" $3) }
| lexpr OP1 lexpr
   { mk_l_infix $1 $2 $3 }
| lexpr OP2 lexpr
   { mk_l_infix $1 $2 $3 }
| lexpr OP3 lexpr
   { mk_l_infix $1 $2 $3 }
| lexpr OP4 lexpr
   { mk_l_infix $1 $2 $3 }
| prefix_op lexpr %prec prec_prefix_op
   { mk_l_prefix $1 $2 }
| qualid list1_lexpr_arg
   { mk_pp (PPapp ($1, $2)) }
| IF lexpr THEN lexpr ELSE lexpr
   { mk_pp (PPif ($2, $4, $6)) }
| quant list1_param_var_sep_comma triggers DOT lexpr
   { mk_pp (PPquant ($1, $2, $3, $5)) }
| label lexpr %prec prec_named
   { mk_pp (PPnamed ($1, $2)) }
| LET pattern EQUAL lexpr IN lexpr
   { match $2.pat_desc with
       | PPpvar id -> mk_pp (PPlet (id, $4, $6))
       | _ -> mk_pp (PPmatch ($4, [$2, $6])) }
| MATCH lexpr WITH bar_ match_cases END
   { mk_pp (PPmatch ($2, $5)) }
| MATCH lexpr COMMA list1_lexpr_sep_comma WITH bar_ match_cases END
   { mk_pp (PPmatch (mk_pp (PPtuple ($2::$4)), $7)) }
| EPSILON lident labels COLON primitive_type DOT lexpr
   { mk_pp (PPeps (add_lab $2 $3, $5, $7)) }
| lexpr COLON primitive_type
   { mk_pp (PPcast ($1, $3)) }
| lexpr_arg
   { $1 }
;

list1_field_value:
| field_value                             { [$1] }
| list1_field_value SEMICOLON field_value { $3 :: $1 }
;

field_value:
| lqualid EQUAL lexpr { $1, $3 }
;

list1_lexpr_arg:
| lexpr_arg                 { [$1] }
| lexpr_arg list1_lexpr_arg { $1::$2 }
;

constant:
| INTEGER   { Term.ConstInt $1 }
| FLOAT     { Term.ConstReal $1 }
;

lexpr_arg:
| qualid            { mk_pp (PPvar $1) }
| constant          { mk_pp (PPconst $1) }
| TRUE              { mk_pp PPtrue }
| FALSE             { mk_pp PPfalse }
| OPPREF lexpr_arg  { mk_l_prefix $1 $2 }
| lexpr_sub         { $1 }
| QUOTE uident      { mk_pp (PPvar (Qident (quote $2))) }
;

lexpr_dot:
| lqualid_copy      { mk_pp (PPvar $1) }
| OPPREF lexpr_dot  { mk_l_prefix $1 $2 }
| lexpr_sub         { $1 }
;

lexpr_sub:
| lexpr_dot DOT lqualid_rich
   { mk_pp (PPapp ($3, [$1])) }
| LEFTPAR lexpr RIGHTPAR
   { $2 }
| LEFTPAR RIGHTPAR
   { mk_pp (PPtuple []) }
| LEFTPAR lexpr COMMA list1_lexpr_sep_comma RIGHTPAR
   { mk_pp (PPtuple ($2 :: $4)) }
| LEFTREC list1_field_value opt_semicolon RIGHTREC
   { mk_pp (PPrecord (List.rev $2)) }
| LEFTREC lexpr_arg WITH list1_field_value opt_semicolon RIGHTREC
   { mk_pp (PPupdate ($2, List.rev $4)) }
| lexpr_arg LEFTSQ lexpr RIGHTSQ
   { mk_l_mixfix2 "[]" $1 $3 }
| lexpr_arg LEFTSQ lexpr LARROW lexpr RIGHTSQ
   { mk_l_mixfix3 "[<-]" $1 $3 $5 }
;

quant:
| FORALL  { PPforall }
| EXISTS  { PPexists }
| LAMBDA  { PPlambda }
| FUNC    { PPfunc }
| PRED    { PPpred }
;

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
| pattern ARROW lexpr   { ($1,$3) }
;

pattern:
| pat_conj              { $1 }
| pat_conj BAR pattern  { mk_pat (PPpor ($1, $3)) }
;

pat_conj:
| pat_uni                      { $1 }
| pat_uni COMMA list1_pat_uni  { mk_pat (PPptuple ($1::$3)) }
;

list1_pat_uni:
| pat_uni                      { [$1] }
| pat_uni COMMA list1_pat_uni  { $1::$3 }
;

pat_uni:
| pat_arg                   { $1 }
| uqualid list1_pat_arg     { mk_pat (PPpapp ($1, $2)) }
| pat_uni AS lident labels  { mk_pat (PPpas ($1, add_lab $3 $4)) }
;

list1_pat_arg:
| pat_arg                { [$1] }
| pat_arg list1_pat_arg  { $1::$2 }
;

pat_arg:
| UNDERSCORE                { mk_pat (PPpwild) }
| lident labels             { mk_pat (PPpvar (add_lab $1 $2)) }
| uqualid                   { mk_pat (PPpapp ($1, [])) }
| LEFTPAR RIGHTPAR          { mk_pat (PPptuple []) }
| LEFTPAR pattern RIGHTPAR  { $2 }
| LEFTREC pfields RIGHTREC  { mk_pat (PPprec $2) }
;

pfields:
| pat_field opt_semicolon       { [$1] }
| pat_field SEMICOLON pfields   { $1::$3 }
;

pat_field:
| lqualid EQUAL pattern   { ($1, $3) }
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
| list1_lident label labels list0_lident_labels COLON primitive_type
   { let l = match List.rev $1 with
       | i :: l -> add_lab i ($2 :: $3) :: l
       | [] -> assert false
     in
     List.map (fun id -> (Some id, $6)) (List.rev_append l $4) }
;

list1_lident:
| lident               { [$1] }
| lident list1_lident  { $1 :: $2 }
;

list0_lident_labels:
| /* epsilon */                      { [] }
| lident labels list0_lident_labels  { add_lab $1 $2 :: $3 }
;

/* Idents */

ident:
| uident { $1 }
| lident { $1 }
;

uident:
| UIDENT          { mk_id $1 (floc ()) }
;

lident:
| LIDENT          { mk_id $1 (floc ()) }
| lident_keyword  { mk_id $1 (floc ()) }
;

lident_keyword:
| MODEL           { "model" }
;

/* Idents + symbolic operations' names */

ident_rich:
| uident      { $1 }
| lident_rich { $1 }
;

lident_rich:
| lident                      { $1 }
| LEFTPAR lident_op RIGHTPAR  { mk_id $2 (floc ()) }
| LEFTPAR_STAR_RIGHTPAR       { mk_id (infix "*") (floc ()) }
;

lident_op:
| prefix_op             { infix $1 }
| prefix_op UNDERSCORE  { prefix $1 }
| EQUAL                 { infix "=" }
| OPPREF                { prefix $1 }
| LEFTSQ RIGHTSQ        { mixfix "[]" }
| LEFTSQ LARROW RIGHTSQ { mixfix "[<-]" }
;

prefix_op:
| OP1   { $1 }
| OP2   { $1 }
| OP3   { $1 }
| OP4   { $1 }
;

/* Qualified idents */

qualid:
| ident_rich              { Qident $1 }
| uqualid DOT ident_rich  { Qdot ($1, $3) }
;

lqualid_rich:
| lident_rich             { Qident $1 }
| uqualid DOT lident_rich { Qdot ($1, $3) }
;

lqualid:
| lident              { Qident $1 }
| uqualid DOT lident  { Qdot ($1, $3) }
;

/* copy of lqualid to avoid yacc conflicts */
lqualid_copy:
| lident              { Qident $1 }
| uqualid DOT lident  { Qdot ($1, $3) }
;

uqualid:
| uident              { Qident $1 }
| uqualid DOT uident  { Qdot ($1, $3) }
;

/* Theory/Module names */

tqualid:
| uident                { Qident $1 }
| any_qualid DOT uident { Qdot ($1, $3) }
;

any_qualid:
| sident                { Qident $1 }
| any_qualid DOT sident { Qdot ($1, $3) }
;

sident:
| ident   { $1 }
| STRING  { mk_id $1 (floc ()) }
;

/* Misc */

label:
| STRING    { Lstr $1 }
| POSITION  { Lpos $1 }
;

labels:
| /* epsilon */ { [] }
| label labels  { $1 :: $2 }
;

bar_:
| /* epsilon */ { () }
| BAR           { () }
;

/****************************************************************************/

program_file:
| list0_theory_or_module_ EOF { $1 }
;

list0_theory_or_module_:
| /* epsilon */
   { [] }
| list1_theory_or_module_
   { $1 }
;

list1_theory_or_module_:
| theory_or_module_
   { [$1] }
| theory_or_module_ list1_theory_or_module_
   { $1 :: $2 }
;

theory_or_module_:
| THEORY uident labels list0_full_decl END
   { Ptheory { pth_name = add_lab $2 $3; pth_decl = $4; } }
| MODULE uident labels list0_program_decl END
   { Pmodule { mod_name = add_lab $2 $3; mod_decl = $4; } }
;

list0_full_decl:
| /* epsilon */
   { [] }
| list1_full_decl
   { $1 }
;

list1_full_decl:
| full_decl
   { [$1] }
| full_decl list1_full_decl
   { $1 :: $2 }
;

full_decl:
| NAMESPACE namespace_import namespace_name list0_full_decl END
   { Dnamespace (floc_i 3, $3, $2, $4) }
| decl
   { Dlogic $1 }
;

list0_program_decl:
| /* epsilon */
   { [] }
| list1_program_decl
   { $1 }
;

list1_program_decl:
| program_decl
   { [$1] }
| program_decl list1_program_decl
   { $1 :: $2 }
;

program_decl:
| decl
    { Dlogic $1 }
| LET lident_rich_pgm labels list1_type_v_binder opt_cast EQUAL triple
    { Dlet (add_lab $2 $3, mk_expr_i 7 (Efun ($4, cast_body $5 $7))) }
| LET lident_rich_pgm labels EQUAL FUN list1_type_v_binder ARROW triple
    { Dlet (add_lab $2 $3, mk_expr_i 8 (Efun ($6, $8))) }
| LET REC list1_recfun_sep_and
    { Dletrec $3 }
| VAL lident_rich_pgm labels COLON type_v
    { Dparam (add_lab $2 $3, $5) }
| VAL lident_rich_pgm labels list1_type_v_param COLON type_c
    { let tv = Tarrow ($4, $6) in
      Dparam (add_lab $2 $3, tv) }
| EXCEPTION uident labels
    { Dexn (add_lab $2 $3, None) }
| EXCEPTION uident labels primitive_type
    { Dexn (add_lab $2 $3, Some $4) }
| USE use_module
    { $2 }
| NAMESPACE namespace_import namespace_name list0_program_decl END
    { Dnamespace (floc_i 3, $3, $2, $4) }
;

lident_rich_pgm:
| lident_rich
    { $1 }
| LEFTPAR LEFTSQ RIGHTSQ LARROW RIGHTPAR
    { mk_id (mixfix "[]<-") (floc ()) }
;

opt_mutable:
| /* epsilon */ { false }
| MUTABLE       { true  }
;

opt_semicolon:
| /* epsilon */ {}
| SEMICOLON     {}
;

use_module:
| imp_exp MODULE tqualid
    { Duse ($3, $1, None) }
| imp_exp MODULE tqualid AS uident
    { Duse ($3, $1, Some $5) }
;

list1_recfun_sep_and:
| recfun                           { [ $1 ] }
| recfun WITH list1_recfun_sep_and { $1 :: $3 }
;

recfun:
| lident_rich_pgm labels list1_type_v_binder opt_cast opt_variant EQUAL triple
   { add_lab $1 $2, $3, $5, cast_body $4 $7 }
;

expr:
| expr_arg %prec prec_simple
   { $1 }
| expr EQUAL expr
   { mk_infix $1 "=" $3 }
| expr LTGT expr
   { mk_expr (Enot (mk_infix $1 "=" $3)) }
| expr LARROW expr
    { match $1.expr_desc with
        | Eapply (e11, e12) -> begin match e11.expr_desc with
            | Eident x ->
                mk_expr (Eassign (e12, x, $3))
            | Eapply ({ expr_desc = Eident (Qident x) }, e11)
            when x.id = mixfix "[]" ->
                mk_mixfix3 "[]<-" e11 e12 $3
            | _ ->
                raise Parsing.Parse_error
          end
        | _ ->
            raise Parsing.Parse_error
    }
| expr OP1 expr
   { mk_infix $1 $2 $3 }
| expr OP2 expr
   { mk_infix $1 $2 $3 }
| expr OP3 expr
   { mk_infix $1 $2 $3 }
| expr OP4 expr
   { mk_infix $1 $2 $3 }
| NOT expr %prec prec_prefix_op
   { mk_expr (Enot $2) }
| prefix_op expr %prec prec_prefix_op
   { mk_prefix $1 $2 }
| expr_arg list1_expr_arg %prec prec_app
   { mk_expr (mk_apply $1 $2) }
| IF expr THEN expr ELSE expr
   { mk_expr (Eif ($2, $4, $6)) }
| IF expr THEN expr %prec prec_no_else
   { mk_expr (Eif ($2, $4, mk_expr (Etuple []))) }
| expr SEMICOLON expr
   { mk_expr (Esequence ($1, $3)) }
| assertion_kind annotation
   { mk_expr (Eassert ($1, $2)) }
| expr AMPAMP expr
   { mk_expr (Elazy (LazyAnd, $1, $3)) }
| expr BARBAR expr
   { mk_expr (Elazy (LazyOr, $1, $3)) }
| LET pattern EQUAL expr IN expr
   { match $2.pat_desc with
       | PPpvar id -> mk_expr (Elet (id, $4, $6))
       | _ -> mk_expr (Ematch ($4, [$2, $6])) }
| LET lident labels list1_type_v_binder EQUAL triple IN expr
   { mk_expr (Elet (add_lab $2 $3, mk_expr_i 6 (Efun ($4, $6)), $8)) }
| LET REC list1_recfun_sep_and IN expr
   { mk_expr (Eletrec ($3, $5)) }
| FUN list1_type_v_binder ARROW triple
   { mk_expr (Efun ($2, $4)) }
| MATCH expr WITH bar_ program_match_cases END
   { mk_expr (Ematch ($2, $5)) }
| MATCH expr COMMA list1_expr_sep_comma WITH bar_ program_match_cases END
   { mk_expr (Ematch (mk_expr (Etuple ($2::$4)), $7)) }
| QUOTE uident COLON expr %prec prec_mark
   { mk_expr (Emark (quote $2, $4)) }
| LOOP loop_annotation expr END
   { mk_expr (Eloop ($2, $3)) }
| WHILE expr DO loop_annotation expr DONE
   { mk_expr
       (Etry
          (mk_expr
             (Eloop ($4,
                     mk_expr (Eif ($2, $5,
                                   mk_expr (Eraise (exit_exn (), None)))))),
           [exit_exn (), None, mk_expr (Etuple [])])) }
| FOR lident EQUAL expr for_direction expr DO loop_invariant expr DONE
   { mk_expr (Efor ($2, $4, $5, $6, $8, $9)) }
| ABSURD
   { mk_expr Eabsurd }
| expr COLON primitive_type
   { mk_expr (Ecast ($1, $3)) }
| RAISE uqualid
   { mk_expr (Eraise ($2, None)) }
| RAISE LEFTPAR uqualid expr RIGHTPAR
   { mk_expr (Eraise ($3, Some $4)) }
| TRY expr WITH bar_ list1_handler_sep_bar END
   { mk_expr (Etry ($2, $5)) }
| ANY simple_type_c
   { mk_expr (Eany $2) }
| label expr %prec prec_named
   { mk_expr (Enamed ($1, $2)) }
;

triple:
| pre expr post
  { $1, (* add_init_label *) $2, $3 }
| expr %prec prec_triple
  { mk_pp PPtrue, (* add_init_label *) $1, (mk_pp PPtrue, []) }
;

expr_arg:
| constant        { mk_expr (Econstant $1) }
| qualid          { mk_expr (Eident $1) }
| OPPREF expr_arg { mk_prefix $1 $2 }
| expr_sub        { $1 }
;

expr_dot:
| lqualid_copy    { mk_expr (Eident $1) }
| OPPREF expr_dot { mk_prefix $1 $2 }
| expr_sub        { $1 }
;

expr_sub:
| expr_dot DOT lqualid_rich
   { mk_expr (mk_apply (mk_expr_i 3 (Eident $3)) [$1]) }
| LEFTPAR expr RIGHTPAR
    { $2 }
| BEGIN expr END
    { $2 }
| LEFTPAR RIGHTPAR
    { mk_expr (Etuple []) }
| LEFTPAR expr COMMA list1_expr_sep_comma RIGHTPAR
   { mk_expr (Etuple ($2 :: $4)) }
| LEFTREC list1_field_expr opt_semicolon RIGHTREC
   { mk_expr (Erecord (List.rev $2)) }
| LEFTREC expr_arg WITH list1_field_expr opt_semicolon RIGHTREC
   { mk_expr (Eupdate ($2, List.rev $4)) }
| BEGIN END
    { mk_expr (Etuple []) }
| expr_arg LEFTSQ expr RIGHTSQ
    { mk_mixfix2 "[]" $1 $3 }
| expr_arg LEFTSQ expr LARROW expr RIGHTSQ
    { mk_mixfix3 "[<-]" $1 $3 $5 }
;

list1_field_expr:
| field_expr                            { [$1] }
| list1_field_expr SEMICOLON field_expr { $3 :: $1 }
;

field_expr:
| lqualid EQUAL expr { $1, $3 }
;

list1_expr_arg:
| expr_arg %prec prec_simple { [$1] }
| expr_arg list1_expr_arg    { $1 :: $2 }
;

list1_expr_sep_comma:
| expr                            { [$1] }
| expr COMMA list1_expr_sep_comma { $1 :: $3 }
;

list1_handler_sep_bar:
| handler                           { [$1] }
| handler BAR list1_handler_sep_bar { $1 :: $3 }
;

handler:
| uqualid ARROW expr            { ($1, None, $3) }
| uqualid ident ARROW expr      { ($1, Some $2, $4) }
| uqualid UNDERSCORE ARROW expr { ($1, Some (id_anonymous ()), $4) }
;

program_match_cases:
| program_match_case                          { [$1] }
| program_match_case BAR program_match_cases  { $1::$3 }
;

program_match_case:
| pattern ARROW expr   { ($1,$3) }
;

assertion_kind:
| ASSERT { Aassert }
| ASSUME { Aassume }
| CHECK  { Acheck  }
;

for_direction:
| TO     { To }
| DOWNTO { Downto }
;

loop_annotation:
| loop_invariant opt_variant { { loop_invariant = $1; loop_variant = $2 } }
;

loop_invariant:
| INVARIANT annotation { Some $2 }
| /* epsilon */        { None    }
;

list1_type_v_binder:
| type_v_binder                     { $1 }
| type_v_binder list1_type_v_binder { $1 @ $2 }
;

list1_type_v_param:
| type_v_param                    { $1 }
| type_v_param list1_type_v_param { $1 @ $2 }
;

type_v_binder:
| lident labels
   { [add_lab $1 $2, None] }
| type_v_param
   { $1 }
;

type_v_param:
| LEFTPAR RIGHTPAR
   { [id_anonymous (), Some (ty_unit ())] }
| LEFTPAR lidents_lab COLON type_v RIGHTPAR
   { List.map (fun i -> (i, Some $4)) $2 }
;

lidents_lab:
| lident labels list0_lident_labels { add_lab $1 $2 :: $3 }
;

type_v:
| simple_type_v
   { $1 }
| arrow_type_v
   { $1 }
;

arrow_type_v:
| simple_type_v ARROW type_c
   { Tarrow ([id_anonymous (), Some $1], $3) }
| lident labels COLON simple_type_v ARROW type_c
   { Tarrow ([add_lab $1 $2, Some $4], $6) }
   /* TODO: we could alllow lidents instead, e.g. x y : int -> ... */
   /*{ Tarrow (List.map (fun x -> x, Some $3) $1, $5) }*/
;

simple_type_v:
| primitive_type
    { Tpure $1 }
| LEFTPAR arrow_type_v RIGHTPAR
    { $2 }
;

type_c:
| type_v
    { type_c (mk_pp PPtrue) $1 empty_effect (mk_pp PPtrue, []) }
| pre type_v effects post
    { type_c $1 $2 $3 $4 }
;

/* for ANY */
simple_type_c:
| simple_type_v
    { type_c (mk_pp PPtrue) $1 empty_effect (mk_pp PPtrue, []) }
| pre type_v effects post
    { type_c $1 $2 $3 $4 }
;

annotation:
| LEFTBRC RIGHTBRC       { mk_pp PPtrue }
| LEFTBRC lexpr RIGHTBRC { $2 }
;

pre:
| annotation { $1 }
;

post:
| annotation list0_post_exn { $1, $2 }
;

list0_post_exn:
| /* epsilon */  %prec prec_post { [] }
| list1_post_exn                 { $1 }
;

list1_post_exn:
| post_exn                %prec prec_post { [$1] }
| post_exn list1_post_exn                 { $1 :: $2 }
;

post_exn:
| BAR uqualid ARROW annotation { $2, $4 }
;

effects:
| opt_reads opt_writes opt_raises
    { { pe_reads = $1; pe_writes = $2; pe_raises = $3 } }
;

opt_reads:
| /* epsilon */         { [] }
| READS list1_lexpr_arg { $2 }
;

opt_writes:
| /* epsilon */          { [] }
| WRITES list1_lexpr_arg { $2 }
;

opt_raises:
| /* epsilon */        { [] }
| RAISES list1_uqualid { $2 }
;

opt_variant:
| /* epsilon */                   { None }
| VARIANT annotation              { Some ($2, None) }
| VARIANT annotation WITH lqualid { Some ($2, Some $4) }
;

opt_cast:
| /* epsilon */   { None }
| COLON primitive_type { Some $2 }
;

list1_uqualid:
| uqualid               { [$1] }
| uqualid list1_uqualid { $1 :: $2 }
;

/*
Local Variables:
compile-command: "unset LANG; make -C ../.."
End:
*/
