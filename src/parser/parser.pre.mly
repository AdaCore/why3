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
  open Theory

  let env_ref  = ref []
  let lenv_ref = ref []
  let uc_ref   = ref []

  let ref_get  ref = List.hd !ref
  let ref_tail ref = List.tl !ref
  let ref_drop ref = ref := ref_tail ref
  let ref_pop  ref = let v = ref_get ref in ref_drop ref; v

  let ref_push ref v = ref := v :: !ref
  let ref_set  ref v = ref := v :: ref_tail ref

  let inside_env env rule lexer lexbuf =
    ref_push env_ref env;
      ref_push lenv_ref Mnm.empty;
    let res = rule lexer lexbuf in
      ref_drop lenv_ref;
    ref_drop env_ref;
    res

  let inside_uc env lenv uc rule lexer lexbuf =
    ref_push env_ref env;
      ref_push lenv_ref lenv;
        ref_push uc_ref uc;
    let res = rule lexer lexbuf in
        ref_drop uc_ref;
      ref_drop lenv_ref;
    ref_drop env_ref;
    res

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

  let mk_id id loc = { id = id; id_lab = []; id_loc = loc }

  let add_lab id l = { id with id_lab = l }

  let user_loc fname lnum bol cnum1 cnum2 =
    let pos = {
      Lexing.pos_fname = fname;
      Lexing.pos_lnum = lnum;
      Lexing.pos_bol = bol;
      Lexing.pos_cnum = cnum1 }
    in
    pos, { pos with Lexing.pos_cnum = cnum2 }

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
%token BACKQUOTE BAR
%token COLON COMMA
%token DOT EQUAL FUNC LAMBDA LTGT
%token LEFTPAR LEFTPAR_STAR_RIGHTPAR LEFTSQ
%token LRARROW
%token PRED QUOTE
%token RIGHTPAR RIGHTSQ
%token UNDERSCORE

%token EOF

/* Precedences */

%nonassoc DOT ELSE IN
%nonassoc prec_named
%nonassoc COLON

%right ARROW LRARROW
%right OR ASYM_OR
%right AND ASYM_AND
%nonassoc NOT
%left EQUAL LTGT OP1
%left OP2
%left OP3
%left OP4
%nonassoc prefix_op

/* Entry points */

%type <Ptree.lexpr> lexpr_eof
%start lexpr_eof
%type <Theory.theory_uc> list0_decl_eof
%start list0_decl_eof
%type <Theory.theory Theory.Mnm.t> logic_file_eof
%start logic_file_eof
%%

logic_file_eof:
| list0_theory EOF  { ref_get lenv_ref }
;

list0_decl_eof:
| list0_decl EOF  { ref_get uc_ref }
;

lexpr_eof:
| lexpr EOF  { $1 }
;

/* File, theory, namespace */

list0_theory:
| /* epsilon */         { () }
| theory list0_theory   { () }
;

theory_head:
| THEORY uident labels
   { let id = add_lab $2 $3 and labels = $3 in
     let name = Ident.id_user ~labels id.id id.id_loc in
     ref_push uc_ref (create_theory name); id }
;

theory:
| theory_head list0_decl END
   { let uc = ref_pop uc_ref in
     ref_set lenv_ref (Typing.close_theory (ref_get lenv_ref) $1 uc) }
;

list0_decl:
| /* epsilon */        { () }
| new_decl list0_decl  { () }
;

new_decl:
| decl
   { let env = ref_get env_ref in let lenv = ref_get lenv_ref in
     ref_set uc_ref (Typing.add_decl env lenv (ref_get uc_ref) $1) }
| namespace_head namespace_import namespace_name list0_decl END
   { ref_set uc_ref (Typing.close_namespace (loc ()) $2 $3 (ref_get uc_ref)) }
;

namespace_head:
| NAMESPACE
   { ref_set uc_ref (open_namespace (ref_get uc_ref)) }
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
| LOGIC list1_logic_decl
    { LogicDecl $2 }
| INDUCTIVE list1_inductive_decl
    { IndDecl $2 }
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
| META ident list1_meta_arg_sep_comma
    { Meta (loc (), $2, $3) }
| META STRING list1_meta_arg_sep_comma
    { Meta (loc (), mk_id $2 (loc_i 2), $3) }
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
| NAMESPACE ns EQUAL ns     { CSns   ($2, $4) }
| TYPE  qualid EQUAL qualid { CStsym ($2, $4) }
| LOGIC qualid EQUAL qualid { CSlsym ($2, $4) }
| LEMMA qualid              { CSlemma $2 }
| GOAL  qualid              { CSgoal  $2 }
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
| TYPE  qualid { PMAts  $2 }
| LOGIC qualid { PMAls  $2 }
| PROP  qualid { PMApr  $2 }
| STRING       { PMAstr $1 }
| INTEGER      { PMAint $1 }
;

/* Type declarations */

list1_type_decl:
| type_decl                       { [$1] }
| type_decl WITH list1_type_decl  { $1 :: $3 }
;

type_decl:
| lident labels type_args typedefn
  { { td_loc = loc (); td_ident = add_lab $1 $2;
      td_params = $3; td_def = $4 } }
;

type_args:
| /* epsilon */             { [] }
| type_var labels type_args { add_lab $1 $2 :: $3 }
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
| uident labels params   { (loc (), add_lab $1 $2, $3) }
;

/* Logic declarations */

list1_logic_decl:
| logic_decl                        { [$1] }
| logic_decl WITH list1_logic_decl  { $1 :: $3 }
;

logic_decl:
| lident_rich labels params logic_type_option logic_def_option
  { { ld_loc = loc (); ld_ident = add_lab $1 $2;
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
  { { in_loc = loc (); in_ident = add_lab $1 $2;
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
| uident labels COLON lexpr { (loc (), add_lab $1 $2, $4) }
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
   { mk_pp (PPnamed (Ident.label "asym_split", infix_pp $1 PPor $3)) }
| lexpr AND lexpr
   { infix_pp $1 PPand $3 }
| lexpr ASYM_AND lexpr
   { mk_pp (PPnamed (Ident.label "asym_split", infix_pp $1 PPand $3)) }
| NOT lexpr
   { prefix_pp PPnot $2 }
| lexpr EQUAL lexpr
   { mk_pp (PPinfix ($1, mk_id (infix "=") (loc_i 2), $3)) }
| lexpr LTGT lexpr
   { prefix_pp PPnot (mk_pp (PPinfix ($1, mk_id (infix "=") (loc_i 2), $3))) }
| lexpr OP1 lexpr
   { mk_pp (PPinfix ($1, mk_id (infix $2) (loc_i 2), $3)) }
| lexpr OP2 lexpr
   { mk_pp (PPinfix ($1, mk_id (infix $2) (loc_i 2), $3)) }
| lexpr OP3 lexpr
   { mk_pp (PPinfix ($1, mk_id (infix $2) (loc_i 2), $3)) }
| lexpr OP4 lexpr
   { mk_pp (PPinfix ($1, mk_id (infix $2) (loc_i 2), $3)) }
| any_op lexpr %prec prefix_op
   { mk_pp (PPapp (Qident (mk_id (prefix $1) (loc_i 2)), [$2])) }
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

list1_lexpr_arg:
| lexpr_arg                 { [$1] }
| lexpr_arg list1_lexpr_arg { $1::$2 }
;

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
   { mk_pp (PPapp (Qident (mk_id (prefix $1) (loc_i 2)), [$2])) }
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

ident_rich:
| uident      { $1 }
| lident_rich { $1 }
;

lident_rich:
| lident
    { $1 }
| LEFTPAR lident_op RIGHTPAR
    { mk_id (infix $2) (loc ()) }
| LEFTPAR_STAR_RIGHTPAR
    { mk_id (infix "*") (loc ()) }
| LEFTPAR lident_op UNDERSCORE RIGHTPAR
    { mk_id (prefix $2) (loc ()) }
| LEFTPAR OPPREF RIGHTPAR
    { mk_id (prefix $2) (loc ()) }
;

lident:
| LIDENT { mk_id $1 (loc ()) }
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
| UIDENT { mk_id $1 (loc ()) }
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
;

qualid:
| ident_rich             { Qident $1 }
| uqualid DOT ident_rich { Qdot ($1, $3) }
;

/* Misc */

label:
| STRING
   { Ident.label $1 }
| STRING BACKQUOTE INTEGER BACKQUOTE INTEGER
         BACKQUOTE INTEGER BACKQUOTE INTEGER BACKQUOTE STRING
   { let loc = user_loc $11 (int_of_string $3) (int_of_string $5)
                            (int_of_string $7) (int_of_string $9) in
     Ident.label ~loc $1 }
;

labels:
| /* epsilon */ { [] }
| label labels  { $1 :: $2 }
;

bar_:
| /* epsilon */ { () }
| BAR           { () }
;

