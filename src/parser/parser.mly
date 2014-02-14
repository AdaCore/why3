/********************************************************************/
/*                                                                  */
/*  The Why3 Verification Platform   /   The Why3 Development Team  */
/*  Copyright 2010-2013   --   INRIA - CNRS - Paris-Sud University  */
/*                                                                  */
/*  This software is distributed under the terms of the GNU Lesser  */
/*  General Public License version 2.1, with the special exception  */
/*  on linking described in file LICENSE.                           */
/*                                                                  */
/********************************************************************/

%{
module Incremental = struct
  let stack = Stack.create ()
  let open_file inc = Stack.push inc stack
  let close_file () = ignore (Stack.pop stack)
  let open_theory id = (Stack.top stack).Ptree.open_theory id
  let close_theory () = (Stack.top stack).Ptree.close_theory ()
  let open_module id = (Stack.top stack).Ptree.open_module id
  let close_module () = (Stack.top stack).Ptree.close_module ()
  let open_namespace n = (Stack.top stack).Ptree.open_namespace n
  let close_namespace l b = (Stack.top stack).Ptree.close_namespace l b
  let new_decl loc d = (Stack.top stack).Ptree.new_decl loc d
  let new_pdecl loc d = (Stack.top stack).Ptree.new_pdecl loc d
  let use_clone loc use = (Stack.top stack).Ptree.use_clone loc use
end

  open Ptree

  let loc () = (symbol_start_pos (), symbol_end_pos ())
  let floc () = Loc.extract (loc ())

  let loc_i i = (rhs_start_pos i, rhs_end_pos i)
  let floc_i i = Loc.extract (loc_i i)

(* dead code
  let loc_ij i j = (rhs_start_pos i, rhs_end_pos j)
  let floc_ij i j = Loc.extract (loc_ij i j)
*)

  let mk_ppl loc d = { pp_loc = loc; pp_desc = d }
  let mk_pp d = mk_ppl (floc ()) d
  let mk_pat p = { pat_loc = floc (); pat_desc = p }

  let infix_ppl loc a i b = mk_ppl loc (PPbinop (a, i, b))
  let infix_pp a i b = infix_ppl (floc ()) a i b

  let prefix_ppl loc p a = mk_ppl loc (PPunop (p, a))
  let prefix_pp p a = prefix_ppl (floc ()) p a

  let infix  s = "infix "  ^ s
  let prefix s = "prefix " ^ s
  let mixfix s = "mixfix " ^ s

  let mk_id id loc = { id = id; id_lab = []; id_loc = loc }

  let add_lab id l = { id with id_lab = l }

  let mk_l_apply f a =
    let loc = Loc.join f.pp_loc a.pp_loc in
    { pp_loc = loc; pp_desc = PPapply (f,a) }

  let mk_l_prefix op e1 =
    let id = mk_id (prefix op) (floc_i 1) in
    mk_pp (PPidapp (Qident id, [e1]))

  let mk_l_infix e1 op e2 =
    let id = mk_id (infix op) (floc_i 2) in
    mk_pp (PPinfix (e1, id, e2))

  let mk_l_mixfix2 op e1 e2 =
    let id = mk_id (mixfix op) (floc_i 2) in
    mk_pp (PPidapp (Qident id, [e1;e2]))

  let mk_l_mixfix3 op e1 e2 e3 =
    let id = mk_id (mixfix op) (floc_i 2) in
    mk_pp (PPidapp (Qident id, [e1;e2;e3]))

  let () = Exn_printer.register
    (fun fmt exn -> match exn with
      | Parsing.Parse_error -> Format.fprintf fmt "syntax error"
      | _ -> raise exn)

  let mk_expr d = { expr_loc = floc (); expr_desc = d }

  let mk_expr_i i d = { expr_loc = floc_i i; expr_desc = d }

  let mk_apply f a =
    let loc = Loc.join f.expr_loc a.expr_loc in
    { expr_loc = loc; expr_desc = Eapply (f,a) }

  let mk_prefix op e1 =
    let id = mk_id (prefix op) (floc_i 1) in
    mk_expr (Eidapp (Qident id, [e1]))

  let mk_infix e1 op e2 =
    let id = mk_id (infix op) (floc_i 2) in
    mk_expr (Einfix (e1, id, e2))

  let mk_mixfix2 op e1 e2 =
    let id = mk_id (mixfix op) (floc_i 2) in
    mk_expr (Eidapp (Qident id, [e1; e2]))

  let mk_mixfix3 op e1 e2 e3 =
    let id = mk_id (mixfix op) (floc_i 2) in
    mk_expr (Eidapp (Qident id, [e1; e2; e3]))

  let id_anonymous () = mk_id "_" (floc ())

  let variant_union v1 v2 = match v1, v2 with
    | _, [] -> v1
    | [], _ -> v2
    | _, _ -> Loc.errorm ~loc:(floc ())
        "multiple `variant' clauses are not allowed"

  let empty_spec = {
    sp_pre     = [];
    sp_post    = [];
    sp_xpost   = [];
    sp_reads   = [];
    sp_writes  = [];
    sp_variant = [];
    sp_checkrw = false;
    sp_diverge = false;
  }

  let spec_union s1 s2 = {
    sp_pre     = s1.sp_pre @ s2.sp_pre;
    sp_post    = s1.sp_post @ s2.sp_post;
    sp_xpost   = s1.sp_xpost @ s2.sp_xpost;
    sp_reads   = s1.sp_reads @ s2.sp_reads;
    sp_writes  = s1.sp_writes @ s2.sp_writes;
    sp_variant = variant_union s1.sp_variant s2.sp_variant;
    sp_checkrw = s1.sp_checkrw || s2.sp_checkrw;
    sp_diverge = s1.sp_diverge || s2.sp_diverge;
  }

(* dead code
  let add_init_mark e =
    let init = { id = "Init"; id_lab = []; id_loc = e.expr_loc } in
    { e with expr_desc = Emark (init, e) }
*)

  let small_integer i =
    try
      match i with
      | Number.IConstDec s -> int_of_string s
      | Number.IConstHex s -> int_of_string ("0x"^s)
      | Number.IConstOct s -> int_of_string ("0o"^s)
      | Number.IConstBin s -> int_of_string ("0b"^s)
    with Failure _ -> raise Parsing.Parse_error

  let qualid_last = function
    | Qident x | Qdot (_, x) -> x.id

%}

/* Tokens */

%token <string> LIDENT UIDENT
%token <Ptree.integer_constant> INTEGER
%token <string> OP1 OP2 OP3 OP4 OPPREF
%token <Ptree.real_constant> FLOAT
%token <string> STRING
%token <Loc.position> POSITION
%token <string> QUOTE_UIDENT QUOTE_LIDENT OPAQUE_QUOTE_LIDENT

/* keywords */

%token AS AXIOM CLONE COINDUCTIVE CONSTANT
%token ELSE END EPSILON EXISTS EXPORT FALSE FORALL FUNCTION
%token GOAL IF IMPORT IN INDUCTIVE LEMMA
%token LET MATCH META NAMESPACE NOT PROP PREDICATE
%token THEN THEORY TRUE TYPE USE WITH

/* program keywords */

%token ABSTRACT ABSURD ANY ASSERT ASSUME BEGIN CHECK DIVERGES DO DONE DOWNTO
%token ENSURES EXCEPTION FOR
%token FUN GHOST INVARIANT LOOP MODEL MODULE MUTABLE PRIVATE RAISE
%token RAISES READS REC REQUIRES RETURNS TO TRY VAL VARIANT WHILE WRITES

/* symbols */

%token AND ARROW
%token BAR
%token COLON COMMA
%token DOT EQUAL LAMBDA LTGT
%token LEFTPAR LEFTPAR_STAR_RIGHTPAR LEFTSQ
%token LARROW LRARROW OR
%token RIGHTPAR RIGHTSQ
%token UNDERSCORE

%token EOF

/* program symbols */

%token AMPAMP BARBAR LEFTBRC RIGHTBRC SEMICOLON

/* Precedences */

%nonassoc prec_mark
%nonassoc prec_fun
%nonassoc IN
%right SEMICOLON
%nonassoc prec_no_else
%nonassoc DOT ELSE GHOST
%nonassoc prec_no_spec
%nonassoc REQUIRES ENSURES RETURNS RAISES READS WRITES DIVERGES VARIANT
%nonassoc prec_named
%nonassoc COLON

%right ARROW LRARROW
%right OR BARBAR
%right AND AMPAMP
%nonassoc NOT
%left EQUAL LTGT OP1
%nonassoc LARROW
%nonassoc RIGHTSQ    /* stronger than <- for e1[e2 <- e3] */
%left OP2
%left OP3
%left OP4
%nonassoc prec_prefix_op
%nonassoc LEFTSQ
%nonassoc OPPREF

/* Entry points */

%type <Ptree.incremental -> unit> open_file
%start open_file
%type <unit> logic_file
%start logic_file
%type <unit> program_file
%start program_file
%%

open_file:
| /* epsilon */  { Incremental.open_file }
;

logic_file:
| list0_theory EOF  { Incremental.close_file () }
;

/* File, theory, namespace */

list0_theory:
| /* epsilon */         { () }
| theory list0_theory   { () }
;

theory_head:
| THEORY uident labels  { Incremental.open_theory (add_lab $2 $3) }
;

theory:
| theory_head list0_decl END  { Incremental.close_theory () }
;

list0_decl:
| /* epsilon */        { () }
| new_decl list0_decl  { () }
| new_ns_th list0_decl { () }
;

new_decl:
| decl
   { Incremental.new_decl (floc ()) $1 }
| use_clone
   { Incremental.use_clone (floc ()) $1 }
;

new_ns_th:
| namespace_head list0_decl END
   { Incremental.close_namespace (floc_i 1) $1 }
;

namespace_head:
| NAMESPACE namespace_import uident
   { Incremental.open_namespace $3.id; $2 }
;

namespace_import:
| /* epsilon */  { false }
| IMPORT         { true }
;

/* Declaration */

decl:
| TYPE list1_type_decl
    { TypeDecl $2 }
| TYPE late_invariant
    { TypeDecl [$2] }
| CONSTANT logic_decl_constant
    { LogicDecl [$2] }
| FUNCTION list1_logic_decl_function
    { LogicDecl $2 }
| PREDICATE list1_logic_decl_predicate
    { LogicDecl $2 }
| inductive list1_inductive_decl
    { IndDecl ($1, $2) }
| AXIOM ident labels COLON lexpr
    { PropDecl (Kaxiom, add_lab $2 $3, $5) }
| LEMMA ident labels COLON lexpr
    { PropDecl (Klemma, add_lab $2 $3, $5) }
| GOAL ident labels COLON lexpr
    { PropDecl (Kgoal, add_lab $2 $3, $5) }
| META sident list1_meta_arg_sep_comma
    { Meta ($2, $3) }
;

inductive:
| INDUCTIVE   { Decl.Ind }
| COINDUCTIVE { Decl.Coind }
;

/* Use and clone */

use_clone:
| USE use
    { ($2, None) }
| CLONE use clone_subst
    { ($2, Some $3) }
;

use:
| opt_import tqualid
    { { use_theory = $2; use_import = Some ($1, qualid_last $2) } }
| opt_import tqualid AS uident
    { { use_theory = $2; use_import = Some ($1, $4.id) } }
| EXPORT tqualid
    { { use_theory = $2; use_import = None } }
;

opt_import:
| /* epsilon */ { false }
| IMPORT        { true  }
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
| NAMESPACE ns     EQUAL ns     { CSns   (floc (), $2, $4) }
| TYPE qualid type_args EQUAL primitive_type
                                { CStsym (floc (), $2, $3, $5) }
| CONSTANT  qualid EQUAL qualid { CSfsym (floc (), $2, $4) }
| FUNCTION  qualid EQUAL qualid { CSfsym (floc (), $2, $4) }
| PREDICATE qualid EQUAL qualid { CSpsym (floc (), $2, $4) }
| LEMMA     qualid              { CSlemma (floc (), $2) }
| GOAL      qualid              { CSgoal  (floc (), $2) }
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
| TYPE primitive_type { PMAty $2 }
| CONSTANT  qualid { PMAfs  $2 }
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
  { let model, vis, def, inv = $4 in
    let vis = if model then Abstract else vis in
    { td_loc = floc (); td_ident = add_lab $1 $2;
      td_params = $3; td_model = model;
      td_vis = vis; td_def = def; td_inv = inv } }
;

late_invariant:
| lident labels type_args invariant type_invariant
  { { td_loc = floc (); td_ident = add_lab $1 $2;
      td_params = $3; td_model = false;
      td_vis = Public; td_def = TDabstract; td_inv = $4::$5 } }
;

type_args:
| /* epsilon */                 { [] }
| quote_lident labels type_args { add_lab $1 $2 :: $3 }
;

typedefn:
| /* epsilon */
    { false, Public, TDabstract, [] }
| equal_model visibility typecases type_invariant
    { $1, $2, TDalgebraic $3, $4 }
| equal_model visibility BAR typecases type_invariant
    { $1, $2, TDalgebraic $4, $5 }
| equal_model visibility record_type type_invariant
    { $1, $2, TDrecord $3, $4 }
/* abstract/private is not allowed for alias type */
| equal_model visibility primitive_type
    { if $2 <> Public then Loc.error ~loc:(floc_i 2) Parsing.Parse_error;
      $1, Public, TDalias $3, [] }
;

visibility:
| /* epsilon */ { Public }
| PRIVATE       { Private }
| ABSTRACT      { Abstract }
;

equal_model:
| EQUAL { false }
| MODEL { true }
;

record_type:
| LEFTBRC list1_record_field opt_semicolon RIGHTBRC { List.rev $2 }
;

list1_record_field:
| record_field                              { [$1] }
| list1_record_field SEMICOLON record_field { $3 :: $1 }
;

field_modifiers:
| /* epsilon */ { false, false }
| MUTABLE       { true,  false }
| GHOST         { false, true  }
| GHOST MUTABLE { true,  true  }
| MUTABLE GHOST { true,  true  }
;

record_field:
| field_modifiers lident labels COLON primitive_type
   { { f_loc = floc ();
       f_ident = add_lab $2 $3;
       f_mutable = fst $1;
       f_ghost = snd $1;
       f_pty = $5 } }
;

typecases:
| typecase                { [$1] }
| typecase BAR typecases  { $1::$3 }
;

typecase:
| uident labels list0_param   { (floc (), add_lab $1 $2, $3) }
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

logic_decl_constant:
| lident_rich labels COLON primitive_type logic_def_option
  { { ld_loc = floc (); ld_ident = add_lab $1 $2;
      ld_params = []; ld_type = Some $4; ld_def = $5 } }
;

logic_decl_function:
| lident_rich labels list0_param COLON primitive_type logic_def_option
  { { ld_loc = floc (); ld_ident = add_lab $1 $2;
      ld_params = $3; ld_type = Some $5; ld_def = $6 } }
;

logic_decl_predicate:
| lident_rich labels list0_param logic_def_option
  { { ld_loc = floc (); ld_ident = add_lab $1 $2;
      ld_params = $3; ld_type = None; ld_def = $4 } }
;

logic_decl:
| lident_rich labels list0_param opt_cast logic_def_option
  { { ld_loc = floc (); ld_ident = add_lab $1 $2;
      ld_params = $3; ld_type = $4; ld_def = $5 } }
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
| lident_rich labels list0_param inddefn
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
| primitive_type_arg                  { $1 }
| lqualid primitive_type_args         { PPTtyapp ($1, $2) }
| primitive_type ARROW primitive_type { PPTarrow ($1, $3) }
;

primitive_type_args:
| primitive_type_arg                      { [$1] }
| primitive_type_arg primitive_type_args  { $1 :: $2 }
;

primitive_type_arg:
| lqualid
   { PPTtyapp ($1, []) }
| quote_lident
   { PPTtyvar ($1, false) }
| opaque_quote_lident
   { PPTtyvar ($1, true) }
| LEFTPAR list2_primitive_type_sep_comma RIGHTPAR
   { PPTtuple $2 }
| LEFTPAR RIGHTPAR
   { PPTtuple [] }
| LEFTPAR primitive_type RIGHTPAR
   { PPTparen $2 }
;

list2_primitive_type_sep_comma:
| primitive_type COMMA list1_primitive_type_sep_comma { $1 :: $3 }
;

list1_primitive_type_sep_comma:
| primitive_type                                      { [$1] }
| primitive_type COMMA list1_primitive_type_sep_comma { $1 :: $3 }
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
   { infix_pp $1 PPor_asym $3 }
| lexpr AND lexpr
   { infix_pp $1 PPand $3 }
| lexpr AMPAMP lexpr
   { infix_pp $1 PPand_asym $3 }
| NOT lexpr
   { prefix_pp PPnot $2 }
| lexpr EQUAL lexpr
   { mk_l_infix $1 "=" $3 }
| lexpr LTGT lexpr
   { mk_l_infix $1 "<>" $3 }
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
   { mk_pp (PPidapp ($1, $2)) }
| lexpr_arg_noid list1_lexpr_arg
   { List.fold_left mk_l_apply $1 $2 }
| IF lexpr THEN lexpr ELSE lexpr
   { mk_pp (PPif ($2, $4, $6)) }
| quant list1_quant_vars triggers DOT lexpr
   { mk_pp (PPquant ($1, $2, $3, $5)) }
| label lexpr %prec prec_named
   { mk_pp (PPnamed ($1, $2)) }
| LET pattern EQUAL lexpr IN lexpr
   { match $2.pat_desc with
     | PPpvar id -> mk_pp (PPlet (id, $4, $6))
     | PPpwild -> mk_pp (PPlet (id_anonymous (), $4, $6))
     | PPptuple [] -> mk_pp (PPlet (id_anonymous (),
          { $4 with pp_desc = PPcast ($4, PPTtuple []) }, $6))
     | _ -> mk_pp (PPmatch ($4, [$2, $6])) }
| MATCH lexpr WITH bar_ match_cases END
   { mk_pp (PPmatch ($2, $5)) }
| MATCH list2_lexpr_sep_comma WITH bar_ match_cases END
   { mk_pp (PPmatch (mk_pp (PPtuple $2), $5)) }
| lexpr COLON primitive_type
   { mk_pp (PPcast ($1, $3)) }
| lexpr_arg
   { match $1.pp_desc with (* break the infix relation chain *)
     | PPinfix (l,o,r) -> { $1 with pp_desc = PPinnfix (l,o,r) }
     | _ -> $1 }
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
| INTEGER   { Number.ConstInt $1 }
| FLOAT     { Number.ConstReal $1 }
;

lexpr_arg:
| qualid            { mk_pp (PPident $1) }
| lexpr_arg_noid    { $1 }
;

lexpr_arg_noid:
| constant          { mk_pp (PPconst $1) }
| TRUE              { mk_pp PPtrue }
| FALSE             { mk_pp PPfalse }
| OPPREF lexpr_arg  { mk_l_prefix $1 $2 }
| lexpr_sub         { $1 }
| quote_uident      { mk_pp (PPident (Qident $1)) }
;

lexpr_dot:
| lqualid_copy      { mk_pp (PPident $1) }
| OPPREF lexpr_dot  { mk_l_prefix $1 $2 }
| lexpr_sub         { $1 }
;

lexpr_sub:
| lexpr_dot DOT lqualid_rich
   { mk_pp (PPidapp ($3, [$1])) }
| LEFTPAR lexpr RIGHTPAR
   { $2 }
| LEFTPAR RIGHTPAR
   { mk_pp (PPtuple []) }
| LEFTPAR list2_lexpr_sep_comma RIGHTPAR
   { mk_pp (PPtuple $2) }
| LEFTBRC list1_field_value opt_semicolon RIGHTBRC
   { mk_pp (PPrecord (List.rev $2)) }
| LEFTBRC lexpr_arg WITH list1_field_value opt_semicolon RIGHTBRC
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

list2_lexpr_sep_comma:
| lexpr COMMA list1_lexpr_sep_comma { $1 :: $3 }
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
| LEFTBRC pfields RIGHTBRC  { mk_pat (PPprec $2) }
;

pfields:
| pat_field opt_semicolon       { [$1] }
| pat_field SEMICOLON pfields   { $1::$3 }
;

pat_field:
| lqualid EQUAL pattern   { ($1, $3) }
;

/* Binders */

list0_param:
| /* epsilon */ { [] }
| list1_param   { $1 }
;

list1_param:
| param               { $1 }
| param list1_param   { $1 @ $2 }
;

list1_binder:
| binder              { $1 }
| binder list1_binder { $1 @ $2 }
;

/* [param] and [binder] below must have the same grammar and
   raise [Parse_error] in the same cases. Interpretaion of
   single-standing untyped [Qident]'s is different: [param]
   treats them as type expressions, [binder], as parameter
   names, whose type must be inferred. */

param:
| anon_binder
   { Loc.errorm ~loc:(floc ())
      "cannot determine the type of the parameter" }
| primitive_type_arg
   { [floc (), None, false, $1] }
| LEFTPAR GHOST primitive_type RIGHTPAR
   { [floc (), None, true, $3] }
| primitive_type_arg label labels
   { match $1 with
      | PPTtyapp (Qident _, []) -> Loc.errorm ~loc:(floc ())
          "cannot determine the type of the parameter"
      | _ -> Loc.error ~loc:(floc_i 2) Parsing.Parse_error }
| LEFTPAR binder_vars_rest RIGHTPAR
   { match $2 with [l,_] -> Loc.errorm ~loc:l
          "cannot determine the type of the parameter"
      | _ -> Loc.error ~loc:(floc_i 3) Parsing.Parse_error }
| LEFTPAR GHOST binder_vars_rest RIGHTPAR
   { match $3 with [l,_] -> Loc.errorm ~loc:l
          "cannot determine the type of the parameter"
      | _ -> Loc.error ~loc:(floc_i 4) Parsing.Parse_error }
| LEFTPAR binder_vars COLON primitive_type RIGHTPAR
   { List.map (fun (l,i) -> l, i, false, $4) $2 }
| LEFTPAR GHOST binder_vars COLON primitive_type RIGHTPAR
   { List.map (fun (l,i) -> l, i, true, $5) $3 }
;

binder:
| anon_binder
   { Loc.errorm ~loc:(floc ())
      "cannot determine the type of the parameter" }
| primitive_type_arg
   { match $1 with
      | PPTtyapp (Qident id, [])
      | PPTparen (PPTtyapp (Qident id, [])) ->
             [floc (), Some id, false, None]
      | _ -> [floc (), None, false, Some $1] }
| LEFTPAR GHOST primitive_type RIGHTPAR
   { match $3 with
      | PPTtyapp (Qident id, []) ->
             [floc (), Some id, true, None]
      | _ -> [floc (), None, true, Some $3] }
| primitive_type_arg label labels
   { match $1 with
      | PPTtyapp (Qident id, []) ->
          [floc (), Some (add_lab id ($2::$3)), false, None]
      | _ -> Loc.error ~loc:(floc_i 2) Parsing.Parse_error }
| LEFTPAR binder_vars_rest RIGHTPAR
   { match $2 with [l,i] -> [l, i, false, None]
      | _ -> Loc.error ~loc:(floc_i 3) Parsing.Parse_error }
| LEFTPAR GHOST binder_vars_rest RIGHTPAR
   { match $3 with [l,i] -> [l, i, true, None]
      | _ -> Loc.error ~loc:(floc_i 4) Parsing.Parse_error }
| LEFTPAR binder_vars COLON primitive_type RIGHTPAR
   { List.map (fun (l,i) -> l, i, false, Some $4) $2 }
| LEFTPAR GHOST binder_vars COLON primitive_type RIGHTPAR
   { List.map (fun (l,i) -> l, i, true, Some $5) $3 }
;

binder_vars:
| binder_vars_head  { List.rev $1 }
| binder_vars_rest  { $1 }
;

binder_vars_rest:
| binder_vars_head label labels list0_lident_labels
   { List.rev_append (match $1 with
      | (l, Some id) :: bl ->
          (Loc.join l (floc_i 3), Some (add_lab id ($2::$3))) :: bl
      | _ -> assert false) $4 }
| binder_vars_head anon_binder list0_lident_labels
   { List.rev_append $1 ($2 :: $3) }
| anon_binder list0_lident_labels
   { $1 :: $2 }
;

binder_vars_head:
| primitive_type {
    let of_id id = id.id_loc, Some id in
    let push acc = function
      | PPTtyapp (Qident id, []) -> of_id id :: acc
      | _ -> Loc.error ~loc:(floc ()) Parsing.Parse_error in
    match $1 with
      | PPTtyapp (Qident id, l) -> List.fold_left push [of_id id] l
      | _ -> Loc.error ~loc:(floc ()) Parsing.Parse_error }
;

list1_quant_vars:
| quant_vars                        { $1 }
| quant_vars COMMA list1_quant_vars { $1 @ $3 }
;

quant_vars:
| list1_lident_labels opt_cast {
    List.map (function
      | loc, None -> Loc.errorm ~loc "anonymous binders are not allowed here"
      | _, Some i -> i, $2) $1 }
;

list0_lident_labels:
| /* epsilon */        { [] }
| list1_lident_labels  { $1 }
;

list1_lident_labels:
| lident_labels list0_lident_labels  { $1 :: $2 }
;

lident_labels:
| lident labels { floc (), Some (add_lab $1 $2) }
| anon_binder   { $1 }

anon_binder:
| UNDERSCORE    { floc (), None }
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

quote_uident:
| QUOTE_UIDENT    { mk_id ("'" ^ $1) (floc ()) }
;

quote_lident:
| QUOTE_LIDENT    { mk_id $1 (floc ()) }
;

opaque_quote_lident:
| OPAQUE_QUOTE_LIDENT { mk_id $1 (floc ()) }
;

/* Idents + symbolic operations' names */

ident_rich:
| uident      { $1 }
| lident_rich { $1 }
;

lident_rich:
| lident        { $1 }
| lident_op_id  { $1 }
;

lident_op_id:
| LEFTPAR lident_op RIGHTPAR  { mk_id $2 (floc_i 2) }
| LEFTPAR_STAR_RIGHTPAR       { mk_id (infix "*") (floc ()) }
  /* FIXME: use location of operator star rather than left parenthesis */
;

lident_op:
| prefix_op             { infix $1 }
| prefix_op UNDERSCORE  { prefix $1 }
| EQUAL                 { infix "=" }
| OPPREF                { prefix $1 }
| LEFTSQ RIGHTSQ        { mixfix "[]" }
| LEFTSQ LARROW RIGHTSQ { mixfix "[<-]" }
| LEFTSQ RIGHTSQ LARROW { mixfix "[]<-" }
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
| STRING    { Lstr (Ident.create_label $1) }
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
| list0_theory_or_module EOF { Incremental.close_file () }
;

list0_theory_or_module:
| /* epsilon */                   { () }
| theory list0_theory_or_module   { () }
| module_ list0_theory_or_module  { () }
;

module_head:
| MODULE uident labels  { Incremental.open_module (add_lab $2 $3) }
;

module_:
| module_head list0_pdecl END  { Incremental.close_module () }
;

list0_pdecl:
| /* epsilon */         { () }
| new_decl  list0_pdecl { () }
| new_pdecl list0_pdecl { () }
| new_ns_mo list0_pdecl { () }
;

new_pdecl:
| pdecl { Incremental.new_pdecl (floc ()) $1 }
;

new_ns_mo:
| namespace_head list0_pdecl END
   { Incremental.close_namespace (floc_i 1) $1 }
;

pdecl:
| LET top_ghost lident_rich labels EQUAL fun_expr
    { Dfun (add_lab $3 $4, $2, $6) }
| LET top_ghost lident_rich labels fun_defn
    { Dfun (add_lab $3 $4, $2, $5) }
| LET REC list1_rec_defn
    { Drec $3 }
| VAL top_ghost lident_rich labels type_v
    { Dval (add_lab $3 $4, $2, $5) }
| EXCEPTION uident labels
    { Dexn (add_lab $2 $3, PPTtuple []) }
| EXCEPTION uident labels primitive_type
    { Dexn (add_lab $2 $3, $4) }
;

/*
type_c:
| spec arrow_type_v { $2, $1 }
| simple_type_c     { $1 }
;
*/

type_v:
| arrow_type_v          { $1 }
| COLON primitive_type  { Tpure $2 }
;

arrow_type_v:
| list1_param tail_type_c  { Tarrow ($1, $2) }
;

tail_type_c:
| single_spec spec arrow_type_v   { $3, spec_union $1 $2 }
| COLON simple_type_c             { $2 }
;

simple_type_c:
| primitive_type spec { Tpure $1, $2 }
;

opt_semicolon:
| /* epsilon */ {}
| SEMICOLON     {}
;

list1_rec_defn:
| rec_defn                     { [ $1 ] }
| rec_defn WITH list1_rec_defn { $1 :: $3 }
;

inner_list1_rec_defn:
| inner_rec_defn                           { [ $1 ] }
| inner_rec_defn WITH inner_list1_rec_defn { $1 :: $3 }

rec_defn:
| top_ghost lident_rich labels list1_binder opt_cast spec EQUAL spec expr
   { add_lab $2 $3, $1, ($4, $5, $9, spec_union $6 $8) }
;

inner_rec_defn:
| top_ghost lident_rich labels list1_binder opt_cast spec EQUAL spec final_expr
   { add_lab $2 $3, $1, ($4, $5, $9, spec_union $6 $8) }
;

fun_defn:
| list1_binder opt_cast spec EQUAL spec expr
   { ($1, $2, $6, spec_union $3 $5) }
;

inner_fun_defn:
| list1_binder opt_cast spec EQUAL spec final_expr
   { ($1, $2, $6, spec_union $3 $5) }
;

fun_expr:
| FUN list1_binder spec ARROW spec expr %prec prec_fun
   { ($2, None, $6, spec_union $3 $5) }
;

expr:
| expr_arg
   { match $1.expr_desc with (* break the infix relation chain *)
     | Einfix (l,o,r) -> { $1 with expr_desc = Einnfix (l,o,r) }
     | _ -> $1 }
| expr EQUAL expr
   { mk_infix $1 "=" $3 }
| expr LTGT expr
   { mk_infix $1 "<>" $3 }
| expr LARROW expr
   { match $1.expr_desc with
     | Eidapp (q, [e1]) -> mk_expr (Eassign (e1, q, $3))
     | Eidapp (Qident id, [e1;e2]) when id.id = mixfix "[]" ->
         mk_mixfix3 "[]<-" e1 e2 $3
     | _ -> raise Parsing.Parse_error }
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
| qualid list1_expr_arg
   { mk_expr (Eidapp ($1, $2)) }
| expr_arg_noid list1_expr_arg
   { List.fold_left mk_apply $1 $2 }
| IF final_expr THEN expr ELSE expr
   { mk_expr (Eif ($2, $4, $6)) }
| IF final_expr THEN expr %prec prec_no_else
   { mk_expr (Eif ($2, $4, mk_expr (Etuple []))) }
| expr SEMICOLON expr
   { mk_expr (Esequence ($1, $3)) }
| assertion_kind LEFTBRC lexpr RIGHTBRC
   { mk_expr (Eassert ($1, $3)) }
| expr AMPAMP expr
   { mk_expr (Elazy (LazyAnd, $1, $3)) }
| expr BARBAR expr
   { mk_expr (Elazy (LazyOr, $1, $3)) }
| LET pattern EQUAL final_expr IN expr
   { match $2.pat_desc with
     | PPpvar id -> mk_expr (Elet (id, Gnone, $4, $6))
     | PPpwild -> mk_expr (Elet (id_anonymous (), Gnone, $4, $6))
     | PPptuple [] -> mk_expr (Elet (id_anonymous (), Gnone,
          { $4 with expr_desc = Ecast ($4, PPTtuple []) }, $6))
     | _ -> mk_expr (Ematch ($4, [$2, $6])) }
| LET GHOST pat_arg EQUAL final_expr IN expr
   { match $3.pat_desc with
     | PPpvar id -> mk_expr (Elet (id, Gghost, $5, $7))
     | PPpwild -> mk_expr (Elet (id_anonymous (), Gghost, $5, $7))
     | PPptuple [] -> mk_expr (Elet (id_anonymous (), Gghost,
          { $5 with expr_desc = Ecast ($5, PPTtuple []) }, $7))
     | _ -> mk_expr (Ematch ({ $5 with expr_desc = Eghost $5 }, [$3, $7])) }
| LET lident labels inner_fun_defn IN expr
   { mk_expr (Efun (add_lab $2 $3, Gnone, $4, $6)) }
| LET lident_op_id labels inner_fun_defn IN expr
   { mk_expr (Efun (add_lab $2 $3, Gnone, $4, $6)) }
| LET GHOST lident labels inner_fun_defn IN expr
   { mk_expr (Efun (add_lab $3 $4, Gghost, $5, $7)) }
| LET GHOST lident_op_id labels inner_fun_defn IN expr
   { mk_expr (Efun (add_lab $3 $4, Gghost, $5, $7)) }
| LET lident_op_id labels EQUAL final_expr IN expr
   { mk_expr (Elet (add_lab $2 $3, Gnone, $5, $7)) }
| LET GHOST lident_op_id labels EQUAL final_expr IN expr
   { mk_expr (Elet (add_lab $3 $4, Gghost, $6, $8)) }
| LET LEMMA lident_rich labels EQUAL final_expr IN expr
   { mk_expr (Elet (add_lab $3 $4, Glemma, $6, $8)) }
| LET LEMMA lident_rich labels inner_fun_defn IN expr
   { mk_expr (Efun (add_lab $3 $4, Glemma, $5, $7)) }
| LET REC inner_list1_rec_defn IN expr
   { mk_expr (Erec ($3, $5)) }
| fun_expr
   { mk_expr (Elam $1) }
| VAL top_ghost lident_rich labels tail_type_c IN expr
   { mk_expr (Elet (add_lab $3 $4, $2, mk_expr_i 5 (Eany $5), $7)) }
| MATCH final_expr WITH bar_ program_match_cases END
   { mk_expr (Ematch ($2, $5)) }
| MATCH list2_expr_sep_comma WITH bar_ program_match_cases END
   { mk_expr (Ematch (mk_expr (Etuple $2), $5)) }
| quote_uident COLON expr %prec prec_mark
   { mk_expr (Emark ($1, $3)) }
| LOOP loop_annotation final_expr END
   { mk_expr (Eloop ($2, $3)) }
| WHILE final_expr DO loop_annotation final_expr DONE
   { mk_expr (Ewhile ($2, $4, $5)) }
| FOR lident EQUAL final_expr for_direction final_expr
  DO for_loop_invariant final_expr DONE
   { mk_expr (Efor ($2, $4, $5, $6, $8, $9)) }
| ABSURD
   { mk_expr Eabsurd }
| expr COLON primitive_type
   { mk_expr (Ecast ($1, $3)) }
| RAISE uqualid
   { mk_expr (Eraise ($2, None)) }
| RAISE LEFTPAR uqualid final_expr RIGHTPAR
   { mk_expr (Eraise ($3, Some $4)) }
| TRY final_expr WITH bar_ list1_handler_sep_bar END
   { mk_expr (Etry ($2, $5)) }
| ANY simple_type_c
   { mk_expr (Eany $2) }
| GHOST expr
   { mk_expr (Eghost $2) }
| ABSTRACT expr spec
   { mk_expr (Eabstract($2, $3)) }
| label expr %prec prec_named
   { mk_expr (Enamed ($1, $2)) }
;

final_expr:
| expr opt_semicolon  { $1 }
;

expr_arg:
| qualid          { mk_expr (Eident $1) }
| expr_arg_noid   { $1 }
;

expr_arg_noid:
| constant        { mk_expr (Econst $1) }
| TRUE            { mk_expr Etrue }
| FALSE           { mk_expr Efalse }
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
    { mk_expr (Eidapp ($3, [$1])) }
| LEFTPAR final_expr RIGHTPAR
    { $2 }
| BEGIN final_expr END
    { $2 }
| LEFTPAR RIGHTPAR
    { mk_expr (Etuple []) }
| LEFTPAR list2_expr_sep_comma RIGHTPAR
    { mk_expr (Etuple $2) }
| LEFTBRC list1_field_expr opt_semicolon RIGHTBRC
    { mk_expr (Erecord (List.rev $2)) }
| LEFTBRC expr_arg WITH list1_field_expr opt_semicolon RIGHTBRC
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
| expr_arg                   { [$1] }
| expr_arg list1_expr_arg    { $1 :: $2 }
;

list2_expr_sep_comma:
| final_expr COMMA list1_expr_sep_comma { $1 :: $3 }
;

list1_expr_sep_comma:
| final_expr                            { [$1] }
| final_expr COMMA list1_expr_sep_comma { $1 :: $3 }
;

list1_handler_sep_bar:
| handler                           { [$1] }
| handler BAR list1_handler_sep_bar { $1 :: $3 }
;

handler:
| uqualid ARROW final_expr
    { ($1, None, $3) }
| uqualid pat_arg ARROW final_expr
    { ($1, Some $2, $4) }
;

program_match_cases:
| program_match_case                          { [$1] }
| program_match_case BAR program_match_cases  { $1::$3 }
;

program_match_case:
| pattern ARROW final_expr   { ($1,$3) }
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
| /* epsilon */
    { { loop_invariant = []; loop_variant = [] } }
| invariant loop_annotation
    { let a = $2 in { a with loop_invariant = $1 :: a.loop_invariant } }
| variant loop_annotation
    { let a = $2 in { a with loop_variant = variant_union $1 a.loop_variant } }
;

for_loop_invariant:
| /* epsilon */                 { [] }
| invariant for_loop_invariant  { $1::$2 }
;

type_invariant:
| /* epsilon */             { [] }
| invariant type_invariant  { $1::$2 }
;

spec:
| /* epsilon */     %prec prec_no_spec  { empty_spec }
| single_spec spec                      { spec_union $1 $2 }
;

single_spec:
| REQUIRES LEFTBRC lexpr RIGHTBRC
    { { empty_spec with sp_pre = [$3] } }
| ENSURES LEFTBRC ensures RIGHTBRC
    { { empty_spec with sp_post = [floc_i 3, $3] } }
| RETURNS LEFTBRC returns RIGHTBRC
    { { empty_spec with sp_post = [floc_i 3, $3] } }
| RETURNS LEFTBRC BAR returns RIGHTBRC
    { { empty_spec with sp_post = [floc_i 4, $4] } }
| RAISES LEFTBRC raises RIGHTBRC
    { { empty_spec with sp_xpost = [floc_i 3, $3] } }
| RAISES LEFTBRC BAR raises RIGHTBRC
    { { empty_spec with sp_xpost = [floc_i 4, $4] } }
| READS  LEFTBRC reads RIGHTBRC
    { { empty_spec with sp_reads = $3; sp_checkrw = true } }
| WRITES LEFTBRC writes RIGHTBRC
    { { empty_spec with sp_writes = $3; sp_checkrw = true } }
| RAISES LEFTBRC xsymbols RIGHTBRC
    { { empty_spec with sp_xpost = [floc_i 3, $3] } }
| DIVERGES
    { { empty_spec with sp_diverge = true } }
| variant
    { { empty_spec with sp_variant = $1 } }
;

ensures:
| lexpr { [mk_pat (PPpvar (mk_id "result" (floc ()))), $1] }
;

returns:
| pattern ARROW lexpr             { [$1,$3] }
| pattern ARROW lexpr BAR returns { ($1,$3)::$5 }
;

raises:
| raises_case             { [$1] }
| raises_case BAR raises  { $1::$3 }
;

raises_case:
| uqualid ARROW lexpr
    { $1, { pat_desc = PPptuple []; pat_loc = floc_i 1 }, $3 }
| uqualid pat_arg ARROW lexpr
    { $1, $2, $4 }
;

reads:
| /* epsilon */ { [] }
| list_reads1   { $1 }
;

list_reads1:
| lqualid                   { [$1] }
| lqualid COMMA list_reads1 { $1::$3 }
;

writes:
| /* epsilon */ { [] }
| list_writes1  { $1 }
;

list_writes1:
| lexpr                    { [$1] }
| lexpr COMMA list_writes1 { $1::$3 }
;

xsymbols:
| xsymbol                { [$1] }
| xsymbol COMMA xsymbols { $1::$3 }
;

xsymbol:
| uqualid { $1, mk_pat PPpwild, mk_pp PPtrue }
;

invariant:
| INVARIANT LEFTBRC lexpr RIGHTBRC  { $3 }
;

variant:
| VARIANT LEFTBRC list1_variant RIGHTBRC { $3 }
;

list1_variant:
| single_variant                     { [$1] }
| single_variant COMMA list1_variant { $1::$3 }
;

single_variant:
| lexpr              { $1, None }
| lexpr WITH lqualid { $1, Some $3 }
;

opt_cast:
| /* epsilon */        { None }
| COLON primitive_type { Some $2 }
;

top_ghost:
| /* epsilon */ { Gnone }
| GHOST         { Gghost }
| LEMMA         { Glemma }
;

/*
Local Variables:
compile-command: "unset LANG; make -C ../.."
End:
*/
