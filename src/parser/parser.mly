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

  let pty_of_id i = PPTtyapp (Qident i, [])

  let params_of_binders bl = List.map (function
    | l, None, _, None -> Loc.errorm ~loc:l "cannot determine the type"
    | l, Some i, gh, None -> l, None, gh, pty_of_id i
    | l, i, gh, Some t -> l, i, gh, t) bl

  let quvars_of_lidents ty ll = List.map (function
    | l, None -> Loc.errorm ~loc:l "anonymous binders are not allowed here"
    | _, Some i -> i, ty) ll

  let mk_ppl loc d = { pp_loc = loc; pp_desc = d }
  let mk_pp d = mk_ppl (floc ()) d
(* dead code
  let mk_pp_i i d = mk_ppl (floc_i i) d
*)
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

  let mk_l_prefix op e1 =
    let id = mk_id (prefix op) (floc_i 1) in
    mk_pp (PPapp (Qident id, [e1]))

  let mk_l_infix e1 op e2 =
    let id = mk_id (infix op) (floc_i 2) in
    mk_pp (PPinfix (e1, id, e2))

  let mk_l_mixfix2 op e1 e2 =
    let id = mk_id (mixfix op) (floc_i 2) in
    mk_pp (PPapp (Qident id, [e1;e2]))

  let mk_l_mixfix3 op e1 e2 e3 =
    let id = mk_id (mixfix op) (floc_i 2) in
    mk_pp (PPapp (Qident id, [e1;e2;e3]))

  let () = Exn_printer.register
    (fun fmt exn -> match exn with
      | Parsing.Parse_error -> Format.fprintf fmt "syntax error"
      | _ -> raise exn)

  let mk_expr d = { expr_loc = floc (); expr_desc = d }
  let mk_expr_i i d = { expr_loc = floc_i i; expr_desc = d }

  let cast_body c e = match c with
    | Some pt -> { e with expr_desc = Ecast (e, pt) }
    | None -> e

  let rec mk_apply f = function
    | [] ->
        assert false
    | [a] ->
        Eapply (f, a)
    | a :: l ->
        let loc = Loc.join f.expr_loc a.expr_loc in
        mk_apply { expr_loc = loc; expr_desc = Eapply (f, a) } l

  let mk_apply_id id =
    mk_apply { expr_desc = Eident (Qident id); expr_loc = id.id_loc }

  let mk_mixfix2 op e1 e2 =
    let id = mk_id (mixfix op) (floc_i 2) in
    mk_expr (mk_apply_id id [e1; e2])

  let mk_mixfix3 op e1 e2 e3 =
    let id = mk_id (mixfix op) (floc_i 2) in
    mk_expr (mk_apply_id id [e1; e2; e3])

  let mk_infix e1 op e2 =
    let id = mk_id (infix op) (floc_i 2) in
    mk_expr (Einfix (e1, id, e2))

  let mk_prefix op e1 =
    let id = mk_id (prefix op) (floc_i 1) in
    mk_expr (mk_apply_id id [e1])

  let exit_exn () = Qident (mk_id "%Exit" (floc ()))
  let id_anonymous () = mk_id "_" (floc ())
  let ty_unit () = PPTtuple []

(* dead code
  let id_lt_nat () = Qident (mk_id "lt_nat" (floc ()))
*)

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
  }

  let spec_union s1 s2 = {
    sp_pre     = s1.sp_pre @ s2.sp_pre;
    sp_post    = s1.sp_post @ s2.sp_post;
    sp_xpost   = s1.sp_xpost @ s2.sp_xpost;
    sp_reads   = s1.sp_reads @ s2.sp_reads;
    sp_writes  = s1.sp_writes @ s2.sp_writes;
    sp_variant = variant_union s1.sp_variant s2.sp_variant;
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

%token ABSTRACT ABSURD ANY ASSERT ASSUME BEGIN CHECK DO DONE DOWNTO
%token ENSURES EXCEPTION FOR
%token FUN GHOST INVARIANT LOOP MODEL MODULE MUTABLE PRIVATE RAISE
%token RAISES READS REC REQUIRES RETURNS TO TRY VAL VARIANT WHILE WRITES

/* symbols */

%token AND ARROW
%token BAR
%token COLON COMMA
%token DOT EQUAL FUNC LAMBDA LTGT
%token LEFTPAR LEFTPAR_STAR_RIGHTPAR LEFTSQ
%token LARROW LRARROW OR PRED
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
%nonassoc REQUIRES ENSURES RETURNS RAISES READS WRITES VARIANT
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
;

new_decl:
| decl
   { Incremental.new_decl (floc ()) $1 }
| use_clone
   { Incremental.use_clone (floc ()) $1 }
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
| primitive_type_arg           { $1 }
| lqualid primitive_type_args  { PPTtyapp ($1, $2) }
;

primitive_type_non_lident:
| primitive_type_arg_non_lident           { $1 }
| uqualid DOT lident primitive_type_args  { PPTtyapp (Qdot ($1, $3), $4) }
;

primitive_type_args:
| primitive_type_arg                      { [$1] }
| primitive_type_arg primitive_type_args  { $1 :: $2 }
;

primitive_type_args_non_lident:
| primitive_type_arg_non_lident                      { [$1] }
| primitive_type_arg_non_lident primitive_type_args  { $1 :: $2 }
;

primitive_type_arg:
| lident                         { PPTtyapp (Qident $1, []) }
| primitive_type_arg_non_lident  { $1 }
;

primitive_type_arg_non_lident:
| uqualid DOT lident
   { PPTtyapp (Qdot ($1, $3), []) }
| quote_lident
   { PPTtyvar ($1, false) }
| opaque_quote_lident
   { PPTtyvar ($1, true) }
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

/* Logic expressions */

lexpr:
| lexpr ARROW lexpr
   { infix_pp $1 PPimplies $3 }
| lexpr LRARROW lexpr
   { infix_pp $1 PPiff $3 }
| lexpr OR lexpr
   { infix_pp $1 PPor $3 }
| lexpr BARBAR lexpr
   { infix_pp (mk_pp (PPnamed (Lstr Term.asym_label, $1))) PPor $3 }
| lexpr AND lexpr
   { infix_pp $1 PPand $3 }
| lexpr AMPAMP lexpr
   { infix_pp (mk_pp (PPnamed (Lstr Term.asym_label, $1))) PPand $3 }
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
   { mk_pp (PPapp ($1, $2)) }
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
| MATCH lexpr COMMA list1_lexpr_sep_comma WITH bar_ match_cases END
   { mk_pp (PPmatch (mk_pp (PPtuple ($2::$4)), $7)) }
| EPSILON lident labels COLON primitive_type DOT lexpr
   { mk_pp (PPeps ((add_lab $2 $3, Some $5), $7)) }
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
| qualid            { mk_pp (PPvar $1) }
| constant          { mk_pp (PPconst $1) }
| TRUE              { mk_pp PPtrue }
| FALSE             { mk_pp PPfalse }
| OPPREF lexpr_arg  { mk_l_prefix $1 $2 }
| lexpr_sub         { $1 }
| quote_uident      { mk_pp (PPvar (Qident $1)) }
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
| list1_binder  { params_of_binders $1 }
;

list1_binder:
| binder              { $1 }
| binder list1_binder { $1 @ $2 }
;

binder:
| quote_lident
   { [floc (), None, false, Some (PPTtyvar ($1, false))] }
| opaque_quote_lident
   { [floc (), None, false, Some (PPTtyvar ($1, true))] }
| lqualid_qualified
   { [floc (), None, false, Some (PPTtyapp ($1, []))] }
| lident labels
   { [floc (), Some (add_lab $1 $2), false, None] }
| UNDERSCORE
   { Loc.errorm ~loc:(floc ()) "untyped anonymous parameters are not allowed" }
| LEFTPAR RIGHTPAR
   { [floc (), None, false, Some (PPTtuple [])] }
| LEFTPAR binder_in RIGHTPAR
   { $2 }
| LEFTPAR GHOST binder_in RIGHTPAR
   { List.map (fun (l,i,_,t) -> (l,i,true,t)) $3 }
| LEFTPAR binder_type COMMA list1_primitive_type_sep_comma RIGHTPAR
   { [floc (), None, false, Some (PPTtuple ($2::$4))] }
;

binder_in:
| lident labels
   { [floc (), Some (add_lab $1 $2), false, None] }
| UNDERSCORE
   { Loc.errorm ~loc:(floc ()) "untyped anonymous parameters are not allowed" }
| binder_type_rest
   { [floc (), None, false, Some $1] }
| binder_vars COLON primitive_type
   { List.map (fun (l,v) -> l, v, false, Some $3) $1 }
;

binder_type:
| lident            { PPTtyapp (Qident $1, []) }
| binder_type_rest  { $1 }
;

binder_type_rest:
| lident list1_lident
   { PPTtyapp (Qident $1, List.map pty_of_id $2) }
| lident list0_lident primitive_type_args_non_lident
   { PPTtyapp (Qident $1, List.map pty_of_id $2 @ $3) }
| primitive_type_non_lident
   { $1 }
;

binder_vars:
| list1_lident
   { List.map (fun id -> id.id_loc, Some id) $1 }
| list1_lident UNDERSCORE list0_lident_labels
   { List.map (fun id -> id.id_loc, Some id) $1 @ (floc_i 2, None) :: $3 }
| lident list1_lident label labels list0_lident_labels
   { let l = match List.rev ($1 :: $2) with
       | i :: l -> add_lab i ($3 :: $4) :: l
       | [] -> assert false in
     List.fold_left (fun acc id -> (id.id_loc, Some id) :: acc) $5 l }
| lident label labels list0_lident_labels
   { ($1.id_loc, Some (add_lab $1 ($2 :: $3))) :: $4 }
| UNDERSCORE list0_lident_labels
   { (floc_i 1, None) :: $2 }
;

list0_lident:
| /* epsilon */ { [] }
| list1_lident  { $1 }
;

list1_lident:
| lident list0_lident  { $1 :: $2 }
;

list1_quant_vars:
| quant_vars                        { $1 }
| quant_vars COMMA list1_quant_vars { $1 @ $3 }
;

quant_vars:
| list1_lident_labels COLON primitive_type
   { quvars_of_lidents (Some $3) $1 }
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

lqualid_qualified:
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
;

new_pdecl:
| pdecl { Incremental.new_pdecl (floc ()) $1 }
;

pdecl:
| LET ghost lident_rich labels fun_defn
    { Dlet (add_lab $3 $4, $2, $5) }
| LET ghost lident_rich labels EQUAL fun_expr
    { Dlet (add_lab $3 $4, $2, $6) }
| LET REC list1_rec_defn
    { Dletrec $3 }
| VAL ghost lident_rich labels type_v
    { Dparam (add_lab $3 $4, $2, $5) }
| EXCEPTION uident labels
    { Dexn (add_lab $2 $3, ty_unit ()) }
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

rec_defn:
| ghost lident_rich labels list1_binder opt_cast spec EQUAL spec expr
   { floc (), add_lab $2 $3, $1, $4, (cast_body $5 $9, spec_union $6 $8) }
;

fun_defn:
| list1_binder opt_cast spec EQUAL spec expr
   { mk_expr_i 6 (Efun ($1, (cast_body $2 $6, spec_union $3 $5))) }
;

fun_expr:
| FUN list1_binder spec ARROW spec expr %prec prec_fun
   { mk_expr (Efun ($2, ($6, spec_union $3 $5))) }
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
| expr_arg list1_expr_arg
   { mk_expr (mk_apply $1 $2) }
| IF expr THEN expr ELSE expr
   { mk_expr (Eif ($2, $4, $6)) }
| IF expr THEN expr %prec prec_no_else
   { mk_expr (Eif ($2, $4, mk_expr (Etuple []))) }
| expr SEMICOLON expr
   { mk_expr (Esequence ($1, $3)) }
| assertion_kind LEFTBRC lexpr RIGHTBRC
   { mk_expr (Eassert ($1, $3)) }
| expr AMPAMP expr
   { mk_expr (Elazy (LazyAnd, $1, $3)) }
| expr BARBAR expr
   { mk_expr (Elazy (LazyOr, $1, $3)) }
| LET pattern EQUAL expr IN expr
   { match $2.pat_desc with
     | PPpvar id -> mk_expr (Elet (id, false, $4, $6))
     | PPpwild -> mk_expr (Elet (id_anonymous (), false, $4, $6))
     | PPptuple [] -> mk_expr (Elet (id_anonymous (), false,
          { $4 with expr_desc = Ecast ($4, PPTtuple []) }, $6))
     | _ -> mk_expr (Ematch ($4, [$2, $6])) }
| LET GHOST pattern EQUAL expr IN expr
   { match $3.pat_desc with
     | PPpvar id -> mk_expr (Elet (id, true, $5, $7))
     | PPpwild -> mk_expr (Elet (id_anonymous (), true, $5, $7))
     | PPptuple [] -> mk_expr (Elet (id_anonymous (), true,
          { $5 with expr_desc = Ecast ($5, PPTtuple []) }, $7))
     | _ -> Loc.errorm ~loc:(floc_i 3) "`ghost' cannot come before a pattern" }
| LET lident labels fun_defn IN expr
   { mk_expr (Elet (add_lab $2 $3, false, $4, $6)) }
| LET lident_op_id labels fun_defn IN expr
   { mk_expr (Elet (add_lab $2 $3, false, $4, $6)) }
| LET GHOST lident labels fun_defn IN expr
   { mk_expr (Elet (add_lab $3 $4, true, $5, $7)) }
| LET GHOST lident_op_id labels fun_defn IN expr
   { mk_expr (Elet (add_lab $3 $4, true, $5, $7)) }
| LET REC list1_rec_defn IN expr
   { mk_expr (Eletrec ($3, $5)) }
| fun_expr
   { $1 }
| MATCH expr WITH bar_ program_match_cases END
   { mk_expr (Ematch ($2, $5)) }
| MATCH expr COMMA list1_expr_sep_comma WITH bar_ program_match_cases END
   { mk_expr (Ematch (mk_expr (Etuple ($2::$4)), $7)) }
| quote_uident COLON expr %prec prec_mark
   { mk_expr (Emark ($1, $3)) }
| LOOP loop_annotation expr END
   { mk_expr (Eloop ($2, $3)) }
| WHILE expr DO loop_annotation expr DONE
   { mk_expr
       (Etry
          (mk_expr
             (Eloop ($4,
                     mk_expr (Eif ($2, $5,
                                   mk_expr (Eraise (exit_exn (), None)))))),
          [exit_exn (), mk_pat (PPptuple []), mk_expr (Etuple [])])) }
| FOR lident EQUAL expr for_direction expr DO for_loop_invariant expr DONE
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
| GHOST expr
   { mk_expr (Eghost $2) }
| ABSTRACT expr spec
   { mk_expr (Eabstract($2, $3)) }
| label expr %prec prec_named
   { mk_expr (Enamed ($1, $2)) }
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

list1_expr_sep_comma:
| expr                            { [$1] }
| expr COMMA list1_expr_sep_comma { $1 :: $3 }
;

list1_handler_sep_bar:
| handler                           { [$1] }
| handler BAR list1_handler_sep_bar { $1 :: $3 }
;

handler:
| uqualid ARROW expr
    { ($1, { pat_desc = PPptuple []; pat_loc = floc_i 1 }, $3) }
| uqualid pat_arg ARROW expr
    { ($1, $2, $4) }
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
| READS  LEFTBRC effect RIGHTBRC
    { { empty_spec with sp_reads = $3 } }
| WRITES LEFTBRC effect RIGHTBRC
    { { empty_spec with sp_writes = $3 } }
| RAISES LEFTBRC xsymbols RIGHTBRC
    { { empty_spec with sp_xpost = [floc_i 3, $3] } }
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

effect:
| lexpr              { [$1] }
| lexpr COMMA effect { $1::$3 }
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

ghost:
| /* epsilon */ { false }
| GHOST         { true }
;

/*
Local Variables:
compile-command: "unset LANG; make -C ../.."
End:
*/
