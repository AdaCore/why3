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

  open Parsing
  open Lexing
  open Ptree
  open Pgm_ptree

  let loc () = (symbol_start_pos (), symbol_end_pos ())
  let loc_i i = (rhs_start_pos i, rhs_end_pos i)
  let loc_ij i j = (rhs_start_pos i, rhs_end_pos j)

  let mk_expr d = { expr_loc = loc (); expr_info = (); expr_desc = d }
  let mk_expr_i i d = { expr_loc = loc_i i; expr_info = (); expr_desc = d }
 
  (* FIXME: factorize with parser/parser.mly *)
  let infix s = "infix " ^ s
  let prefix s = "prefix " ^ s
  let postfix s = "postfix " ^ s

  let join (b,_) (_,e) = (b,e)

  let rec mk_apply f = function
    | [] -> 
	assert false
    | [a] -> 
	Eapply (f, a)
    | a :: l -> 
	let loc = join f.expr_loc a.expr_loc in 
	mk_apply { expr_loc = loc; expr_info = (); expr_desc = Eapply (f, a) } l

  let mk_apply_id id = 
    let e = 
      { expr_desc = Eident (Qident id); expr_info = (); expr_loc = id.id_loc } 
    in
    mk_apply e
      
  let mk_infix e1 op e2 =
    let id = { id = infix op; id_loc = loc_i 2 } in
    mk_expr (mk_apply_id id [e1; e2])
     
  let mk_prefix op e1 =
    let id = { id = prefix op; id_loc = loc_i 1 } in
    mk_expr (mk_apply_id id [e1])
     

  (* parsing LOGIC strings using functions from src/parser/
     requires proper relocation *)

  let reloc loc lb =
    lb.lex_curr_p <- loc;
    lb.lex_abs_pos <- loc.pos_cnum

  let parse_string f loc s =
    let lb = Lexing.from_string s in
    reloc loc lb;
    f lb
    
  let logic_list0_decl (loc, s) = parse_string Lexer.parse_list0_decl loc s

  let lexpr (loc, s) = parse_string Lexer.parse_lexpr loc s

%}

/* Tokens */ 

%token <string> LIDENT UIDENT
%token <string> INTEGER
%token <string> OP0 OP1 OP2 OP3
%token <Ptree.real_constant> REAL
%token <string> STRING
%token <Lexing.position * string> LOGIC

/* keywords */

%token ABSURD AND AS ASSERT ASSUME BEGIN CHECK DO DONE ELSE END EXCEPTION FOR
%token FUN GHOST IF IN INVARIANT LET MATCH NOT RAISE RAISES READS REC 
%token RETURNS THEN TRY TYPE VARIANT VOID WHILE WITH WRITES

/* symbols */

%token UNDERSCORE QUOTE COMMA LEFTPAR RIGHTPAR COLON SEMICOLON
%token COLONEQUAL ARROW EQUAL AT DOT LEFTSQ RIGHTSQ BANG
%token LEFTBLEFTB RIGHTBRIGHTB BAR BARBAR AMPAMP BIGARROW 
%token EOF

/* Precedences */

%nonassoc prec_recfun
%nonassoc prec_fun
%left LEFTB LEFTBLEFTB
%left prec_simple

%left COLON 

%left prec_letrec
%left IN
%nonassoc GHOST

%right SEMICOLON

%left prec_no_else
%left ELSE

%left COLONEQUAL
%right ARROW LRARROW
%right BARBAR
%right AMPAMP
%right prec_if
%left EQUAL OP0
%left OP1
%left OP2
%left OP3
%nonassoc prefix_op
%right unary_op
%left prec_app
%left prec_ident
%left LEFTSQ

%nonassoc prec_decls
%nonassoc LOGIC TYPE INDUCTIVE

/* Entry points */

%type <Pgm_ptree.file> file
%start file

%%

file:
| list0_decl EOF { $1 }
;

list0_decl:
| /* epsilon */
   { [] }
| list1_decl 
   { $1 }
;

list1_decl:
| decl 
   { [$1] }
| decl list1_decl 
   { $1 :: $2 }
;

decl:
| LOGIC
    { Dlogic (logic_list0_decl $1) }
| LET lident EQUAL expr
    { Dcode ($2, $4) }
;

lident:
| LIDENT
    { { id = $1; id_loc = loc () } }
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

expr:
| simple_expr %prec prec_simple 
   { $1 }
| expr EQUAL expr 
   { mk_infix $1 "=" $3 }
| expr COLONEQUAL expr 
   { mk_infix $1 ":=" $3 }
| expr OP0 expr 
   { mk_infix $1 $2 $3 }
| expr OP1 expr 
   { mk_infix $1 $2 $3 }
| expr OP2 expr 
   { mk_infix $1 $2 $3 }
| expr OP3 expr 
   { mk_infix $1 $2 $3 }
| any_op expr %prec prefix_op
   { mk_prefix $1 $2 }
| simple_expr list1_simple_expr %prec prec_app
   { mk_expr (mk_apply $1 $2) }
| IF expr THEN expr ELSE expr
   { mk_expr (Eif ($2, $4, $6)) }
| IF expr THEN expr %prec prec_no_else
   { mk_expr (Eif ($2, $4, mk_expr Eskip)) }
| expr SEMICOLON expr
   { mk_expr (Esequence ($1, $3)) }
| assertion_kind LOGIC
   { mk_expr (Eassert ($1, lexpr $2)) }
| expr AMPAMP expr
   { mk_expr (Elazy_and ($1, $3)) }
| expr BARBAR expr
   { mk_expr (Elazy_or ($1, $3)) }
| LET lident EQUAL expr IN expr
   { mk_expr (Elet ($2, $4, $6)) }
| GHOST expr
   { mk_expr (Eghost $2) }
| uident COLON expr
   { mk_expr (Elabel ($1, $3)) }
| WHILE expr DO loop_annotation expr DONE
   { mk_expr (Ewhile ($2, $4, $5)) }
;

simple_expr:
| constant
    { mk_expr (Econstant $1) }
| BANG expr
    { mk_prefix "!" $2 }
| lqualid 
    { mk_expr (Eident $1) }
| LEFTPAR expr RIGHTPAR
    { $2 }
| BEGIN expr END
    { $2 }
| LEFTPAR RIGHTPAR
    { mk_expr Eskip }
| BEGIN END
    { mk_expr Eskip }
;

list1_simple_expr:
| simple_expr %prec prec_simple { [$1] }
| simple_expr list1_simple_expr { $1 :: $2 }
;

assertion_kind:
| ASSERT { Aassert }
| ASSUME { Aassume }
| CHECK  { Acheck  }
;

loop_annotation:
| loop_invariant loop_variant { { loop_invariant = $1; loop_variant = $2 } }
;

loop_invariant:
| INVARIANT LOGIC { Some (lexpr $2) }
| /* epsilon */   { None            }
;

loop_variant:
| VARIANT LOGIC { Some (lexpr $2) }
| /* epsilon */ { None            }
;

constant:
| INTEGER
   { Term.ConstInt $1 }
| REAL
   { Term.ConstReal $1 }
;

/*****

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
| LEFTPAR UNDERSCORE lident_op UNDERSCORE RIGHTPAR 
    { { id = infix $3; id_loc = loc () } }
| LEFTPAR lident_op UNDERSCORE RIGHTPAR 
    { { id = prefix $2; id_loc = loc () } }
/*
| LEFTPAR UNDERSCORE lident_op RIGHTPAR 
    { { id = postfix $3; id_loc = loc () } }
* /
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
| /* epsilon * /                          { [] }
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
| /* epsilon * /                                   { [] }
| LEFTPAR list1_primitive_type_sep_comma RIGHTPAR { $2 }

logic_type_option:
| /* epsilon * /        { None }
| COLON primitive_type { Some $2 }
;

type_var:
| QUOTE ident { $2 }
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

list0_ident_sep_comma:
| /* epsilon * /         { [] }
| list1_ident_sep_comma { $1 }
;

list1_ident_sep_comma:
| ident                             { [$1] }
| ident COMMA list1_ident_sep_comma { $1 :: $3 }
;

decl:
| INCLUDE STRING
   { Include (loc_i 2,$2) }
| LET ident EQUAL expr
   { Program (loc_i 2,$2, $4) }
| LET ident binders EQUAL list0_bracket_assertion expr
   { Program (loc_i 2,$2, locate (Slam ($3, $5, force_function_post $6))) }
| LET REC recfun
   { let (loc,p) = $3 in Program (loc,rec_name p, locate p) }
| EXCEPTION ident
   { Exception (loc (), $2, None) }
| EXCEPTION ident OF primitive_type
   { Exception (loc (), $2, Some $4) }
| PARAMETER list1_ident_sep_comma COLON type_v
   { Parameter (loc_i 3, $2, $4) }

type_v:
| simple_type_v ARROW type_c
   { PVarrow ([Ident.anonymous, $1], $3) }
| ident COLON simple_type_v ARROW type_c
   { PVarrow ([($1, $3)], $5) }
| simple_type_v
   { $1 }
;

simple_type_v:
| primitive_type REF      { PVref $1 }
| primitive_type          { PVpure $1 }
| LEFTPAR type_v RIGHTPAR { $2 }
;

type_c:
| LEFTB opt_assertion RIGHTB result effects LEFTB opt_post_condition RIGHTB
   { let id,v = $4 in
     { pc_result_name = id; pc_result_type = v;
       pc_effect = $5; pc_pre = list_of_some $2; pc_post = $7 } }
| type_v
   { ptype_c_of_v $1 }
;

result:
| RETURNS ident COLON type_v { $2, $4 }
| type_v                     { Ident.result, $1 }
;

effects:
| opt_reads opt_writes opt_raises
    { { pe_reads = $1; pe_writes = $2; pe_raises = $3 } }
;

opt_reads:
| /* epsilon * /               { [] }
| READS list0_ident_sep_comma { $2 }
;

opt_writes:
| /* epsilon * /                { [] }
| WRITES list0_ident_sep_comma { $2 }
;

opt_raises:
| /* epsilon * /                { [] }
| RAISES list0_ident_sep_comma { $2 }
;

opt_assertion:
| /* epsilon * /  { None }
| assertion      { Some $1 }
;

assertion:
| lexpr          
    { { pa_name = Anonymous; pa_value = $1; pa_loc = loc () } }
| lexpr AS ident 
    { { pa_name = Name $3; pa_value = $1; pa_loc = loc () } }
;

opt_post_condition:
| /* epsilon * /  { None }
| post_condition { Some $1 }
;

post_condition:
| assertion 
   { $1, [] }
| assertion BAR list1_exn_condition_sep_bar
   { $1, $3 }
| BAR list1_exn_condition_sep_bar
   { Format.eprintf "%awarning: no postcondition; false inserted@\n" 
       Loc.report_position (loc ());
     (* if Options.werror then exit 1; *)
     ({ pa_name = Anonymous; pa_value = mk_pp PPfalse; pa_loc = loc () }, $2) }
;

bracket_assertion:
| LEFTB assertion RIGHTB { $2 }
;

list1_bracket_assertion:
| bracket_assertion                         { [$1] }
| bracket_assertion list1_bracket_assertion { $1 :: $2 }
;

list0_bracket_assertion:
| /* epsilon * /           { [] }
| LEFTB RIGHTB            { [] }
| list1_bracket_assertion { $1 }
;

list1_exn_condition_sep_bar:
| exn_condition                                 { [$1] }
| exn_condition BAR list1_exn_condition_sep_bar { $1 :: $3 }
;

exn_condition:
| ident BIGARROW assertion { $1,$3 }
;

expr:
| simple_expr %prec prec_simple 
   { $1 }
| ident COLONEQUAL expr
   { locate 
       (Sapp (locate (Sapp (locate (Svar Ident.ref_set), 
			    locate_i 1 (Svar $1))),
	      $3)) }
| ident LEFTSQ expr RIGHTSQ COLONEQUAL expr
   { locate 
       (Sapp (locate 
		(Sapp (locate 
			 (Sapp (locate (Svar Ident.array_set), 
				locate_i 1 (Svar $1))),
			 $3)),
		$6)) }
| IF expr THEN expr ELSE expr
   { locate (Sif ($2, $4, $6)) }
| IF expr THEN expr %prec prec_no_else
   { locate (Sif ($2, $4, locate (Sconst ConstUnit))) }
| WHILE expr DO invariant_variant expr DONE
   { (* syntactic suget for
        try loop { invariant variant } if b then e else raise Exit
        with Exit -> void end *)
     let inv,var = $4 in
     locate 
       (Stry
	  (locate 
	     (Sloop (inv, var, 
		     locate 
		       (Sif ($2, $5,
			     locate (Sraise (exit_exn, None, None)))))),
	     [((exit_exn, None), locate (Sconst ConstUnit))])) }
| IDENT COLON expr
   { locate (Slabel ($1, $3)) }
| LET ident EQUAL expr IN expr
   { locate (Sletin ($2, $4, $6)) }
| LET ident EQUAL REF expr IN expr
   { locate (Sletref ($2, $5, $7)) }
| FUN binders ARROW list0_bracket_assertion expr %prec prec_fun
   { locate (Slam ($2, $4, force_function_post $5)) }
| LET ident binders EQUAL list0_bracket_assertion expr IN expr
   { let b =  force_function_post ~warn:true $6 in
     locate (Sletin ($2, locate (Slam ($3, $5, b)), $8)) }
| LET REC recfun %prec prec_letrec
   { let _loc,p = $3 in locate p }
| LET REC recfun IN expr
   { let _loc,p = $3 in locate (Sletin (rec_name p, locate p, $5)) }
| RAISE ident opt_cast
   { locate (Sraise ($2, None, $3)) }
| RAISE LEFTPAR ident expr RIGHTPAR opt_cast
   { locate (Sraise ($3, Some $4 , $6)) }
| TRY expr WITH bar_ list1_handler_sep_bar END
   { locate (Stry ($2, $5)) }
| ABSURD opt_cast
   { locate (Sabsurd $2) }
| simple_expr list1_simple_expr %prec prec_app
   { locate (app $1 $2) }
| expr BARBAR expr
   { locate (Slazy_or ($1, $3))
     (* let ptrue = locate (Sconst (ConstBool true)) in
     locate (Sif ($1, ptrue, $3)) *) }
| expr AMPAMP expr
   { locate (Slazy_and ($1, $3))
     (* let pf = locate (Sconst (ConstBool false)) in
     locate (Sif ($1, $3, pf)) *) }
| NOT expr
   { locate (Snot $2)
     (* let pf = locate (Sconst (ConstBool false)) in
     let pt = locate (Sconst (ConstBool true)) in
     locate (Sif ($2, pf, pt)) *) }
| expr relation_id expr %prec prec_relation
   { bin_op $2 $1 $3 }
| expr PLUS expr
   { bin_op (loc_i 2, Ident.t_add) $1 $3 }
| expr MINUS expr
   { bin_op (loc_i 2, Ident.t_sub) $1 $3 }
| expr TIMES expr
   { bin_op (loc_i 2, Ident.t_mul) $1 $3 }
| expr SLASH expr
   { bin_op (loc_i 2, Ident.t_div) $1 $3 }
| expr PERCENT expr
   { bin_op (loc_i 2, Ident.t_mod_int) $1 $3 }
| MINUS expr %prec uminus
   { un_op (loc_i 1, Ident.t_neg) $2 }
| expr SEMICOLON expr
   { locate (Sseq ($1, $3)) }
| ASSERT list1_bracket_assertion SEMICOLON expr 
   { locate (Sassert (`ASSERT,$2, $4)) }
| CHECK list1_bracket_assertion SEMICOLON expr 
   { locate (Sassert (`CHECK,$2, $4)) }
| expr LEFTB post_condition RIGHTB
   { locate (Spost ($1, $3, Transparent)) }
| expr LEFTBLEFTB post_condition RIGHTBRIGHTB
   { locate (Spost ($1, $3, Opaque)) }
;

simple_expr:
| ident %prec prec_ident
   { locate (Svar $1) }
| INTEGER
   { locate (Sconst (ConstInt $1)) }
| FLOAT
   { let f = $1 in locate (Sconst (ConstFloat f)) }
| VOID
   { locate (Sconst ConstUnit) }
| TRUE
   { locate (Sconst (ConstBool true)) }
| FALSE
   { locate (Sconst (ConstBool false)) }
| BANG ident
   { locate (Sderef $2) }
| ident LEFTSQ expr RIGHTSQ
   { locate 
       (Sapp (locate (Sapp (locate (Svar Ident.array_get), 
			    locate_i 1 (Svar $1))),
	      $3)) }
| LEFTSQ type_c RIGHTSQ
   { locate (Sany $2) }
| LEFTPAR expr RIGHTPAR
   { $2 }
| BEGIN expr END
   { $2 }
;

relation_id:
| LT    { loc (), Ident.t_lt }
| LE    { loc (), Ident.t_le }
| GT    { loc (), Ident.t_gt }
| GE    { loc (), Ident.t_ge }
| EQUAL { loc (), Ident.t_eq }
| NOTEQ { loc (), Ident.t_neq }
;

list1_simple_expr:
| simple_expr %prec prec_simple { [$1] }
| simple_expr list1_simple_expr { $1 :: $2 }
;

list1_handler_sep_bar:
| handler                           { [$1] }
| handler BAR list1_handler_sep_bar { $1 :: $3 }
;

handler:
| ident ARROW expr       { (($1, None), $3) }
| ident ident ARROW expr { (($1, Some $2), $4) }
;

opt_cast:
| /* epsilon * / { None }
| COLON type_v  { Some $2 }
;

invariant_variant:
| /* epsilon * / { None, None }
| LEFTB opt_invariant RIGHTB { $2, None }
| LEFTB opt_invariant VARIANT variant RIGHTB { $2, Some $4 }
;

opt_invariant:
| /* epsilon * /       { None }
| INVARIANT assertion { Some $2 }
;

recfun:
| ident binders COLON type_v opt_variant EQUAL 
  list0_bracket_assertion expr %prec prec_recfun
   { (loc_i 1),Srec ($1, $2, $4, $5, $7, force_function_post $8) }
;

opt_variant:
| LEFTB VARIANT variant RIGHTB { Some $3 } 
| /* epsilon * /                { None }
;

variant:
| lexpr FOR ident { ($1, $3) }
| lexpr           { ($1, Ident.t_zwf_zero) }
;

binders:
| list1_binder { List.flatten $1 }
;

list1_binder:
| binder              { [$1] }
| binder list1_binder { $1 :: $2 }
;

binder:
| LEFTPAR RIGHTPAR
   { [Ident.anonymous, PVpure PPTunit] }
| LEFTPAR list1_ident_sep_comma COLON type_v RIGHTPAR 
   { List.map (fun s -> (s, $4)) $2 }
;

*****/

