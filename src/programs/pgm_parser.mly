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
  open Why
  open Ptree
  open Pgm_ptree

  let loc () = (symbol_start_pos (), symbol_end_pos ())
  let loc_i i = (rhs_start_pos i, rhs_end_pos i)
  let loc_ij i j = (rhs_start_pos i, rhs_end_pos j)

  let mk_expr d = { expr_loc = loc (); expr_desc = d }
  let mk_expr_i i d = { expr_loc = loc_i i; expr_desc = d }

  let mk_pat p = { pat_loc = loc (); pat_desc = p }

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
	mk_apply { expr_loc = loc; expr_desc = Eapply (f, a) } l

  let mk_apply_id id = 
    let e = 
      { expr_desc = Eident (Qident id); expr_loc = id.id_loc } 
    in
    mk_apply e
      
  let mk_infix e1 op e2 =
    let id = { id = infix op; id_loc = loc_i 2 } in
    mk_expr (mk_apply_id id [e1; e2])
     
  let mk_binop e1 op e2 =
    let id = { id = op; id_loc = loc_i 2 } in
    mk_expr (mk_apply_id id [e1; e2])
     
  let mk_prefix op e1 =
    let id = { id = prefix op; id_loc = loc_i 1 } in
    mk_expr (mk_apply_id id [e1])

  let id_unit () = { id = "Unit"; id_loc = loc () }
  let id_result () = { id = "result"; id_loc = loc () }
  let id_anonymous () = { id = "_"; id_loc = loc () }

  let lexpr_true () = { Ptree.pp_loc = loc (); Ptree.pp_desc = PPtrue }
  let lexpr_false () = { Ptree.pp_loc = loc (); Ptree.pp_desc = PPfalse }

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

  let empty_effect = { pe_reads = []; pe_writes = []; pe_raises = [] }

%}

/* Tokens */ 

%token <string> LIDENT UIDENT
%token <string> INTEGER
%token <string> OP0 OP1 OP2 OP3
%token <Why.Ptree.real_constant> REAL
%token <string> STRING
%token <Lexing.position * string> LOGIC

/* keywords */

%token ABSURD AND AS ASSERT ASSUME BEGIN CHECK DO DONE ELSE END
%token EXCEPTION FOR
%token FUN GHOST IF IN INVARIANT LABEL LET MATCH NOT OF PARAMETER
%token RAISE RAISES READS REC 
%token THEN TRY TYPE VARIANT WHILE WITH WRITES

/* symbols */

%token UNDERSCORE QUOTE COMMA LEFTPAR RIGHTPAR COLON SEMICOLON
%token COLONEQUAL ARROW EQUAL AT DOT LEFTSQ RIGHTSQ BANG
%token LEFTBLEFTB RIGHTBRIGHTB BAR BARBAR AMPAMP BIGARROW 
%token EOF

/* Precedences */

%nonassoc prec_recfun
%nonassoc prec_triple
%left LEFTBLEFTB
%left prec_simple

%left COLON 

%left prec_letrec
%left IN
%nonassoc GHOST

%right SEMICOLON

%left prec_no_else
%left ELSE

%left COLONEQUAL
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
    { Dlet ($2, $4) }
| LET lident list1_type_v_binder EQUAL triple
    { Dlet ($2, mk_expr_i 3 (Efun ($3, $5))) }
| LET REC list1_recfun_sep_and 
    { Dletrec $3 }
| PARAMETER lident COLON type_v
    { Dparam ($2, $4) }
| EXCEPTION uident 
    { Dexn ($2, None) }
| EXCEPTION uident OF pure_type
    { Dexn ($2, Some $4) }
;

list1_recfun_sep_and:
| recfun                          { [ $1 ] }
| recfun AND list1_recfun_sep_and { $1 :: $3 }
;

recfun:
| lident list1_type_v_binder opt_variant EQUAL triple
   { $1, $2, $3, $5 }
;

lident:
| LIDENT { { id = $1; id_loc = loc () } }
;

uident:
| UIDENT { { id = $1; id_loc = loc () } }
;

ident:
| uident { $1 }
| lident { $1 }
;

any_op:
| OP0   { $1 }
| OP2   { $1 }
| OP3   { $1 }
;

qualid:
| ident             { Qident $1 }
| uqualid DOT ident { Qdot ($1, $3) }
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
   { mk_binop $1 "eq_bool" $3 }
| expr OP0 expr 
   { mk_binop $1 ($2 ^ "_bool") $3 }
| expr OP1 expr 
   { mk_infix $1 $2 $3 }
| expr OP2 expr 
   { mk_infix $1 $2 $3 }
| expr OP3 expr 
   { mk_infix $1 $2 $3 }
| NOT expr %prec prefix_op
   { mk_expr (mk_apply_id { id = "notb"; id_loc = loc () } [$2]) }
| any_op expr %prec prefix_op
   { mk_prefix $1 $2 }
| expr COLONEQUAL expr 
   { mk_infix $1 ":=" $3 }
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
   { mk_expr (Elazy (LazyAnd, $1, $3)) }
| expr BARBAR expr
   { mk_expr (Elazy (LazyOr, $1, $3)) }
| LET lident EQUAL expr IN expr
   { mk_expr (Elet ($2, $4, $6)) }
| LET lident list1_type_v_binder EQUAL triple IN expr
   { mk_expr (Elet ($2, mk_expr_i 3 (Efun ($3, $5)), $7)) }
| LET REC list1_recfun_sep_and IN expr
   { mk_expr (Eletrec ($3, $5)) }
| FUN list1_type_v_binder ARROW triple
   { mk_expr (Efun ($2, $4)) }
| MATCH list1_expr_sep_comma WITH option_bar match_cases END
   { mk_expr (Ematch ($2, $5)) }
| GHOST expr
   { mk_expr (Eghost $2) }
| LABEL uident COLON expr
   { mk_expr (Elabel ($2, $4)) }
| WHILE expr DO loop_annotation expr DONE
   { mk_expr (Ewhile ($2, $4, $5)) }
| ABSURD
   { mk_expr Eabsurd }
| expr COLON pure_type
   { mk_expr (Ecast ($1, $3)) }
| RAISE uident
   { mk_expr (Eraise ($2, None)) }
| RAISE LEFTPAR uident expr RIGHTPAR
   { mk_expr (Eraise ($3, Some $4)) }
;

triple:
| LOGIC expr LOGIC
  { lexpr $1, $2, lexpr $3 }
| expr %prec prec_triple
  { lexpr_true (), $1, lexpr_true () }
;

simple_expr:
| constant
    { mk_expr (Econstant $1) }
| BANG simple_expr
    { mk_prefix "!" $2 }
| qualid 
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

list1_expr_sep_comma:
| expr                            { [$1] }
| expr COMMA list1_expr_sep_comma { $1 :: $3 }
;

option_bar:
| /* epsilon */ { () }
| BAR           { () }
;

match_cases:
| match_case                  { [$1] }
| match_case BAR match_cases  { $1::$3 }
;

match_case:
| list1_pat_sep_comma ARROW expr { ($1,$3) }
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
| LEFTPAR pattern RIGHTPAR                      { $2 }
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

type_var:
| QUOTE ident { $2 }
;

pure_type:
| type_var 
   { PPTtyvar $1 }
| lqualid
   { PPTtyapp ([], $1) }
| pure_type lqualid
   { PPTtyapp ([$1], $2) }
| LEFTPAR pure_type COMMA list1_pure_type_sep_comma RIGHTPAR lqualid
   { PPTtyapp ($2 :: $4, $6) }
;

list1_pure_type_sep_comma:
| pure_type                                      { [$1] }
| pure_type COMMA list1_pure_type_sep_comma { $1 :: $3 }
;

list1_type_v_binder:
| type_v_binder                     { [$1] }
| type_v_binder list1_type_v_binder { $1 :: $2 }
;

type_v_binder:
| lident                               { $1, None }
| LEFTPAR lident COLON type_v RIGHTPAR { $2, Some $4 }
;

opt_colon_spec:
| /* epsilon */ { None }
| COLON type_c  { Some $2 }
;

type_v:
| simple_type_v
   { $1 }
| simple_type_v ARROW type_c
   { Tarrow ([id_anonymous (), Some $1], $3) }
| lident COLON simple_type_v ARROW type_c
   { Tarrow ([$1, Some $3], $5) }
;

simple_type_v:
| pure_type
    { Tpure $1 }
| LEFTPAR type_v RIGHTPAR
    { $2 }
;

type_c:
| type_v 
  { { pc_result_name = id_result ();
      pc_result_type = $1;
      pc_effect      = empty_effect;
      pc_pre         = lexpr_true ();
      pc_post        = lexpr_true (); } }
| LOGIC type_v effects LOGIC
  { { pc_result_name = id_result ();
      pc_result_type = $2;
      pc_effect      = $3;
      pc_pre         = lexpr $1;
      pc_post        = lexpr $4; } }
;

effects:
| opt_reads opt_writes opt_raises
    { { pe_reads = $1; pe_writes = $2; pe_raises = $3 } }
;

opt_reads:
| /* epsilon */               { [] }
| READS list0_lident_sep_comma { $2 }
;

opt_writes:
| /* epsilon */                { [] }
| WRITES list0_lident_sep_comma { $2 }
;

opt_raises:
| /* epsilon */                { [] }
| RAISES list0_uident_sep_comma { $2 }
;

opt_variant:
| /* epsilon */ { None }
| VARIANT LOGIC  { Some (lexpr $2) }
;

list0_lident_sep_comma:
| /* epsilon */          { [] }
| list1_lident_sep_comma { $1 }
;

list1_lident_sep_comma:
| lident                              { [$1] }
| lident COMMA list1_lident_sep_comma { $1 :: $3 }
;

list0_uident_sep_comma:
| /* epsilon */          { [] }
| list1_uident_sep_comma { $1 }
;

list1_uident_sep_comma:
| uident                              { [$1] }
| uident COMMA list1_uident_sep_comma { $1 :: $3 }
;

/*
Local Variables: 
compile-command: "unset LANG; make -C ../.. testl"
End: 
*/


