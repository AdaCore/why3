/**************************************************************************/
/*                                                                        */
/*  Copyright (C) 2010-                                                   */
/*    François Bobot                                                     */
/*    Jean-Christophe Filliâtre                                          */
/*    Claude Marché                                                      */
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

  let add_lab id l = { id with id_lab = l }

  let user_loc fname lnum bol cnum1 cnum2 =
    let pos = {
      Lexing.pos_fname = fname;
      Lexing.pos_lnum = lnum;
      Lexing.pos_bol = bol;
      Lexing.pos_cnum = cnum1 }
    in
    pos, { pos with Lexing.pos_cnum = cnum2 }

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
    let id = { id = infix op; id_lab = []; id_loc = loc_i 2 } in
    mk_expr (mk_apply_id id [e1; e2])

  let mk_binop e1 op e2 =
    let id = { id = op; id_lab = []; id_loc = loc_i 2 } in
    mk_expr (mk_apply_id id [e1; e2])

  let mk_prefix op e1 =
    let id = { id = prefix op; id_lab = []; id_loc = loc_i 1 } in
    mk_expr (mk_apply_id id [e1])

  let id_unit () = { id = "unit"; id_lab = []; id_loc = loc () }
  let id_result () = { id = "result"; id_lab = []; id_loc = loc () }
  let id_anonymous () = { id = "_"; id_lab = []; id_loc = loc () }
  let exit_exn () = { id = "%Exit"; id_lab = []; id_loc = loc () }

  let id_lt_nat () = Qident { id = "lt_nat"; id_lab = []; id_loc = loc () }

  let ty_unit () = Tpure (PPTtyapp ([], Qident (id_unit ())))

  let lexpr_true () = loc (), "true"
  let lexpr_false () = loc (), "false"

  let empty_effect = { pe_reads = []; pe_writes = []; pe_raises = [] }

  let type_c p ty ef q =
    { pc_result_type = ty;
      pc_effect      = ef;
      pc_pre         = p;
      pc_post        = q; }

  let cast_body c ((p,e,q) as t) = match c with
    | None -> t
    | Some pt -> p, { e with expr_desc = Ecast (e, pt) }, q

%}

/* Tokens */

%token <string> LIDENT UIDENT
%token <string> INTEGER
%token <string> OP1 OP2 OP3 OP4 OPPREF
%token <Why.Ptree.real_constant> REAL
%token <string> STRING
%token <Why.Loc.position * string> LOGIC

/* keywords */

%token ABSURD AND ANY AS ASSERT ASSUME BEGIN CHECK DO DONE DOWNTO ELSE END
%token EXCEPTION FOR
%token FUN GHOST IF IN INVARIANT LABEL LET MATCH NOT OF PARAMETER
%token RAISE RAISES READS REC
%token THEN TO TRY TYPE VARIANT WHILE WITH WRITES

/* symbols */

%token UNDERSCORE QUOTE COMMA LEFTPAR RIGHTPAR COLON SEMICOLON
%token COLONEQUAL ARROW EQUAL LTGT AT DOT LEFTSQ RIGHTSQ
%token LEFTBLEFTB RIGHTBRIGHTB BAR BARBAR AMPAMP
%token BACKQUOTE LEFTPAR_STAR_RIGHTPAR EOF

/* Precedences */

%nonassoc prec_post
%nonassoc BAR

%nonassoc prec_id_pattern
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
%left EQUAL LTGT OP1
%left OP2
%left OP3
%left OP4
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
    { Dlogic $1 }
| LET lident labels list1_type_v_binder opt_cast EQUAL triple
    { Dlet (add_lab $2 $3, mk_expr_i 7 (Efun ($4, cast_body $5 $7))) }
| LET lident labels EQUAL FUN list1_type_v_binder ARROW triple
    { Dlet (add_lab $2 $3, mk_expr_i 8 (Efun ($6, $8))) }
| LET REC list1_recfun_sep_and
    { Dletrec $3 }
| PARAMETER lident labels COLON type_v
    { Dparam (add_lab $2 $3, $5) }
| EXCEPTION uident labels
    { Dexn (add_lab $2 $3, None) }
| EXCEPTION uident labels OF pure_type
    { Dexn (add_lab $2 $3, Some $5) }
;

list1_recfun_sep_and:
| recfun                          { [ $1 ] }
| recfun AND list1_recfun_sep_and { $1 :: $3 }
;

recfun:
| lident labels list1_type_v_binder opt_cast opt_variant EQUAL triple
   { add_lab $1 $2, $3, $5, cast_body $4 $7 }
;

lident:
| LIDENT { { id = $1; id_lab = []; id_loc = loc () } }
;

uident:
| UIDENT { { id = $1; id_lab = []; id_loc = loc () } }
;

ident:
| uident { $1 }
| lident { $1 }
;

any_op:
| OP1   { $1 }
| OP2   { $1 }
| OP3   { $1 }
| OP4   { $1 }
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
   { mk_infix $1 "=" $3 }
| expr LTGT expr
   { let t = mk_infix $1 "=" $3 in
     mk_expr (mk_apply_id { id = "notb"; id_lab = []; id_loc = loc () } [t]) }
| expr OP1 expr
   { mk_infix $1 $2 $3 }
| expr OP2 expr
   { mk_infix $1 $2 $3 }
| expr OP3 expr
   { mk_infix $1 $2 $3 }
| expr OP4 expr
   { mk_infix $1 $2 $3 }
| NOT expr %prec prefix_op
   { mk_expr (mk_apply_id { id = "notb"; id_lab = []; id_loc = loc () } [$2]) }
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
| MATCH expr WITH option_bar match_cases END
   { mk_expr (Ematch ($2, $5)) }
| MATCH expr COMMA list1_expr_sep_comma WITH option_bar match_cases END
   { mk_expr (Ematch (mk_expr (Etuple ($2::$4)), $7)) }
| LABEL uident COLON expr
   { mk_expr (Elabel ($2, $4)) }
| WHILE expr DO loop_annotation expr DONE
   { mk_expr
       (Etry
	  (mk_expr
	     (Eloop ($4,
		     mk_expr (Eif ($2, $5,
				   mk_expr (Eraise (exit_exn (), None)))))),
	   [exit_exn (), None, mk_expr Eskip])) }
| FOR lident EQUAL expr for_direction expr DO loop_invariant expr DONE
   { mk_expr (Efor ($2, $4, $5, $6, $8, $9)) }
| ABSURD
   { mk_expr Eabsurd }
| expr COLON pure_type
   { mk_expr (Ecast ($1, $3)) }
| RAISE uident
   { mk_expr (Eraise ($2, None)) }
| RAISE LEFTPAR uident expr RIGHTPAR
   { mk_expr (Eraise ($3, Some $4)) }
| TRY expr WITH option_bar list1_handler_sep_bar END
   { mk_expr (Etry ($2, $5)) }
| ANY simple_type_c
   { mk_expr (Eany $2) }
| LEFTPAR expr COMMA list1_expr_sep_comma RIGHTPAR
   { mk_expr (Etuple ($2 :: $4)) }
;

triple:
| pre expr post
  { $1, $2, $3 }
| expr %prec prec_triple
  { lexpr_true (), $1, (lexpr_true (), []) }
;

simple_expr:
| constant
    { mk_expr (Econstant $1) }
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
| OPPREF simple_expr
    { mk_prefix $1 $2 }
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

list1_handler_sep_bar:
| handler                           { [$1] }
| handler BAR list1_handler_sep_bar { $1 :: $3 }
;

handler:
| ident ARROW expr            { ($1, None, $3) }
| ident ident ARROW expr      { ($1, Some $2, $4) }
| ident UNDERSCORE ARROW expr { ($1, Some (id_anonymous ()), $4) }
;

match_cases:
| match_case                  { [$1] }
| match_case BAR match_cases  { $1::$3 }
;

match_case:
| pattern ARROW expr   { ($1,$3) }
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
| INVARIANT LOGIC { Some $2 }
| /* epsilon */   { None    }
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
| pure_type_arg_no_paren { $1 }
| lqualid pure_type_args { PPTtyapp ($2, $1) }
;

pure_type_args:
| pure_type_arg                { [$1] }
| pure_type_arg pure_type_args { $1 :: $2 }
;

pure_type_arg:
| LEFTPAR pure_type RIGHTPAR { $2 }
| pure_type_arg_no_paren     { $1 }
;

pure_type_arg_no_paren:
| type_var
   { PPTtyvar $1 }
| lqualid
   { PPTtyapp ([], $1) }
| LEFTPAR pure_type COMMA list1_pure_type_sep_comma RIGHTPAR
   { PPTtuple ($2 :: $4) }
| LEFTPAR RIGHTPAR
   { PPTtuple ([]) }
;

list1_pure_type_sep_comma:
| pure_type                                 { [$1] }
| pure_type COMMA list1_pure_type_sep_comma { $1 :: $3 }
;

list1_type_v_binder:
| type_v_binder                     { $1 }
| type_v_binder list1_type_v_binder { $1 @ $2 }
;

type_v_binder:
| lident labels
   { [add_lab $1 $2, None] }
| LEFTPAR RIGHTPAR
   { [id_anonymous (), Some (ty_unit ())] }
| LEFTPAR lidents_lab COLON type_v RIGHTPAR
   { List.map (fun i -> (i, Some $4)) $2 }
;

lidents_lab:
| lident labels             { add_lab $1 $2 :: [] }
| lident labels lidents_lab { add_lab $1 $2 :: $3 }
;

type_v:
| simple_type_v
   { $1 }
| simple_type_v ARROW type_c
   { Tarrow ([id_anonymous (), Some $1], $3) }
| lident labels COLON simple_type_v ARROW type_c
   { Tarrow ([add_lab $1 $2, Some $4], $6) }
   /* TODO: we could alllow lidents instead, e.g. x y : int -> ... */
   /*{ Tarrow (List.map (fun x -> x, Some $3) $1, $5) }*/
;

simple_type_v:
| pure_type
    { Tpure $1 }
| LEFTPAR type_v RIGHTPAR
    { $2 }
;

type_c:
| type_v
    { type_c (lexpr_true ()) $1 empty_effect (lexpr_true (), []) }
| pre type_v effects post
    { type_c $1 $2 $3 $4 }
;

/* for ANY */
simple_type_c:
| pure_type
    { type_c (lexpr_true ()) (Tpure $1) empty_effect (lexpr_true (), []) }
| LEFTPAR type_v RIGHTPAR
    { type_c (lexpr_true ()) $2 empty_effect (lexpr_true (), []) }
| pre type_v effects post
    { type_c $1 $2 $3 $4 }
;

pre:
| LOGIC { $1 }
;

post:
| LOGIC list0_post_exn { $1, $2 }
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
| BAR uident ARROW LOGIC { $2, $4 }
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
| /* epsilon */              { None }
| VARIANT LOGIC              { Some ($2, id_lt_nat ()) }
| VARIANT LOGIC WITH lqualid { Some ($2, $4) }
;

opt_cast:
| /* epsilon */   { None }
| COLON pure_type { Some $2 }
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

/*
Local Variables:
compile-command: "unset LANG; make -C ../.. testl"
End:
*/


