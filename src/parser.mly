
%{

  open Ptree
  open Parsing

  let loc () = (symbol_start_pos (), symbol_end_pos ())
  let loc_i i = (rhs_start_pos i, rhs_end_pos i)
  let loc_ij i j = (rhs_start_pos i, rhs_end_pos j)

  let mk_ppl loc d = { pp_loc = loc; pp_desc = d }
  let mk_pp d = mk_ppl (loc ()) d
  let mk_pp_i i d = mk_ppl (loc_i i) d
		    
  let infix_ppl loc a i b = mk_ppl loc (PPinfix (a, i, b))
  let infix_pp a i b = infix_ppl (loc ()) a i b

  let prefix_ppl loc p a = mk_ppl loc (PPprefix (p, a))
  let prefix_pp p a = prefix_ppl (loc ()) p a

(***
  let with_loc loc d = { pdesc = d; ploc = loc }
  let locate d = with_loc (loc ()) d
  let locate_i i d = with_loc (loc_i i) d

  let rec_name = function Srec (x,_,_,_,_,_) -> x | _ -> assert false

  let join (b,_) (_,e) = (b,e)

  let rec app f = function
    | [] -> 
	assert false
    | [a] -> 
	Sapp (f, a)
    | a :: l -> 
	let loc = join f.ploc a.ploc in 
	app (with_loc loc (Sapp (f, a))) l

  let bin_op (loc_op,op) e1 e2 =
    let f = with_loc loc_op (Svar op) in
    let f_e1 = with_loc (join e1.ploc loc_op) (Sapp (f, e1)) in
    locate (Sapp (f_e1, e2))
      
  let un_op (loc_op,op) e =
    locate (app (with_loc loc_op (Svar op)) [e])

  let ptype_c_of_v v =
    { pc_result_name = Ident.result;
      pc_result_type = v;
      pc_effect = { pe_reads = []; pe_writes = []; pe_raises = [] };
      pc_pre = []; 
      pc_post = None }

  let list_of_some = function None -> [] | Some x -> [x]

  (*s ensures a postcondition for a function body *)

  let force_function_post ?(warn=false) e = match e.pdesc with
    | Spost _ -> 
	e
    | _ -> 
       if warn then 
	 Format.eprintf 
	   "%ano postcondition for this function; true inserted@\n"
	   Loc.report_position e.ploc; 
       let q = 
	 { pa_name = Anonymous; pa_value = mk_pp PPtrue; pa_loc = loc () }
       in
       { e with pdesc = Spost (e, (q, []), Transparent) }
***)
%}

/* Tokens */ 

%token <string> IDENT
%token <string> INTEGER
%token <Ptree.real_constant> FLOAT
%token <string> STRING
%token ABSURD AMPAMP AND ARRAY ARROW AS ASSERT AT AXIOM 
%token BANG BAR BARBAR BEGIN 
%token BIGARROW BOOL CHECK COLON COLONEQUAL COMMA DO DONE DOT ELSE END EOF EQUAL
%token EXCEPTION EXISTS EXTERNAL FALSE FOR FORALL FPI FUN FUNCTION GE GOAL GT
%token IF IN INCLUDE INDUCTIVE INT INVARIANT
%token LE LEFTB LEFTBLEFTB LEFTPAR LEFTSQ LET LOGIC LRARROW LT MATCH MINUS
%token NOT NOTEQ OF OR PARAMETER PERCENT PLUS PREDICATE PROP 
%token QUOTE RAISE RAISES READS REAL REC REF RETURNS RIGHTB RIGHTBRIGHTB
%token RIGHTPAR RIGHTSQ 
%token SEMICOLON SLASH 
%token THEN TIMES TRUE TRY TYPE UNIT VARIANT VOID WHILE WITH WRITES

/* Precedences */

%nonassoc prec_recfun
%nonassoc prec_fun
%left LEFTB LEFTBLEFTB
%left prec_simple

%left COLON 

%left prec_letrec
%left IN

%right SEMICOLON

%left prec_no_else
%left ELSE

%right prec_named
%left COLONEQUAL
%right prec_forall prec_exists
%right ARROW LRARROW
%right OR BARBAR
%right AND AMPAMP
%right NOT
%right prec_if
%left prec_relation EQUAL NOTEQ LT LE GT GE
%left PLUS MINUS
%left TIMES SLASH PERCENT
%right uminus
%left prec_app
%left prec_ident
%left LEFTSQ

/* Entry points */

%type <Ptree.lexpr> lexpr
%start lexpr
%type <Ptree.logic_file> logic_file
%start logic_file
%%

logic_file:
| list1_decl EOF 
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

decl:
| external_ LOGIC list1_ident_sep_comma COLON logic_type
   { Logic (loc_i 3, $1, $3, $5) }
| AXIOM ident COLON lexpr
   { Axiom (loc (), $2, $4) }
| PREDICATE ident LEFTPAR list0_logic_binder_sep_comma RIGHTPAR EQUAL lexpr
   { Predicate_def (loc (), $2, $4, $7) }
| INDUCTIVE ident COLON logic_type inddefn
   { Inductive_def (loc (), $2, $4, $5) }
| FUNCTION ident LEFTPAR list0_logic_binder_sep_comma RIGHTPAR COLON 
  primitive_type EQUAL lexpr
   { Function_def (loc (), $2, $4, $7, $9) }
| GOAL ident COLON lexpr
   { Goal (loc (), $2, $4) }
| EXTERNAL TYPE typedecl
   { let loc, vl, id = $3 in TypeDecl (loc, true, vl, id) }
| TYPE typedecl typedefn
   { let loc, vl, id = $2 in $3 loc vl id }
;

typedecl:
| ident
    { (loc_i 1, [], $1) }
| type_var ident
    { (loc_i 2, [$1], $2) }
| LEFTPAR type_var COMMA list1_type_var_sep_comma RIGHTPAR ident
    { (loc_i 6, $2 :: $4, $6) }
;

typedefn:
| /* epsilon */
    { fun loc vl id -> TypeDecl (loc, false, vl, id) }
| EQUAL bar_ typecases typecont
    { fun loc vl id -> AlgType ((loc, vl, id, $3) :: $4) }
;

typecont:
| /* epsilon */
    { [] }
| AND typedecl EQUAL bar_ typecases typecont
    { let loc, vl, id = $2 in (loc, vl, id, $5) :: $6 }
;

typecases:
| typecase                { [$1] }
| typecase BAR typecases  { $1::$3 }
;

typecase:
| ident
    { (loc_i 1,$1,[]) }
| ident LEFTPAR list1_primitive_type_sep_comma RIGHTPAR
    { (loc_i 1,$1,$3) }
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
| ident COLON lexpr { (loc_i 1,$1,$3) }
;

primitive_type:
| INT 
   { PPTint }
| BOOL 
   { PPTbool }
| REAL 
   { PPTreal }
| UNIT 
   { PPTunit }
| type_var 
   { PPTvarid ($1, loc ()) }
| ident 
   { PPTexternal ([], $1, loc ()) }
| primitive_type ident
   { PPTexternal ([$1], $2, loc_i 2) }
| LEFTPAR primitive_type COMMA list1_primitive_type_sep_comma RIGHTPAR ident
   { PPTexternal ($2 :: $4, $6, loc_i 6) }
/*
| LEFTPAR list1_primitive_type_sep_comma RIGHTPAR
   { match $2 with [p] -> p | _ -> raise Parse_error }
*/
;


logic_type:
| list0_primitive_type_sep_comma ARROW PROP
   { PPredicate $1 }
| PROP
   { PPredicate [] }
| list0_primitive_type_sep_comma ARROW primitive_type
   { PFunction ($1, $3) }
| primitive_type
   { PFunction ([], $1) }
;

list0_primitive_type_sep_comma:
| /* epsilon */                  { [] }
| list1_primitive_type_sep_comma { $1 }
;

list1_primitive_type_sep_comma:
| primitive_type                                      { [$1] }
| primitive_type COMMA list1_primitive_type_sep_comma { $1 :: $3 }
;

list0_logic_binder_sep_comma:
| /* epsilon */                { [] }
| list1_logic_binder_sep_comma { $1 }
;

list1_logic_binder_sep_comma:
| logic_binder                                    { [$1] }
| logic_binder COMMA list1_logic_binder_sep_comma { $1 :: $3 }
;

logic_binder:
| ident COLON primitive_type       
    { (loc_i 1, $1, $3) }
/***
| ident COLON primitive_type ARRAY 
    { (loc_i 1, $1, PPTexternal ([$3], Ident.farray, loc_i 3)) }
***/
;

external_:
| /* epsilon */ { false }
| EXTERNAL      { true  }
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
| lexpr relation lexpr %prec prec_relation
   { infix_pp $1 $2 $3 }
| lexpr PLUS lexpr
   { infix_pp $1 PPadd $3 }
| lexpr MINUS lexpr
   { infix_pp $1 PPsub $3 }
| lexpr TIMES lexpr
   { infix_pp $1 PPmul $3 }
| lexpr SLASH lexpr
   { infix_pp $1 PPdiv $3 }
| lexpr PERCENT lexpr
   { infix_pp $1 PPmod $3 }
| MINUS lexpr %prec uminus
   { prefix_pp PPneg $2 }
/***
| qualid_ident
   { mk_pp (PPvar $1) }
| qualid_ident LEFTPAR list1_lexpr_sep_comma RIGHTPAR
   { mk_pp (PPapp ($1, $3)) }
| qualid_ident LEFTSQ lexpr RIGHTSQ
   { mk_pp (PPapp (Ident.access, [mk_pp_i 1 (PPvar $1); $3])) }
***/
| IF lexpr THEN lexpr ELSE lexpr %prec prec_if 
   { mk_pp (PPif ($2, $4, $6)) }
| FORALL list1_ident_sep_comma COLON primitive_type triggers 
  DOT lexpr %prec prec_forall
   { let rec mk = function
       | [] -> assert false
       | [id] -> mk_pp (PPforall (id, $4, $5, $7))
       | id :: l -> mk_pp (PPforall (id, $4, [], mk l))
     in
     mk $2 }
| EXISTS ident COLON primitive_type DOT lexpr %prec prec_exists
   { mk_pp (PPexists ($2, $4, $6)) }
| INTEGER
   { mk_pp (PPconst (ConstInt $1)) }
| FLOAT
   { mk_pp (PPconst (ConstFloat $1)) }
| TRUE
   { mk_pp PPtrue }
| FALSE
   { mk_pp PPfalse }    
/***
| VOID
   { mk_pp (PPconst ConstUnit) }
***/
| LEFTPAR lexpr RIGHTPAR
   { $2 }
| ident_or_string COLON lexpr %prec prec_named
   { mk_pp (PPnamed ($1, $3)) }
| LET ident EQUAL lexpr IN lexpr 
   { mk_pp (PPlet ($2, $4, $6)) }
| MATCH lexpr WITH bar_ match_cases END
   { mk_pp (PPmatch ($2, $5)) }
;

match_cases:
| match_case                  { [$1] }
| match_case BAR match_cases  { $1::$3 }
;

match_case:
| pattern ARROW lexpr { ($1,$3) }
;

pattern:
| ident                                         { ($1, [], loc ()) }
| ident LEFTPAR list1_ident_sep_comma RIGHTPAR  { ($1, $3, loc ()) }
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

relation:
| LT { PPlt }
| LE { PPle }
| GT { PPgt }
| GE { PPge }
| EQUAL { PPeq }
| NOTEQ { PPneq }
;

type_var:
| QUOTE ident { $2 }
;

list1_type_var_sep_comma:
| type_var                                { [$1] }
| type_var COMMA list1_type_var_sep_comma { $1 :: $3 }
;

ident:
| IDENT { $1 }
;

qualid_ident:
| IDENT          { $1, None }
| IDENT AT       { $1, Some "" }
| IDENT AT IDENT { $1, Some $3 }
;

ident_or_string:
| IDENT  { $1 }
| STRING { $1 }
;

bar_:
| /* epsilon */ { () }
| BAR           { () }
;

list1_ident_sep_comma:
| ident                             { [$1] }
| ident COMMA list1_ident_sep_comma { $1 :: $3 }
;

/******* programs **************************************************

list0_ident_sep_comma:
| /* epsilon * /         { [] }
| list1_ident_sep_comma { $1 }
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
| external_ PARAMETER list1_ident_sep_comma COLON type_v
   { Parameter (loc_i 3, $1, $3, $5) }

type_v:
| simple_type_v ARROW type_c
   { PVarrow ([Ident.anonymous, $1], $3) }
| ident COLON simple_type_v ARROW type_c
   { PVarrow ([($1, $3)], $5) }
| simple_type_v
   { $1 }
;

simple_type_v:
| primitive_type ARRAY    { PVref (PPTexternal ([$1], Ident.farray, loc_i 2)) }
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

****/
