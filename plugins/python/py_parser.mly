(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

%{
  open Why3
  open Ptree
  open Py_ast

  let () = Exn_printer.register (fun fmt exn -> match exn with
    | Error -> Format.pp_print_string fmt "syntax error"
    | _ -> raise exn)

  let floc s e = Loc.extract (s,e)
  let mk_id id s e = { id_str = id; id_ats = []; id_loc = floc s e }
  let mk_pat  d s e = { pat_desc  = d; pat_loc  = floc s e }
  let mk_term d s e = { term_desc = d; term_loc = floc s e }
  let mk_expr loc d = { expr_desc = d; expr_loc = loc }
  let mk_stmt loc d = Dstmt { stmt_desc = d; stmt_loc = loc }
  let mk_var id = mk_expr id.id_loc (Eident id)

  let variant_union v1 v2 = match v1, v2 with
    | _, [] -> v1
    | [], _ -> v2
    | _, ({term_loc = loc},_)::_ -> Loc.errorm ~loc
        "multiple `variant' clauses are not allowed"

  let get_op s e = Qident (mk_id (Ident.op_get "") s e)
  let upd_op s e = Qident (mk_id (Ident.op_update "") s e)

  let empty_spec = {
    sp_pre     = [];    sp_post    = [];  sp_xpost  = [];
    sp_reads   = [];    sp_writes  = [];  sp_alias  = [];
    sp_variant = [];
    sp_checkrw = false; sp_diverge = false; sp_partial = false;
  }

  let spec_union s1 s2 = {
    sp_pre     = s1.sp_pre @ s2.sp_pre;
    sp_post    = s1.sp_post @ s2.sp_post;
    sp_xpost   = s1.sp_xpost @ s2.sp_xpost;
    sp_reads   = s1.sp_reads @ s2.sp_reads;
    sp_writes  = s1.sp_writes @ s2.sp_writes;
    sp_alias   = s1.sp_alias @ s2.sp_alias;
    sp_variant = variant_union s1.sp_variant s2.sp_variant;
    sp_checkrw = s1.sp_checkrw || s2.sp_checkrw;
    sp_diverge = s1.sp_diverge || s2.sp_diverge;
    sp_partial = s1.sp_partial || s2.sp_partial;
  }

  let fresh_type_var =
    let r = ref 0 in
    fun loc -> incr r;
      PTtyvar { id_str = "a" ^ string_of_int !r; id_loc = loc; id_ats = [] }

  let logic_type loc = function
  | None    -> fresh_type_var loc
  | Some ty -> ty

  let logic_param loc (id, ty) = id, logic_type loc ty

%}

%token <string> INTEGER
%token <string> STRING
%token <Py_ast.binop> CMP
%token <string> IDENT QIDENT TVAR
%token DEF IF ELSE ELIF RETURN WHILE FOR IN AND OR NOT NONE TRUE FALSE PASS
%token FROM IMPORT BREAK CONTINUE
%token EOF
%token LEFTPAR RIGHTPAR LEFTSQ RIGHTSQ COMMA EQUAL COLON BEGIN END NEWLINE
       PLUSEQUAL MINUSEQUAL TIMESEQUAL DIVEQUAL MODEQUAL
       LEFTBR RIGHTBR
%token PLUS MINUS TIMES DIV MOD
(* annotations *)
%token INVARIANT VARIANT ASSUME ASSERT CHECK REQUIRES ENSURES LABEL
%token FUNCTION PREDICATE AXIOM LEMMA CONSTANT CALL
%token ARROW LARROW LRARROW FORALL EXISTS DOT THEN LET OLD AT BY SO

(* precedences *)

%nonassoc IN
%nonassoc DOT ELSE
%right ARROW LRARROW BY SO
%nonassoc IF
%right OR
%right AND
%nonassoc NOT
%right CMP
%left PLUS MINUS
%left TIMES DIV MOD
%nonassoc unary_minus prec_prefix_op
%nonassoc LEFTSQ

%start file
(* Transformations entries *)
%start <Why3.Ptree.term> term_eof
%start <Why3.Ptree.term list> term_comma_list_eof
%start <Why3.Ptree.ident list> ident_comma_list_eof

%type <Py_ast.file> file
%type <Py_ast.decl> stmt

%%

file:
| NEWLINE* EOF
    { [] }
| NEWLINE? dl=nonempty_list(decl) NEWLINE? EOF
    { dl }
;

decl:
| import { $1 }
| def    { $1 }
| stmt   { $1 }
| func   { $1 }
| prop   { $1 }
| const  { $1 }

import:
| FROM m=ident IMPORT l=separated_list(COMMA, ident) NEWLINE
  { Dimport (m, l) }

const:
| CONSTANT NEWLINE id = ident EQUAL e = expr NEWLINE
  { Dconst (id,e) }

prop:
| LEMMA id=ident COLON t=term NEWLINE
  { Dprop (Decl.Plemma, id, t) }
| AXIOM id=ident COLON t=term NEWLINE
  { Dprop (Decl.Paxiom, id, t) }

func:
| FUNCTION id=ident LEFTPAR l=separated_list(COMMA, param) RIGHTPAR
  ty=option(function_type) var = option(fp_variant) def=option(logic_body)
  NEWLINE
  { let loc = floc $startpos $endpos in
    Dlogic (id, List.map (logic_param loc) l, Some (logic_type loc ty),
            var, def) }
| PREDICATE id=ident LEFTPAR l=separated_list(COMMA, param) RIGHTPAR
  var=option(fp_variant) def=option(logic_body) NEWLINE
  { let loc = floc $startpos $endpos in
    Dlogic (id, List.map (logic_param loc) l, None, var, def) }

fp_variant:
| LEFTBR VARIANT v=term RIGHTBR { v }

logic_body:
| EQUAL t=term
  { t }

param:
| id=ident ty=option(param_type)
  { id, ty }

param_type:
| COLON ty=typ
  { ty }

function_type:
| ARROW ty=typ
  { ty }

/* Note: "list" is a legal type annotation in Python; we make it a
 * polymorphic type "list 'a" in WhyML  */
typ:
| id=type_var
  { PTtyvar id }
| id=ident
  { if id.id_str = "list"
    then PTtyapp (Qident id, [fresh_type_var (floc $startpos $endpos)])
    else PTtyapp (Qident id, []) }
| id=ident LEFTSQ tyl=separated_nonempty_list(COMMA, typ) RIGHTSQ
    {
      if id.id_str = "Tuple" then PTtuple tyl else PTtyapp (Qident id, tyl)
    }

def:
| fct = as_funct
  DEF f = ident LEFTPAR x = separated_list(COMMA, param) RIGHTPAR
  ty=option(function_type) COLON NEWLINE BEGIN s=spec l=body END
    {
      if f.id_str = "range" then
        let loc = floc $startpos $endpos in
        Loc.errorm ~loc "micro Python does not allow shadowing 'range'"
      else if fct && ty = None then
        let loc = floc $startpos $endpos in
        Loc.errorm ~loc "a logical function should not return a unit type"
      else Ddef (f, x, ty, s, l ty s, fct)
    }
;

as_funct:
| FUNCTION NEWLINE { true  }
| (* epsilon *)    { false }
;

body:
| nonempty_list(stmt)
  { fun _ _ -> $1 }
| PASS NEWLINE
  { fun ty s -> [mk_stmt (floc $startpos $endpos) (Spass (ty, s))] }

spec:
| (* epsilon *)     { empty_spec }
| single_spec spec  { spec_union $1 $2 }

single_spec:
| REQUIRES t=term NEWLINE
    { { empty_spec with sp_pre = [t] } }
| ENSURES e=ensures NEWLINE
    { { empty_spec with sp_post = [floc $startpos(e) $endpos(e), e] } }
| variant
    { { empty_spec with sp_variant = $1 } }

ensures:
| term
    { let id = mk_id "result" $startpos $endpos in
      [mk_pat (Pvar id) $startpos $endpos, $1] }
;

expr_dot:
| d = expr_dot_
   { mk_expr (floc $startpos $endpos) d }
;

expr_dot_:
| id = ident
    { Eident id }
| LEFTPAR e = expr RIGHTPAR
    { e.expr_desc }
;

expr:
| d = expr_desc
   { mk_expr (floc $startpos $endpos) d }
;

/*
expr_desc:
  e = expr_nt { e.expr_desc }
| e1 = expr_nt COMMA el = separated_list(COMMA, expr_nt)
    { Etuple (e1::el) }
;
*/
expr_desc:
  e = expr_nt_desc { e }
| e = expr_nt COMMA el = separated_list(COMMA, expr_nt) { Etuple (e::el) }
;

expr_nt:
| d = expr_nt_desc
   { mk_expr (floc $startpos $endpos) d }
;

expr_nt_desc:
| NONE
    { Enone }
| TRUE
    { Ebool true }
| FALSE
    { Ebool false }
| c = INTEGER
    { Eint c }
| s = STRING
    { Estring s }
| e1 = expr_nt LEFTSQ e2 = expr_nt RIGHTSQ
    { Eget (e1, e2) }
| e1 = expr_nt LEFTSQ e2=option(expr_nt) COLON e3=option(expr_nt) RIGHTSQ
    {
      let f = mk_id "slice" $startpos $endpos in
      let none = mk_expr (floc $startpos $endpos) Enone in
      let e2, e3 = match e2, e3 with
        | None, None -> none, none
        | Some e, None -> e, none
        | None, Some e -> none, e
        | Some e, Some e' -> e, e'
      in
      Ecall(f,[e1;e2;e3])
    }
| MINUS e1 = expr_nt %prec unary_minus
    { Eunop (Uneg, e1) }
| NOT e1 = expr_nt
    { Eunop (Unot, e1) }
| e1 = expr_nt o = binop e2 = expr_nt
    { Ebinop (o, e1, e2) }
| e1 = expr_nt TIMES e2 = expr_nt
    { match e1.expr_desc with
      | Elist [e1] -> Emake (e1, e2)
      | _ -> Ebinop (Bmul, e1, e2) }
| e=expr_dot DOT f=ident LEFTPAR el=separated_list(COMMA, expr_nt) RIGHTPAR
    {
      match f.id_str with
      | "pop" | "append" | "reverse" | "clear" | "copy" | "sort" ->
        Edot (e, f, el)
      | m -> let loc = floc $startpos $endpos in
             Loc.errorm ~loc "The method '%s' is not implemented" m
    }
| f = ident LEFTPAR e = separated_list(COMMA, expr_nt) RIGHTPAR
    { Ecall (f, e) }
| LEFTSQ l = separated_list(COMMA, expr_nt) RIGHTSQ
    { Elist l }
| e1=expr_nt IF c=expr_nt ELSE e2=expr_nt
    { Econd(c,e1,e2) }
| e=expr_dot_
    { e }
;

%inline binop:
| PLUS  { Badd }
| MINUS { Bsub }
| DIV   { Bdiv }
| MOD   { Bmod }
| c=CMP { c    }
| AND   { Band }
| OR    { Bor  }
;

located(X):
| X { mk_stmt (floc $startpos $endpos) $1 }
;

suite:
| s = simple_stmt NEWLINE
    { [s] }
| NEWLINE BEGIN l = nonempty_list(stmt) END
    { l }
;

stmt:
| located(stmt_desc)      { $1 }
| s = simple_stmt NEWLINE { s }

stmt_desc:
| IF c = expr_nt COLON s1 = suite s2=else_branch
    { Sif (c, s1, s2) }
| WHILE e = expr_nt COLON b=loop_body
    { let i, v, l = b in Swhile (e, i, v, l) }
| FOR x = ident IN e = expr COLON b=loop_body
    { let i, _, l = b in Sfor (x, e, i, l) }
;

else_branch:
| /* epsilon */
    { [] }
| ELSE COLON s2=suite
    { s2 }
| ELIF c=expr_nt COLON s1=suite s2=else_branch
    { [mk_stmt (floc $startpos $endpos) (Sif (c, s1, s2))] }


loop_body:
| s = simple_stmt NEWLINE
  { [], [], [s] }
| NEWLINE BEGIN a=loop_annotation l=nonempty_list(stmt) END
  { fst a, snd a, l }

loop_annotation:
| (* epsilon *)
    { [], [] }
| invariant loop_annotation
    { let (i, v) = $2 in ($1::i, v) }
| variant loop_annotation
    { let (i, v) = $2 in (i, variant_union $1 v) }

invariant:
| INVARIANT i=term NEWLINE { i }

variant:
| VARIANT l=comma_list1(term) NEWLINE { List.map (fun t -> t, None) l }

simple_stmt: located(simple_stmt_desc) { $1 };

simple_stmt_desc:
| RETURN e = expr
    { Sreturn e }
| lhs = expr EQUAL rhs = expr { Sassign (lhs, rhs) }
| id=ident o=binop_equal e=expr_nt
    { let loc = floc $startpos $endpos in
      Sassign (mk_var id,
               mk_expr loc (Ebinop (o, mk_expr loc (Eident id), e))) }
| e0 = expr_nt LEFTSQ e1 = expr_nt RIGHTSQ o=binop_equal e2 = expr
    {
      let loc = floc $startpos $endpos in
      let mk_expr_floc = mk_expr loc in
      let id = mk_id "'i" $startpos $endpos in
      let expr_id = mk_expr_floc (Eident id) in
      let a = mk_id "'a" $startpos $endpos in
      let expr_a = mk_expr_floc (Eident a) in
      let operation =
        mk_expr_floc (Ebinop (o, mk_expr_floc (Eget(expr_a, expr_id)), e2)) in
      let s1 =
        Dstmt ({ stmt_desc = Sassign (mk_var a, e0); stmt_loc = loc }) in
      let s2 =
        Dstmt ({ stmt_desc = Sassign (mk_var id, e1); stmt_loc = loc }) in
      let s3 =
        Dstmt ({ stmt_desc = Sset (expr_a, expr_id, operation);
                 stmt_loc = loc }) in
      Sblock [s1; s2; s3]
    }
| k=assertion_kind t = term
    { Sassert (k, t) }
| e = expr
    { Seval e }
| CALL f = ident LEFTPAR e = separated_list(COMMA, term) RIGHTPAR
    { Scall_lemma (f, e) }
| BREAK
    { Sbreak }
| CONTINUE
    { Scontinue }
| LABEL id=ident
    { Slabel id }
;

%inline binop_equal:
| PLUSEQUAL  { Badd }
| MINUSEQUAL { Bsub }
| DIVEQUAL   { Bdiv }
| TIMESEQUAL { Bmul }
| MODEQUAL   { Bmod }
;

assertion_kind:
| ASSERT  { Expr.Assert }
| ASSUME  { Expr.Assume }
| CHECK   { Expr.Check }

ident:
| id = IDENT { mk_id id $startpos $endpos }
;
quote_ident:
| id = QIDENT { mk_id id $startpos $endpos }
;
type_var:
| id = TVAR { mk_id id $startpos $endpos }
;

/* logic */

mk_term(X): d = X { mk_term d $startpos $endpos }

term_tuple: t = mk_term(term_tuple_) { t }

term_tuple_:
| t = term ; COMMA; lt=separated_list(COMMA, term)
    { Ttuple (t::lt) }
| t = term_ { t }

term: t = mk_term(term_) { t }

term_:
| term_arg_
    { match $1 with (* break the infix relation chain *)
      | Tinfix (l,o,r) -> Tinnfix (l,o,r)
      | Tbinop (l,o,r) -> Tbinnop (l,o,r)
      | d -> d }
| NOT term
    { Tnot $2 }
| OLD LEFTPAR t=term RIGHTPAR
    { Tat (t, mk_id Dexpr.old_label $startpos($1) $endpos($1)) }
| AT LEFTPAR t=term COMMA l=ident RIGHTPAR
    { Tat (t, l) }
| o = prefix_op ; t = term %prec prec_prefix_op
    { Tidapp (Qident o, [t]) }
| l = term ; o = bin_op ; r = term
    { Tbinop (l, o, r) }
| l = term ; o = infix_op_1 ; r = term
    { Tinfix (l, o, r) }
| l = term ; o = infix_op_234 ; r = term
    { Tidapp (Qident o, [l; r]) }
| IF term THEN term ELSE term
    { Tif ($2, $4, $6) }
| LET id=ident EQUAL t1=term IN t2=term
    { Tlet (id, t1, t2) }
| q=quant l=comma_list1(param) DOT t=term
    { let var (id, ty) = id.id_loc, Some id, false, ty in
      Tquant (q, List.map var l, [], t) }
| id=ident LEFTPAR l=separated_list(COMMA, term) RIGHTPAR
    { Tidapp (Qident id, l) }

quant:
| FORALL  { Dterm.DTforall }
| EXISTS  { Dterm.DTexists }

term_arg: mk_term(term_arg_) { $1 }

term_arg_:
| quote_ident { Tident (Qident $1) }
| ident       { Tident (Qident $1) }
| INTEGER     { Tconst (Constant.ConstInt Number.(int_literal ILitDec ~neg:false $1)) }
| NONE        { Ttuple [] }
| TRUE        { Ttrue }
| FALSE       { Tfalse }
| term_sub_                 { $1 }

term_sub_:
| LEFTPAR term_tuple RIGHTPAR                             { $2.term_desc }
| term_arg LEFTSQ term RIGHTSQ
    { Tidapp (get_op $startpos($2) $endpos($2), [$1;$3]) }
| term_arg LEFTSQ term LARROW term RIGHTSQ
    { Tidapp (upd_op $startpos($2) $endpos($2), [$1;$3;$5]) }
| e1 = term_arg LEFTSQ e2=option(term) COLON e3=option(term) RIGHTSQ
    {
      let slice = mk_id "slice" $startpos $endpos in
      let len = mk_id "len" $startpos $endpos in
      let z = Tconst (Constant.int_const_of_int 0) in
      let l = Tidapp(Qident len, [e1]) in
      let z = mk_term z $startpos $endpos in
      let l = mk_term l $startpos $endpos in
      let e2, e3 = match e2, e3 with
        | None, None -> z, l
        | Some e, None -> e, l
        | None, Some e -> z, e
        | Some e, Some e' -> e, e'
      in
      Tidapp(Qident slice,[e1;e2;e3])
    }

%inline bin_op:
| ARROW   { Dterm.DTimplies }
| LRARROW { Dterm.DTiff }
| OR      { Dterm.DTor }
| AND     { Dterm.DTand }
| BY      { Dterm.DTby }
| SO      { Dterm.DTso }

%inline infix_op_1:
| c=CMP  { let op = match c with
          | Beq  -> "="
          | Bneq -> "<>"
          | Blt  -> "<"
          | Ble  -> "<="
          | Bgt  -> ">"
          | Bge  -> ">="
          | Badd|Bsub|Bmul|Bdiv|Bmod|Band|Bor -> assert false in
           mk_id (Ident.op_infix op) $startpos $endpos }

%inline prefix_op:
| MINUS { mk_id (Ident.op_prefix "-")  $startpos $endpos }

%inline infix_op_234:
| DIV    { mk_id (Ident.op_infix "//") $startpos $endpos }
| MOD    { mk_id (Ident.op_infix "%") $startpos $endpos }
| PLUS   { mk_id (Ident.op_infix "+") $startpos $endpos }
| MINUS  { mk_id (Ident.op_infix "-") $startpos $endpos }
| TIMES  { mk_id (Ident.op_infix "*") $startpos $endpos }

comma_list1(X):
| separated_nonempty_list(COMMA, X) { $1 }

(* Parsing of a list of qualified identifiers for the ITP *)

(* parsing of a single term *)

term_eof:
| term NEWLINE EOF { $1 }

ident_comma_list_eof:
| comma_list1(ident) NEWLINE EOF { $1 }

term_comma_list_eof:
| comma_list1(term) NEWLINE EOF { $1 }
(* we use single_term to avoid conflict with tuples, that
   do not need parentheses *)
