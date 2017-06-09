(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

%{
  open Ptree

  let infix  s = "infix "  ^ s
  let prefix s = "prefix " ^ s
  let mixfix s = "mixfix " ^ s

  let qualid_last = function Qident x | Qdot (_, x) -> x

  let use_as q = function Some x -> x | None -> qualid_last q

  let floc s e = Loc.extract (s,e)

  let model_label = Ident.create_label "model"
  let model_projected = Ident.create_label "model_projected"

  let is_model_label l = match l with
    | Lstr lab -> Ident.lab_equal lab model_label ||
                  Ident.lab_equal lab model_projected
    | Lpos _ -> false

  let model_lab_present labels = List.exists is_model_label labels

  let is_model_trace_label l = match l with
    | Lstr lab -> Strings.has_prefix "model_trace:" lab.Ident.lab_string
    | Lpos _ -> false

  let model_trace_lab_present labels = List.exists is_model_trace_label labels

  let add_model_trace name labels =
    if model_lab_present labels && not (model_trace_lab_present labels) then
      (Lstr (Ident.create_label ("model_trace:" ^ name)))::labels
    else
      labels

  let add_lab id l = { id with id_lab = add_model_trace id.id_str l }

  let id_anonymous loc = { id_str = "_"; id_lab = []; id_loc = loc }

  let mk_id id s e = { id_str = id; id_lab = []; id_loc = floc s e }

  let get_op s e = Qident (mk_id (mixfix "[]") s e)
  let set_op s e = Qident (mk_id (mixfix "[<-]") s e)
  let sub_op s e = Qident (mk_id (mixfix "[_.._]") s e)
  let above_op s e = Qident (mk_id (mixfix "[_..]") s e)
  let below_op s e = Qident (mk_id (mixfix "[.._]") s e)

  let mk_pat  d s e = { pat_desc  = d; pat_loc  = floc s e }
  let mk_term d s e = { term_desc = d; term_loc = floc s e }
  let mk_expr d s e = { expr_desc = d; expr_loc = floc s e }

  let variant_union v1 v2 = match v1, v2 with
    | _, [] -> v1
    | [], _ -> v2
    | _, ({term_loc = loc},_)::_ -> Loc.errorm ~loc
        "multiple `variant' clauses are not allowed"

  let empty_spec = {
    sp_pre     = [];
    sp_post    = [];
    sp_xpost   = [];
    sp_reads   = [];
    sp_writes  = [];
    sp_alias   = [];
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
    sp_alias   = s1.sp_alias @ s2.sp_alias;
    sp_variant = variant_union s1.sp_variant s2.sp_variant;
    sp_checkrw = s1.sp_checkrw || s2.sp_checkrw;
    sp_diverge = s1.sp_diverge || s2.sp_diverge;
  }

(* dead code
  let add_init_mark e =
    let init = { id_str = "Init"; id_lab = []; id_loc = e.expr_loc } in
    { e with expr_desc = Emark (init, e) }
*)

  let small_integer i =
    try match i with
      | Number.IConstDec s -> int_of_string s
      | Number.IConstHex s -> int_of_string ("0x"^s)
      | Number.IConstOct s -> int_of_string ("0o"^s)
      | Number.IConstBin s -> int_of_string ("0b"^s)
    with Failure _ -> raise Error

  let error_param loc =
    Loc.errorm ~loc "cannot determine the type of the parameter"

  let error_loc loc = Loc.error ~loc Error

  let () = Exn_printer.register (fun fmt exn -> match exn with
    | Error -> Format.fprintf fmt "syntax error"
    | _ -> raise exn)
%}

(* Tokens *)

%token <string> LIDENT LIDENT_QUOTE UIDENT UIDENT_QUOTE
%token <Number.integer_constant> INTEGER
%token <string> OP1 OP2 OP3 OP4 OPPREF
%token <Number.real_constant> REAL
%token <string> STRING
%token <Loc.position> POSITION
%token <string> QUOTE_LIDENT

(* keywords *)

%token AS AXIOM BY CLONE COINDUCTIVE CONSTANT
%token ELSE END EPSILON EXISTS EXPORT FALSE FLOAT FORALL FUNCTION
%token GOAL IF IMPORT IN INDUCTIVE LEMMA
%token LET MATCH META NOT PREDICATE RANGE SCOPE
%token SO THEN THEORY TRUE TYPE USE WITH

(* program keywords *)

%token ABSTRACT ABSURD ANY ASSERT ASSUME AT BEGIN CHECK
%token DIVERGES DO DONE DOWNTO ENSURES EXCEPTION FOR
%token FUN GHOST INVARIANT LABEL MODULE MUTABLE OLD
%token PRIVATE PURE RAISE RAISES READS REC REQUIRES
%token RETURN RETURNS TO TRY VAL VARIANT WHILE WRITES ALIAS

(* symbols *)

%token AND ARROW
%token BAR
%token COLON COMMA
%token DOT DOTDOT EQUAL LT GT LTGT MINUS
%token LEFTPAR LEFTPAR_STAR_RIGHTPAR LEFTSQ
%token LARROW LRARROW OR
%token RIGHTPAR RIGHTSQ
%token TILDE
%token UNDERSCORE

%token EOF

(* program symbols *)

%token AMPAMP BARBAR LEFTBRC RIGHTBRC SEMICOLON

(* Precedences *)

%nonassoc IN
%nonassoc below_SEMI
%nonassoc SEMICOLON
%nonassoc LET VAL EXCEPTION
%nonassoc prec_no_else
%nonassoc DOT ELSE GHOST
%nonassoc prec_named
%nonassoc COLON (* weaker than -> because of t: a -> b *)
%right ARROW LRARROW BY SO
%right OR BARBAR
%right AND AMPAMP
%nonassoc NOT
%right EQUAL LTGT LT GT OP1
%nonassoc AT OLD
%nonassoc LARROW
%nonassoc RIGHTSQ    (* stronger than <- for e1[e2 <- e3] *)
%left OP2 MINUS
%left OP3
%left OP4
%nonassoc prec_prefix_op
%nonassoc INTEGER REAL (* stronger than MINUS *)
%nonassoc LEFTSQ
%nonassoc OPPREF

(* Entry points *)

%start <Pmodule.pmodule Stdlib.Mstr.t> mlw_file
%%

(* Modules and scopes *)

mlw_file:
| mlw_module* EOF
    { Typing.close_file () }
| module_decl+ EOF
    { let loc = floc $startpos($2) $endpos($2) in
      Typing.close_module loc; Typing.close_file () }

mlw_module:
| module_head module_decl* END
    { Typing.close_module (floc $startpos($3) $endpos($3)) }

module_head:
| THEORY labels(uident_nq)  { Typing.open_module $2 }
| MODULE labels(uident_nq)  { Typing.open_module $2 }

scope_head:
| SCOPE boption(IMPORT) uident
    { Typing.open_scope (floc $startpos $endpos) $3; $2 }

module_decl:
| scope_head module_decl* END
    { Typing.close_scope (floc $startpos($1) $endpos($1)) ~import:$1 }
| IMPORT uqualid
    { Typing.import_scope (floc $startpos $endpos) $2 }
| d = pure_decl | d = prog_decl | d = meta_decl
    { Typing.add_decl (floc $startpos $endpos) d }
| use_clone { () }

(* Use and clone *)

use_clone:
| USE EXPORT tqualid
    { Typing.add_decl (floc $startpos $endpos) (Duse $3) }
| CLONE EXPORT tqualid clone_subst
    { Typing.add_decl (floc $startpos $endpos) (Dclone ($3, $4)) }
| USE boption(IMPORT) tqualid option(preceded(AS, uident))
    { let loc = floc $startpos $endpos in
      Typing.open_scope loc (use_as $3 $4);
      Typing.add_decl loc (Duse $3);
      Typing.close_scope loc ~import:$2 }
| CLONE boption(IMPORT) tqualid option(preceded(AS, uident)) clone_subst
    { let loc = floc $startpos $endpos in
      Typing.open_scope loc (use_as $3 $4);
      Typing.add_decl loc (Dclone ($3, $5));
      Typing.close_scope loc ~import:$2 }

clone_subst:
| (* epsilon *)                         { [] }
| WITH comma_list1(single_clone_subst)  { $2 }

single_clone_subst:
| TYPE qualid ty_var* EQUAL ty  { CStsym  ($2,$3,$5) }
| TYPE qualid                   { CStsym  ($2, [], PTtyapp ($2, [])) }
| CONSTANT  qualid EQUAL qualid { CSfsym  ($2,$4) }
| CONSTANT  qualid              { CSfsym  ($2,$2) }
| FUNCTION  qualid EQUAL qualid { CSfsym  ($2,$4) }
| FUNCTION  qualid              { CSfsym  ($2,$2) }
| PREDICATE qualid EQUAL qualid { CSpsym  ($2,$4) }
| PREDICATE qualid              { CSpsym  ($2,$2) }
| VAL       qualid EQUAL qualid { CSvsym  ($2,$4) }
| VAL       qualid              { CSvsym  ($2,$2) }
| EXCEPTION qualid EQUAL qualid { CSxsym  ($2,$4) }
| EXCEPTION qualid              { CSxsym  ($2,$2) }
| AXIOM     qualid              { CSaxiom ($2) }
| LEMMA     qualid              { CSlemma ($2) }
| GOAL      qualid              { CSgoal  ($2) }

(* Meta declarations *)

meta_decl:
| META sident comma_list1(meta_arg)  { Dmeta ($2, $3) }

meta_arg:
| TYPE      ty      { Mty $2 }
| CONSTANT  qualid  { Mfs $2 }
| FUNCTION  qualid  { Mfs $2 }
| PREDICATE qualid  { Mps $2 }
| AXIOM     qualid  { Max $2 }
| LEMMA     qualid  { Mlm $2 }
| GOAL      qualid  { Mgl $2 }
| STRING            { Mstr $1 }
| INTEGER           { Mint (small_integer $1) }

(* Theory declarations *)

pure_decl:
| TYPE with_list1(type_decl)                { Dtype $2 }
| CONSTANT  constant_decl                   { Dlogic [$2] }
| FUNCTION  function_decl  with_logic_decl* { Dlogic ($2::$3) }
| PREDICATE predicate_decl with_logic_decl* { Dlogic ($2::$3) }
| INDUCTIVE   with_list1(inductive_decl)    { Dind (Decl.Ind, $2) }
| COINDUCTIVE with_list1(inductive_decl)    { Dind (Decl.Coind, $2) }
| AXIOM labels(ident_nq) COLON term         { Dprop (Decl.Paxiom, $2, $4) }
| LEMMA labels(ident_nq) COLON term         { Dprop (Decl.Plemma, $2, $4) }
| GOAL  labels(ident_nq) COLON term         { Dprop (Decl.Pgoal, $2, $4) }

(* Type declarations *)

type_decl:
| labels(lident_nq) ty_var* typedefn invariant*
  { let (vis, mut), def = $3 in
    { td_ident = $1; td_params = $2;
      td_vis = vis; td_mut = mut;
      td_inv = $4; td_def = def;
      td_loc = floc $startpos $endpos } }

ty_var:
| labels(quote_lident) { $1 }

typedefn:
| (* epsilon *)
    { (Abstract, false), TDrecord [] }
| EQUAL vis_mut bar_list1(type_case)
    { $2, TDalgebraic $3 }
| EQUAL vis_mut LEFTBRC loption(semicolon_list1(type_field)) RIGHTBRC
    { $2, TDrecord $4 }
| EQUAL vis_mut ty
    { $2, TDalias $3 }
(* FIXME: allow negative bounds *)
| EQUAL LT RANGE INTEGER INTEGER GT
    { (Public, false),
      TDrange (Number.compute_int $4, Number.compute_int $5) }
| EQUAL LT FLOAT INTEGER INTEGER GT
    { (Public, false),
      TDfloat (small_integer $4, small_integer $5) }

vis_mut:
| (* epsilon *)     { Public, false }
| MUTABLE           { Public, true  }
| abstract          { $1, false }
| abstract MUTABLE  { $1, true }
| MUTABLE abstract  { $2, true }

abstract:
| PRIVATE           { Private }
| ABSTRACT          { Abstract }

type_field:
| labels(lident_nq) cast
  { { f_ident = $1; f_mutable = false; f_ghost = false;
      f_pty = $2; f_loc = floc $startpos $endpos } }
| field_modifiers labels(lident_nq) cast
  { { f_ident = $2; f_mutable = fst $1; f_ghost = snd $1;
      f_pty = $3; f_loc = floc $startpos $endpos } }

field_modifiers:
| MUTABLE       { true,  false }
| GHOST         { false, true  }
| GHOST MUTABLE { true,  true  }
| MUTABLE GHOST { true,  true  }

type_case:
| labels(uident_nq) params { floc $startpos $endpos, $1, $2 }

(* Logic declarations *)

constant_decl:
| labels(lident_rich) cast preceded(EQUAL,term)?
  { { ld_ident = $1; ld_params = []; ld_type = Some $2;
      ld_def = $3; ld_loc = floc $startpos $endpos } }

function_decl:
| labels(lident_rich) params cast preceded(EQUAL,term)?
  { { ld_ident = $1; ld_params = $2; ld_type = Some $3;
      ld_def = $4; ld_loc = floc $startpos $endpos } }

predicate_decl:
| labels(lident_rich) params preceded(EQUAL,term)?
  { { ld_ident = $1; ld_params = $2; ld_type = None;
      ld_def = $3; ld_loc = floc $startpos $endpos } }

with_logic_decl:
| WITH labels(lident_rich) params cast? preceded(EQUAL,term)?
  { { ld_ident = $2; ld_params = $3; ld_type = $4;
      ld_def = $5; ld_loc = floc $startpos $endpos } }

(* Inductive declarations *)

inductive_decl:
| labels(lident_rich) params ind_defn
  { { in_ident = $1; in_params = $2;
      in_def = $3; in_loc = floc $startpos $endpos } }

ind_defn:
| (* epsilon *)             { [] }
| EQUAL bar_list1(ind_case) { $2 }

ind_case:
| labels(ident_nq) COLON term  { floc $startpos $endpos, $1, $3 }

(* Type expressions *)

ty:
| ty_arg          { $1 }
| lqualid ty_arg+ { PTtyapp ($1, $2) }
| ty ARROW ty     { PTarrow ($1, $3) }

ty_arg:
| lqualid                           { PTtyapp ($1, []) }
| quote_lident                      { PTtyvar $1 }
| LEFTPAR comma_list2(ty) RIGHTPAR  { PTtuple $2 }
| LEFTPAR RIGHTPAR                  { PTtuple [] }
| LEFTPAR ty RIGHTPAR               { PTparen $2 }
| LEFTBRC ty RIGHTBRC               { PTpure $2 }

cast:
| COLON ty  { $2 }

(* Parameters and binders *)

(* [param] and [binder] below must have the same grammar
   and raise [Error] in the same cases. Interpretaion of
   single-standing untyped [Qident]'s is different: [param]
   treats them as type expressions, [binder], as parameter
   names, whose type must be inferred. *)

params:  param*  { List.concat $1 }

binders: binder+ { List.concat $1 }

param:
| anon_binder
    { error_param (floc $startpos $endpos) }
| ty_arg
    { [floc $startpos $endpos, None, false, $1] }
| LEFTPAR GHOST ty RIGHTPAR
    { [floc $startpos $endpos, None, true, $3] }
| ty_arg label label*
    { match $1 with
      | PTtyapp (Qident _, []) ->
             error_param (floc $startpos $endpos)
      | _ -> error_loc (floc $startpos($2) $endpos($2)) }
| LEFTPAR binder_vars_rest RIGHTPAR
    { match $2 with [l,_] -> error_param l
      | _ -> error_loc (floc $startpos($3) $endpos($3)) }
| LEFTPAR GHOST binder_vars_rest RIGHTPAR
    { match $3 with [l,_] -> error_param l
      | _ -> error_loc (floc $startpos($4) $endpos($4)) }
| LEFTPAR binder_vars cast RIGHTPAR
    { List.map (fun (l,i) -> l, i, false, $3) $2 }
| LEFTPAR GHOST binder_vars cast RIGHTPAR
    { List.map (fun (l,i) -> l, i, true, $4) $3 }

binder:
| anon_binder
    { let l,i = $1 in [l, i, false, None] }
| ty_arg
    { match $1 with
      | PTtyapp (Qident id, [])
      | PTparen (PTtyapp (Qident id, [])) ->
             [floc $startpos $endpos, Some id, false, None]
      | _ -> [floc $startpos $endpos, None, false, Some $1] }
| LEFTPAR GHOST ty RIGHTPAR
    { match $3 with
      | PTtyapp (Qident id, []) ->
             [floc $startpos $endpos, Some id, true, None]
      | _ -> [floc $startpos $endpos, None, true, Some $3] }
| ty_arg label label*
    { match $1 with
      | PTtyapp (Qident id, []) ->
             let id = add_lab id ($2::$3) in
             [floc $startpos $endpos, Some id, false, None]
      | _ -> error_loc (floc $startpos($2) $endpos($2)) }
| LEFTPAR binder_vars_rest RIGHTPAR
    { match $2 with [l,i] -> [l, i, false, None]
      | _ -> error_loc (floc $startpos($3) $endpos($3)) }
| LEFTPAR GHOST binder_vars_rest RIGHTPAR
    { match $3 with [l,i] -> [l, i, true, None]
      | _ -> error_loc (floc $startpos($4) $endpos($4)) }
| LEFTPAR binder_vars cast RIGHTPAR
    { List.map (fun (l,i) -> l, i, false, Some $3) $2 }
| LEFTPAR GHOST binder_vars cast RIGHTPAR
    { List.map (fun (l,i) -> l, i, true, Some $4) $3 }

binder_vars:
| binder_vars_head  { List.rev $1 }
| binder_vars_rest  { $1 }

binder_vars_rest:
| binder_vars_head label label* binder_var*
    { List.rev_append (match $1 with
        | (l, Some id) :: bl ->
            let l3 = floc $startpos($3) $endpos($3) in
            (Loc.join l l3, Some (add_lab id ($2::$3))) :: bl
        | _ -> assert false) $4 }
| binder_vars_head anon_binder binder_var*
    { List.rev_append $1 ($2 :: $3) }
| anon_binder binder_var*
    { $1 :: $2 }

binder_vars_head:
| ty {
    let of_id id = id.id_loc, Some id in
    let push acc = function
      | PTtyapp (Qident id, []) -> of_id id :: acc
      | _ -> Loc.error ~loc:(floc $startpos $endpos) Error in
    match $1 with
      | PTtyapp (Qident id, l) -> List.fold_left push [of_id id] l
      | _ -> Loc.error ~loc:(floc $startpos $endpos) Error }

binder_var:
| labels(lident_nq) { floc $startpos $endpos, Some $1 }
| anon_binder       { $1 }

anon_binder:
| UNDERSCORE        { floc $startpos $endpos, None }

(* Logical terms *)

mk_term(X): d = X { mk_term d $startpos $endpos }

term: t = mk_term(term_) { t }

term_:
| term_arg_
    { match $1 with (* break the infix relation chain *)
      | Tinfix (l,o,r) -> Tinnfix (l,o,r)
      | Tbinop (l,o,r) -> Tbinnop (l,o,r)
      | d -> d }
| NOT term
    { Tnot $2 }
| OLD term
    { Tat ($2, mk_id Dexpr.old_mark $startpos($1) $endpos($1)) }
| term AT uident
    { Tat ($1, $3) }
| prefix_op term %prec prec_prefix_op
    { Tidapp (Qident $1, [$2]) }
| MINUS INTEGER
    { Tidapp (Qident (mk_id (prefix "-") $startpos($1) $endpos($1)),
        [mk_term (Tconst (Number.ConstInt $2)) $startpos($2) $endpos($2)]) }
| MINUS REAL
    { Tidapp (Qident (mk_id (prefix "-") $startpos($1) $endpos($1)),
        [mk_term (Tconst (Number.ConstReal $2)) $startpos($2) $endpos($2)]) }
| l = term ; o = bin_op ; r = term
    { Tbinop (l, o, r) }
| l = term ; o = infix_op_1 ; r = term
    { Tinfix (l, o, r) }
| l = term ; o = infix_op_234 ; r = term
    { Tidapp (Qident o, [l; r]) }
| term_arg located(term_arg)+ (* FIXME/TODO: "term term_arg" *)
    { let join f (a,_,e) = mk_term (Tapply (f,a)) $startpos e in
      (List.fold_left join $1 $2).term_desc }
| IF term THEN term ELSE term
    { Tif ($2, $4, $6) }
| LET pattern EQUAL term IN term
    { let cast ty = { $4 with term_desc = Tcast ($4, ty) } in
      let pat, def = match $2.pat_desc with
        | Ptuple [] -> { $2 with pat_desc = Pwild }, cast (PTtuple [])
        | Pcast ({pat_desc = (Pvar (_,false)|Pwild)} as p, ty) -> p, cast ty
        | _ -> $2, $4 in
      match pat.pat_desc with
      | Pvar (id,false) -> Tlet (id, def, $6)
      | Pwild -> Tlet (id_anonymous pat.pat_loc, def, $6)
      | _ -> Tmatch (def, [pat, $6]) }
| LET labels(lident_op_id) EQUAL term IN term
    { Tlet ($2, $4, $6) }
| LET labels(lident_nq) mk_term(lam_defn) IN term
    { Tlet ($2, $3, $5) }
| LET labels(lident_op_id) mk_term(lam_defn) IN term
    { Tlet ($2, $3, $5) }
| MATCH term WITH match_cases(term) END
    { Tmatch ($2, $4) }
| MATCH comma_list2(term) WITH match_cases(term) END
    { Tmatch (mk_term (Ttuple $2) $startpos($2) $endpos($2), $4) }
| quant comma_list1(quant_vars) triggers DOT term
    { Tquant ($1, List.concat $2, $3, $5) }
| FUN binders ARROW term
    { Tquant (Dterm.DTlambda, $2, [], $4) }
| EPSILON
    { Loc.errorm "Epsilon terms are currently not supported in WhyML" }
| label term %prec prec_named
    { Tnamed ($1, $2) }
| term cast
    { Tcast ($1, $2) }

lam_defn:
| binders EQUAL term  { Tquant (Dterm.DTlambda, $1, [], $3) }

term_arg: mk_term(term_arg_) { $1 }
term_dot: mk_term(term_dot_) { $1 }

term_arg_:
| qualid                    { Tident $1 }
| numeral                   { Tconst $1 }
| TRUE                      { Ttrue }
| FALSE                     { Tfalse }
| o = oppref ; a = term_arg { Tidapp (Qident o, [a]) }
| term_sub_                 { $1 }

term_dot_:
| lqualid                   { Tident $1 }
| o = oppref ; a = term_dot { Tidapp (Qident o, [a]) }
| term_sub_                 { $1 }

term_block:
| LEFTPAR term RIGHTPAR                             { $2.term_desc }
| LEFTPAR RIGHTPAR                                  { Ttuple [] }
| LEFTPAR comma_list2(term) RIGHTPAR                { Ttuple $2 }
| LEFTBRC field_list1(term) RIGHTBRC                { Trecord $2 }
| LEFTBRC term_arg WITH field_list1(term) RIGHTBRC  { Tupdate ($2,$4) }

term_sub_:
| term_block                                        { $1 }
| uqualid DOT mk_term(term_block)                   { Tscope ($1, $3) }
| term_dot DOT lqualid_rich                         { Tidapp ($3,[$1]) }
| term_arg LEFTSQ term RIGHTSQ
    { Tidapp (get_op $startpos($2) $endpos($2), [$1;$3]) }
| term_arg LEFTSQ term LARROW term RIGHTSQ
    { Tidapp (set_op $startpos($2) $endpos($2), [$1;$3;$5]) }
| term_arg LEFTSQ term DOTDOT term RIGHTSQ
    { Tidapp (sub_op $startpos($2) $endpos($2), [$1;$3;$5]) }
| term_arg LEFTSQ term DOTDOT RIGHTSQ
    { Tidapp (above_op $startpos($2) $endpos($2), [$1;$3]) }
| term_arg LEFTSQ DOTDOT term RIGHTSQ
    { Tidapp (below_op $startpos($2) $endpos($2), [$1;$4]) }

field_list1(X):
| fl = semicolon_list1(separated_pair(lqualid, EQUAL, X)) { fl }

match_cases(X):
| cl = bar_list1(separated_pair(pattern, ARROW, X)) { cl }

quant_vars:
| binder_var+ cast? { List.map (fun (l,i) -> l, i, false, $2) $1 }

triggers:
| (* epsilon *)                                                 { [] }
| LEFTSQ separated_nonempty_list(BAR,comma_list1(term)) RIGHTSQ { $2 }

%inline bin_op:
| ARROW   { Dterm.DTimplies }
| LRARROW { Dterm.DTiff }
| OR      { Dterm.DTor }
| BARBAR  { Dterm.DTor_asym }
| AND     { Dterm.DTand }
| AMPAMP  { Dterm.DTand_asym }
| BY      { Dterm.DTby }
| SO      { Dterm.DTso }

quant:
| FORALL  { Dterm.DTforall }
| EXISTS  { Dterm.DTexists }

numeral:
| INTEGER { Number.ConstInt $1 }
| REAL    { Number.ConstReal $1 }

(* Program declarations *)

prog_decl:
| VAL ghost kind labels(lident_rich) mk_expr(val_defn) { Dlet ($4, $2, $3, $5) }
| LET ghost kind labels(lident_rich) mk_expr(fun_defn) { Dlet ($4, $2, $3, $5) }
| LET ghost kind labels(lident_rich) const_defn        { Dlet ($4, $2, $3, $5) }
| LET REC with_list1(rec_defn)                         { Drec $3 }
| EXCEPTION labels(uident_nq)         { Dexn ($2, PTtuple [], Ity.MaskVisible) }
| EXCEPTION labels(uident_nq) return  { Dexn ($2, fst $3, snd $3) }

ghost:
| (* epsilon *) { false }
| GHOST         { true }

kind:
| (* epsilon *) { Expr.RKnone }
| FUNCTION      { Expr.RKfunc }
| CONSTANT      { Expr.RKfunc }
| PREDICATE     { Expr.RKpred }
| LEMMA         { Expr.RKlemma }

(* Function definitions *)

rec_defn:
| ghost kind labels(lident_rich) binders ret_opt spec EQUAL spec seq_expr
    { $3, $1, $2, $4, fst $5, snd $5, spec_union $6 $8, $9 }

fun_defn:
| binders ret_opt spec EQUAL spec seq_expr
    { Efun ($1, fst $2, snd $2, spec_union $3 $5, $6) }

val_defn:
| params ret_opt spec
    { Eany ($1, Expr.RKnone, fst $2, snd $2, $3) }

const_defn:
| cast EQUAL seq_expr   { { $3 with expr_desc = Ecast ($3, $1) } }
| EQUAL seq_expr        { $2 }

(* Program expressions *)

mk_expr(X): d = X { mk_expr d $startpos $endpos }

seq_expr:
| expr %prec below_SEMI   { $1 }
| expr SEMICOLON          { $1 }
| expr SEMICOLON seq_expr { mk_expr (Esequence ($1, $3)) $startpos $endpos }

expr: e = mk_expr(expr_) { e }

expr_:
| expr_arg_
    { match $1 with (* break the infix relation chain *)
      | Einfix (l,o,r) -> Einnfix (l,o,r) | d -> d }
| expr AMPAMP expr
    { Eand ($1, $3) }
| expr BARBAR expr
    { Eor ($1, $3) }
| NOT expr
    { Enot $2 }
| prefix_op expr %prec prec_prefix_op
    { Eidapp (Qident $1, [$2]) }
| MINUS INTEGER
    { Eidapp (Qident (mk_id (prefix "-") $startpos($1) $endpos($1)),
        [mk_expr (Econst (Number.ConstInt $2)) $startpos($2) $endpos($2)]) }
| MINUS REAL
    { Eidapp (Qident (mk_id (prefix "-") $startpos($1) $endpos($1)),
        [mk_expr (Econst (Number.ConstReal $2)) $startpos($2) $endpos($2)]) }
| l = expr ; o = infix_op_1 ; r = expr
    { Einfix (l,o,r) }
| l = expr ; o = infix_op_234 ; r = expr
    { Eidapp (Qident o, [l;r]) }
| expr_arg located(expr_arg)+ (* FIXME/TODO: "expr expr_arg" *)
    { let join f (a,_,e) = mk_expr (Eapply (f,a)) $startpos e in
      (List.fold_left join $1 $2).expr_desc }
| IF seq_expr THEN expr ELSE expr
    { Eif ($2, $4, $6) }
| IF seq_expr THEN expr %prec prec_no_else
    { Eif ($2, $4, mk_expr (Etuple []) $startpos $endpos) }
| expr LARROW expr
    { let loc = floc $startpos $endpos in
      let rec down ll rl = match ll, rl with
        | {expr_desc = Eidapp (q, [e1])}::ll, e2::rl -> (e1,q,e2) :: down ll rl
        | {expr_desc = Eidapp (Qident id, [_;_]); expr_loc = loc}::_, _::_
          when id.id_str = mixfix "[]" -> Loc.errorm ~loc
            "Parallel array assignments are not allowed"
        | {expr_loc = loc}::_, _::_ -> Loc.errorm ~loc
            "Invalid left expression in an assignment"
        | [], [] -> []
        | _ -> Loc.errorm ~loc "Invalid parallel assignment" in
      match $1.expr_desc, $3.expr_desc with
        | Eidapp (Qident id, [e1;e2]), _ when id.id_str = mixfix "[]" ->
            Eidapp (Qident {id with id_str = mixfix "[]<-"}, [e1;e2;$3])
        | Etuple ll, Etuple rl -> Eassign (down ll rl)
        | Etuple _, _ -> Loc.errorm ~loc "Invalid parallel assignment"
        | _, _ -> Eassign (down [$1] [$3]) }
| LET ghost kind let_pattern EQUAL seq_expr IN seq_expr
    { let re_pat pat d = { pat with pat_desc = d } in
      let rec ghostify pat = match pat.pat_desc with
        (* let_pattern marks the opening variable with Ptuple [_] *)
        | Ptuple [{pat_desc = Pvar (id,_)}] -> re_pat pat (Pvar (id,$2))
        | Ptuple (p::pl) -> re_pat pat (Ptuple (ghostify p :: pl))
        | Pas (p,id,gh) -> re_pat pat (Pas (ghostify p, id, gh))
        | Por (p1,p2) -> re_pat pat (Por (ghostify p1, p2))
        | Pcast (p,t) -> re_pat pat (Pcast (ghostify p, t))
        | _ when $2 -> Loc.errorm ~loc:(floc $startpos($2) $endpos($2))
            "illegal ghost qualifier" (* $4 does not start with a Pvar *)
        | _ -> pat in
      let pat = ghostify $4 in
      let kind = match pat.pat_desc with
        | _ when $3 = Expr.RKnone -> $3
        | Pvar (_,_) | Pcast ({pat_desc = Pvar (_,_)},_) -> $3
        | _ -> Loc.errorm ~loc:(floc $startpos($3) $endpos($3))
            "illegal kind qualifier" in
      let cast ty = { $6 with expr_desc = Ecast ($6, ty) } in
      let pat, def = match pat.pat_desc with
        | Ptuple [] -> re_pat pat Pwild, cast (PTtuple [])
        | Pcast ({pat_desc = (Pvar _|Pwild)} as pat, ty) -> pat, cast ty
        | _ -> pat, $6 in
      match pat.pat_desc with
      | Pvar (id, gh) -> Elet (id, gh, kind, def, $8)
      | Pwild -> Elet (id_anonymous pat.pat_loc, false, kind, def, $8)
      | _ -> Ematch (def, [pat, $8]) }
| LET ghost kind labels(lident_op_id) EQUAL seq_expr IN seq_expr
    { Elet ($4, $2, $3, $6, $8) }
| LET ghost kind labels(lident_nq) mk_expr(fun_defn) IN seq_expr
    { Elet ($4, $2, $3, $5, $7) }
| LET ghost kind labels(lident_op_id) mk_expr(fun_defn) IN seq_expr
    { Elet ($4, $2, $3, $5, $7) }
| LET REC with_list1(rec_defn) IN seq_expr
    { Erec ($3, $5) }
| FUN binders spec ARROW spec seq_expr
    { Efun ($2, None, Ity.MaskVisible, spec_union $3 $5, $6) }
| ANY return spec
    { Eany ([], Expr.RKnone, Some (fst $2), snd $2, $3) }
| VAL ghost kind labels(lident_rich) mk_expr(val_defn) IN seq_expr
    { Elet ($4, $2, $3, $5, $7) }
| MATCH seq_expr WITH match_cases(seq_expr) END
    { Ematch ($2, $4) }
| MATCH comma_list2(expr) WITH match_cases(seq_expr) END
    { Ematch (mk_expr (Etuple $2) $startpos($2) $endpos($2), $4) }
| EXCEPTION labels(uident) IN seq_expr
    { Eexn ($2, PTtuple [], Ity.MaskVisible, $4) }
| EXCEPTION labels(uident) return IN seq_expr
    { Eexn ($2, fst $3, snd $3, $5) }
| LABEL labels(uident) IN seq_expr
    { Emark ($2, $4) }
| WHILE seq_expr DO loop_annotation seq_expr DONE
    { let inv, var = $4 in Ewhile ($2, inv, var, $5) }
| FOR lident_nq EQUAL seq_expr for_direction seq_expr DO invariant* seq_expr DONE
    { Efor ($2, $4, $5, $6, $8, $9) }
| ABSURD
    { Eabsurd }
| RAISE uqualid expr_arg?
    { Eraise ($2, $3) }
| RAISE LEFTPAR uqualid expr_arg? RIGHTPAR
    { Eraise ($3, $4) }
| RETURN expr_arg?
    { Eraise (Qident (mk_id Dexpr.old_mark $startpos($1) $endpos($1)), $2) }
| TRY seq_expr WITH bar_list1(exn_handler) END
    { Etry ($2, $4) }
| GHOST expr
    { Eghost $2 }
| assertion_kind LEFTBRC term RIGHTBRC
    { Eassert ($1, $3) }
| label expr %prec prec_named
    { Enamed ($1, $2) }
| expr cast
    { Ecast ($1, $2) }

expr_arg: e = mk_expr(expr_arg_) { e }
expr_dot: e = mk_expr(expr_dot_) { e }

expr_arg_:
| qualid                    { Eident $1 }
| numeral                   { Econst $1 }
| TRUE                      { Etrue }
| FALSE                     { Efalse }
| o = oppref ; a = expr_arg { Eidapp (Qident o, [a]) }
| expr_sub                  { $1 }

expr_dot_:
| lqualid                   { Eident $1 }
| o = oppref ; a = expr_dot { Eidapp (Qident o, [a]) }
| expr_sub                  { $1 }

expr_block:
| BEGIN single_spec spec seq_expr END
    { Efun ([], None, Ity.MaskVisible, spec_union $2 $3, $4) }
| BEGIN single_spec spec END
    { let e = mk_expr (Etuple []) $startpos $endpos in
      Efun ([], None, Ity.MaskVisible, spec_union $2 $3, e) }
| BEGIN seq_expr END                                { $2.expr_desc }
| LEFTPAR seq_expr RIGHTPAR                         { $2.expr_desc }
| BEGIN END                                         { Etuple [] }
| LEFTPAR RIGHTPAR                                  { Etuple [] }
| LEFTPAR comma_list2(expr) RIGHTPAR                { Etuple $2 }
| LEFTBRC field_list1(expr) RIGHTBRC                { Erecord $2 }
| LEFTBRC expr_arg WITH field_list1(expr) RIGHTBRC  { Eupdate ($2, $4) }

expr_pure:
| LEFTBRC qualid RIGHTBRC                           { Eidpur $2 }
| uqualid DOT LEFTBRC ident_rich RIGHTBRC           { Eidpur (Qdot ($1, $4)) }

expr_sub:
| expr_block                                        { $1 }
| expr_pure                                         { $1 }
| uqualid DOT mk_expr(expr_block)                   { Escope ($1, $3) }
| expr_dot DOT mk_expr(expr_pure)                   { Eapply ($3, $1) }
| expr_dot DOT lqualid_rich                         { Eidapp ($3, [$1]) }
| PURE LEFTBRC term RIGHTBRC                        { Epure $3 }
| expr_arg LEFTSQ expr RIGHTSQ
    { Eidapp (get_op $startpos($2) $endpos($2), [$1;$3]) }
| expr_arg LEFTSQ expr LARROW expr RIGHTSQ
    { Eidapp (set_op $startpos($2) $endpos($2), [$1;$3;$5]) }
| expr_arg LEFTSQ expr DOTDOT expr RIGHTSQ
    { Eidapp (sub_op $startpos($2) $endpos($2), [$1;$3;$5]) }
| expr_arg LEFTSQ expr DOTDOT RIGHTSQ
    { Eidapp (above_op $startpos($2) $endpos($2), [$1;$3]) }
| expr_arg LEFTSQ DOTDOT expr RIGHTSQ
    { Eidapp (below_op $startpos($2) $endpos($2), [$1;$4]) }

loop_annotation:
| (* epsilon *)
    { [], [] }
| invariant loop_annotation
    { let inv, var = $2 in $1 :: inv, var }
| variant loop_annotation
    { let inv, var = $2 in inv, variant_union $1 var }

exn_handler:
| uqualid pat_arg? ARROW seq_expr { $1, $2, $4 }

assertion_kind:
| ASSERT  { Expr.Assert }
| ASSUME  { Expr.Assume }
| CHECK   { Expr.Check }

for_direction:
| TO      { Expr.To }
| DOWNTO  { Expr.DownTo }

(* Specification *)

spec:
| (* epsilon *)     { empty_spec }
| single_spec spec  { spec_union $1 $2 }

single_spec:
| REQUIRES LEFTBRC term RIGHTBRC
    { { empty_spec with sp_pre = [$3] } }
| ENSURES LEFTBRC ensures RIGHTBRC
    { { empty_spec with sp_post = [floc $startpos($3) $endpos($3), $3] } }
| RETURNS LEFTBRC match_cases(term) RIGHTBRC
    { { empty_spec with sp_post = [floc $startpos($3) $endpos($3), $3] } }
| RAISES LEFTBRC bar_list1(raises) RIGHTBRC
    { { empty_spec with sp_xpost = [floc $startpos($3) $endpos($3), $3] } }
| READS  LEFTBRC comma_list0(lqualid) RIGHTBRC
    { { empty_spec with sp_reads = $3; sp_checkrw = true } }
| WRITES LEFTBRC comma_list0(term) RIGHTBRC
    { { empty_spec with sp_writes = $3; sp_checkrw = true } }
| ALIAS LEFTBRC comma_list0(alias_pair) RIGHTBRC
	{ { empty_spec with sp_alias = $3 } } (* FIXME checkrw ? *)
| RAISES LEFTBRC comma_list1(xsymbol) RIGHTBRC
    { { empty_spec with sp_xpost = [floc $startpos($3) $endpos($3), $3] } }
| DIVERGES
    { { empty_spec with sp_diverge = true } }
| variant
    { { empty_spec with sp_variant = $1 } }

%inline alias_pair: term TILDE term { ($1,$3) }

ensures:
| term
    { let id = mk_id "result" $startpos $endpos in
      [mk_pat (Pvar (id,false)) $startpos $endpos, $1] }

raises:
| uqualid ARROW term
    { $1, Some (mk_pat (Ptuple []) $startpos($1) $endpos($1), $3) }
| uqualid pat_arg ARROW term
    { $1, Some ($2, $4) }

xsymbol:
| uqualid { $1, None }

invariant:
| INVARIANT LEFTBRC term RIGHTBRC { $3 }

variant:
| VARIANT LEFTBRC comma_list1(single_variant) RIGHTBRC { $3 }

single_variant:
| term preceded(WITH,lqualid)? { $1, $2 }

ret_opt:
| (* epsilon *)     { None, Ity.MaskVisible }
| COLON return      { Some (fst $2), snd $2 }

return:
| ret_arg           { $1 }
| lqualid ty_arg+   { PTtyapp ($1, $2), Ity.MaskVisible }
| ret_arg ARROW ty  { PTarrow (fst $1, $3),
                      if Ity.mask_ghost (snd $1) then
                        raise Error else Ity.MaskVisible }
| GHOST ty          { $2, Ity.MaskGhost }

ret_arg:
| lqualid                               { PTtyapp ($1, []), Ity.MaskVisible }
| quote_lident                          { PTtyvar $1, Ity.MaskVisible }
| LEFTPAR RIGHTPAR                      { PTtuple [], Ity.MaskVisible }
| LEFTBRC ty RIGHTBRC                   { PTpure  $2, Ity.MaskVisible }
| LEFTPAR ret_sub RIGHTPAR              { PTparen (fst $2), snd $2 }
| LEFTPAR comma_list2(ret_sub) RIGHTPAR { PTtuple (List.map fst $2),
                                    Ity.MaskTuple (List.map snd $2) }

ret_sub:
| ty                { $1, Ity.MaskVisible }
| GHOST ty          { $2, Ity.MaskGhost }

(* Patterns *)

mk_pat(X): X { mk_pat $1 $startpos $endpos }

pattern: mk_pat(pattern_) { $1 }
pat_arg: mk_pat(pat_arg_) { $1 }

pattern_:
| pat_conj_                             { $1 }
| mk_pat(pat_conj_) BAR pattern         { Por ($1,$3) }

pat_conj_:
| pat_uni_                              { $1 }
| comma_list2(mk_pat(pat_uni_))         { Ptuple $1 }

pat_uni_:
| pat_arg_                              { $1 }
| uqualid pat_arg+                      { Papp ($1,$2) }
| mk_pat(pat_uni_) AS ghost labels(lident_nq)
                                        { Pas ($1,$4,$3) }
| mk_pat(pat_uni_) cast                 { Pcast ($1,$2) }

pat_arg_:
| pat_arg_shared_                       { $1 }
| labels(lident_nq)                     { Pvar ($1,false) }
| GHOST labels(lident_nq)               { Pvar ($2,true) }

pat_arg_shared_:
| UNDERSCORE                            { Pwild }
| uqualid                               { Papp ($1,[]) }
| LEFTPAR RIGHTPAR                      { Ptuple [] }
| LEFTPAR pattern_ RIGHTPAR             { $2 }
| LEFTBRC field_list1(pattern) RIGHTBRC { Prec $2 }

(* let-patterns that cannot start with "ghost" *)

let_pattern: mk_pat(let_pattern_) { $1 }

let_pattern_:
| let_pat_conj_                         { $1 }
| mk_pat(let_pat_conj_) BAR pattern     { Por ($1,$3) }

let_pat_conj_:
| let_pat_uni_                          { $1 }
| mk_pat(let_pat_uni_) COMMA comma_list1(mk_pat(pat_uni_))
                                        { Ptuple ($1::$3) }

let_pat_uni_:
| let_pat_arg_                          { $1 }
| uqualid pat_arg+                      { Papp ($1,$2) }
| mk_pat(let_pat_uni_) AS ghost labels(lident_nq)
                                        { Pas ($1,$4,$3) }
| mk_pat(let_pat_uni_) cast             { Pcast ($1,$2) }

let_pat_arg_:
| pat_arg_shared_ { $1 }
| labels(lident_nq)  { Ptuple [{pat_desc = Pvar ($1,false); pat_loc = $1.id_loc}] }

(* Idents *)

ident:
| uident { $1 }
| lident { $1 }

ident_nq:
| uident_nq { $1 }
| lident_nq { $1 }

uident:
| UIDENT          { mk_id $1 $startpos $endpos }
| UIDENT_QUOTE    { mk_id $1 $startpos $endpos }

uident_nq:
| UIDENT          { mk_id $1 $startpos $endpos }
| UIDENT_QUOTE    { let loc = floc $startpos($1) $endpos($1) in
                    Loc.errorm ~loc "Symbol %s cannot be user-defined" $1 }

lident:
| LIDENT          { mk_id $1 $startpos $endpos }
| lident_keyword  { mk_id $1 $startpos $endpos }
| LIDENT_QUOTE    { mk_id $1 $startpos $endpos }

lident_nq:
| LIDENT          { mk_id $1 $startpos $endpos }
| lident_keyword  { mk_id $1 $startpos $endpos }
| LIDENT_QUOTE    { let loc = floc $startpos($1) $endpos($1) in
                    Loc.errorm ~loc "Symbol %s cannot be user-defined" $1 }

lident_keyword:
| RANGE           { "range" }
| FLOAT           { "float" }

quote_lident:
| QUOTE_LIDENT  { mk_id $1 $startpos $endpos }

(* Idents + symbolic operation names *)

ident_rich:
| uident        { $1 }
| lident        { $1 }
| lident_op_id  { $1 }

lident_rich:
| lident_nq     { $1 }
| lident_op_id  { $1 }

lident_op_id:
| LEFTPAR lident_op RIGHTPAR  { mk_id $2 $startpos $endpos }
| LEFTPAR_STAR_RIGHTPAR       { mk_id (infix "*") $startpos $endpos }

lident_op:
| op_symbol               { infix $1 }
| op_symbol UNDERSCORE    { prefix $1 }
| MINUS     UNDERSCORE    { prefix "-" }
| EQUAL                   { infix "=" }
| MINUS                   { infix "-" }
| OPPREF                  { prefix $1 }
| LEFTSQ RIGHTSQ          { mixfix "[]" }
| LEFTSQ LARROW RIGHTSQ   { mixfix "[<-]" }
| LEFTSQ RIGHTSQ LARROW   { mixfix "[]<-" }
| LEFTSQ UNDERSCORE DOTDOT UNDERSCORE RIGHTSQ { mixfix "[_.._]" }
| LEFTSQ            DOTDOT UNDERSCORE RIGHTSQ { mixfix "[.._]" }
| LEFTSQ UNDERSCORE DOTDOT            RIGHTSQ { mixfix "[_..]" }

op_symbol:
| OP1 { $1 }
| OP2 { $1 }
| OP3 { $1 }
| OP4 { $1 }
| LT  { "<" }
| GT  { ">" }

%inline oppref:
| o = OPPREF { mk_id (prefix o)  $startpos $endpos }

prefix_op:
| op_symbol { mk_id (prefix $1)  $startpos $endpos }
| MINUS     { mk_id (prefix "-") $startpos $endpos }

%inline infix_op_1:
| o = OP1   { mk_id (infix o)    $startpos $endpos }
| EQUAL     { mk_id (infix "=")  $startpos $endpos }
| LTGT      { mk_id (infix "<>") $startpos $endpos }
| LT        { mk_id (infix "<")  $startpos $endpos }
| GT        { mk_id (infix ">")  $startpos $endpos }

%inline infix_op_234:
| o = OP2   { mk_id (infix o)    $startpos $endpos }
| o = OP3   { mk_id (infix o)    $startpos $endpos }
| o = OP4   { mk_id (infix o)    $startpos $endpos }
| MINUS     { mk_id (infix "-")  $startpos $endpos }

(* Qualified idents *)

qualid:
| ident_rich                { Qident $1 }
| uqualid DOT ident_rich    { Qdot ($1, $3) }

lqualid_rich:
| lident                    { Qident $1 }
| lident_op_id              { Qident $1 }
| uqualid DOT lident        { Qdot ($1, $3) }
| uqualid DOT lident_op_id  { Qdot ($1, $3) }

lqualid:
| lident              { Qident $1 }
| uqualid DOT lident  { Qdot ($1, $3) }

uqualid:
| uident              { Qident $1 }
| uqualid DOT uident  { Qdot ($1, $3) }

(* Theory/Module names *)

tqualid:
| uident                { Qident $1 }
| any_qualid DOT uident { Qdot ($1, $3) }

any_qualid:
| sident                { Qident $1 }
| any_qualid DOT sident { Qdot ($1, $3) }

sident:
| ident   { $1 }
| STRING  { mk_id $1 $startpos $endpos }

(* Labels and position markers *)

labels(X): X label* { add_lab $1 $2 }

label:
| STRING    { Lstr (Ident.create_label $1) }
| POSITION  { Lpos $1 }

(* Miscellaneous *)

bar_list1(X):
| ioption(BAR) ; xl = separated_nonempty_list(BAR, X) { xl }

with_list1(X):
| separated_nonempty_list(WITH, X)  { $1 }

comma_list2(X):
| X COMMA comma_list1(X) { $1 :: $3 }

comma_list1(X):
| separated_nonempty_list(COMMA, X) { $1 }

comma_list0(X):
| xl = separated_list(COMMA, X) { xl }

semicolon_list1(X):
| x = X ; ioption(SEMICOLON)                  { [x] }
| x = X ; SEMICOLON ; xl = semicolon_list1(X) { x :: xl }

located(X): X { $1, $startpos, $endpos }
