(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

%{
  open Ptree

  let qualid_last = function Qident x | Qdot (_, x) -> x

  let use_as q = function Some x -> x | None -> qualid_last q

  let floc s e = Loc.extract (s,e)

  let add_attr id l = (* id.id_ats is usually nil *)
    { id with id_ats = List.rev_append id.id_ats l }

  let id_anonymous loc = { id_str = "_"; id_ats = []; id_loc = loc }

  let mk_int_const neg lit =
    Number.{ ic_negative = neg ; ic_abs = lit}

  let mk_real_const neg lit =
    Number.{ rc_negative = neg ; rc_abs = lit}

  let mk_id id s e = { id_str = id; id_ats = []; id_loc = floc s e }

  let get_op  q s e = Qident (mk_id (Ident.op_get q) s e)
  let upd_op  q s e = Qident (mk_id (Ident.op_update q) s e)
  let cut_op  q s e = Qident (mk_id (Ident.op_cut q) s e)
  let rcut_op q s e = Qident (mk_id (Ident.op_rcut q) s e)
  let lcut_op q s e = Qident (mk_id (Ident.op_lcut q) s e)

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
    sp_partial = false;
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

  let break_id    = "'Break"
  let continue_id = "'Continue"
  let return_id   = "'Return"

  let apply_return pat sp =
    let apply = function
      | loc, [{pat_desc = Pvar {id_str = "result"; id_loc = l}}, f]
        when Loc.equal loc l -> loc, [pat, f]
      | post -> post in
    match pat.pat_desc with
    | Pwild -> sp
    | _ -> { sp with sp_post = List.map apply sp.sp_post }

  type partial =
    | Regular
    | Partial
    | Ghost

  let ghost part = (part = Ghost)

  let apply_partial_sp part sp =
    if part <> Partial then sp else
    { sp with sp_partial = true }

  let apply_partial part e =
    if part <> Partial then e else
    let ed = match e.expr_desc with
      | Efun (_::_ as bl, op, m, s, ex) ->
          Efun (bl, op, m, apply_partial_sp part s, ex)
      | Eany (_::_ as pl, rsk, op, m, s) ->
          Eany (pl, rsk, op, m, apply_partial_sp part s)
      | _ ->
          Loc.errorm ~loc:e.expr_loc
            "this expression cannot be declared partial" in
    { e with expr_desc = ed }

  let we_attr = Ident.create_attribute "expl:witness existence"

  let pre_of_any any_loc ty ql =
    if ql = [] then [] else
    let ri loc = { id_str = "result"; id_loc = loc; id_ats = [] } in
    let rt loc = { term_desc = Tident (Qident (ri loc)); term_loc = loc } in
    let cast t ty = { t with term_desc = Tcast (t,ty) } in
    let case (loc, pfl) =
      let mk_t d = { term_desc = d; term_loc = loc } in
      match pfl with
      | [pat, f] ->
          let rec unfold d p = match p.pat_desc with
            | Pparen p | Pscope (_,p) -> unfold d p
            | Pcast (p,ty) -> unfold (cast d ty) p
            | Ptuple [] -> unfold (cast d (PTtuple []))
                                  { p with pat_desc = Pwild }
            | Pvar { id_str = "result" } | Pwild ->
              begin match d.term_desc with
                | Tident (Qident _) -> f (* no type casts on d *)
                | _ -> mk_t (Tlet (id_anonymous p.pat_loc, d, f))
              end
            | Pvar id -> mk_t (Tlet (id, d, f))
            | _ -> mk_t (Tcase (d, pfl)) in
          unfold (rt loc) pat
      | _ -> mk_t (Tcase (rt loc, pfl)) in
    let mk_t desc = { term_desc = desc; term_loc = any_loc } in
    let rec join ql = match ql with
      | [] -> assert false (* never *)
      | [q] -> case q
      | q::ql -> mk_t (Tbinop (case q, Dterm.DTand_asym, join ql)) in
    let id = add_attr (ri any_loc) [ATstr Ity.break_attr] in
    let bl = [any_loc, Some id, false, Some ty] in
    let p = mk_t (Tquant (Dterm.DTexists, bl, [], join ql)) in
    [mk_t (Tattr (ATstr we_attr, p))]

  let double_ref {id_loc = loc} =
    Loc.errorm ~loc "this variable is already a reference"

  let set_ref id =
    List.iter (function
      | ATstr a when Ident.attr_equal a Pmodule.ref_attr ->
          double_ref id
      | _ -> ()) id.id_ats;
    { id with id_ats = ATstr Pmodule.ref_attr :: id.id_ats }

  let set_ref_opt loc r = function
    | id when not r -> id
    | Some id -> Some (set_ref id)
    | None -> Loc.errorm ~loc "anonymous parameters cannot be references"

  let binder_of_id id =
    if id.id_str = "ref" then Loc.error ~loc:id.id_loc Error;
    (* TODO: recognize and fail on core idents *)
    Some id

  let lq_as_ref = function
    | Qident {id_str = "ref"} -> ()
    | _ -> raise Error

  let error_param loc =
    Loc.errorm ~loc "cannot determine the type of the parameter"

  let error_loc loc = Loc.error ~loc Error

  let () = Exn_printer.register (fun fmt exn -> match exn with
    | Error -> Format.fprintf fmt "syntax error"
    | _ -> raise exn)

  let core_ident_error  = format_of_string
    "Symbol %s cannot be user-defined. User-defined symbol cannot use ' \
      before a letter. You can only use ' followed by _ or a number."

  let add_record_projections (d: Ptree.decl) =
    let meta_id = {id_str = Theory.(meta_record.meta_name);
                   id_ats = [];
                   id_loc = Loc.dummy_position}
    in
    match d with
    | Dtype dl ->
        List.iter (fun td ->
          match td.td_def with
          | TDrecord fl ->
              List.iter (fun field ->
                let m = Dmeta (meta_id, [Mfs (Qident field.f_ident)]) in
                Typing.add_decl field.f_loc m
                )
                fl
          | _ -> ()
          )
          dl
    | _ -> ()
%}

(* Tokens *)

%token <string> LIDENT CORE_LIDENT UIDENT CORE_UIDENT
%token <Number.integer_literal> INTEGER
%token <string> OP1 OP2 OP3 OP4 OPPREF
%token <Number.real_literal> REAL
%token <string> STRING
%token <string> ATTRIBUTE
%token <Loc.position> POSITION
%token <string> QUOTE_LIDENT
%token <string> RIGHTSQ_QUOTE (* ]'' *)
%token <string> RIGHTPAR_QUOTE (* )'spec *)
%token <string> RIGHTPAR_USCORE (* )_spec *)

(* keywords *)

%token AS AXIOM BY CLONE COINDUCTIVE CONSTANT
%token ELSE END EPSILON EXISTS EXPORT FALSE FLOAT FORALL FUNCTION
%token GOAL IF IMPORT IN INDUCTIVE LEMMA
%token LET MATCH META NOT PREDICATE RANGE SCOPE
%token SO THEN THEORY TRUE TYPE USE WITH

(* program keywords *)

%token ABSTRACT ABSURD ALIAS ANY ASSERT ASSUME AT BEGIN BREAK CHECK
%token CONTINUE DIVERGES DO DONE DOWNTO ENSURES EXCEPTION FOR
%token FUN GHOST INVARIANT LABEL MODULE MUTABLE OLD PARTIAL
%token PRIVATE PURE RAISE RAISES READS REF REC REQUIRES
%token RETURN RETURNS TO TRY VAL VARIANT WHILE WRITES

(* symbols *)

%token AND ARROW
%token AMP BAR
%token COLON COMMA
%token DOT DOTDOT EQUAL LT GT LTGT MINUS
%token LEFTPAR LEFTSQ
%token LARROW LRARROW OR
%token RIGHTPAR RIGHTSQ
%token UNDERSCORE

%token EOF

(* program symbols *)

%token AMPAMP BARBAR LEFTBRC RIGHTBRC SEMICOLON

(* Precedences *)

%nonassoc below_SEMI
%nonassoc SEMICOLON
%nonassoc LET VAL EXCEPTION
%nonassoc prec_no_else
%nonassoc DOT ELSE RETURN
%nonassoc prec_no_spec
%nonassoc REQUIRES ENSURES RETURNS RAISES READS WRITES ALIAS DIVERGES VARIANT
%nonassoc below_LARROW
%nonassoc LARROW
%nonassoc below_COMMA
%nonassoc COMMA
%nonassoc AS
%nonassoc GHOST
%nonassoc prec_attr
%nonassoc COLON (* weaker than -> because of t: a -> b *)
%right ARROW LRARROW BY SO
%right OR BARBAR
%right AND AMPAMP
%nonassoc NOT
%right EQUAL LTGT LT GT OP1
%nonassoc AT OLD
%left OP2 MINUS
%left OP3
%left OP4
%nonassoc prec_prefix_op
%nonassoc INTEGER REAL (* stronger than MINUS *)
%nonassoc LEFTSQ
%nonassoc OPPREF

(* Entry points *)

%start <Pmodule.pmodule Wstdlib.Mstr.t> mlw_file
%start <Ptree.term> term_eof
%start <Ptree.qualid> qualid_eof
%start <Ptree.qualid list> qualid_comma_list_eof
%start <Ptree.term list> term_comma_list_eof
%start <Ptree.ident list> ident_comma_list_eof

%%

(* parsing of a single term *)

term_eof:
| term EOF { $1 }

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
| THEORY attrs(uident_nq)  { Typing.open_module $2 }
| MODULE attrs(uident_nq)  { Typing.open_module $2 }

scope_head:
| SCOPE boption(IMPORT) uident
    { Typing.open_scope (floc $startpos $endpos) $3; $2 }

module_decl:
| scope_head module_decl* END
    { Typing.close_scope (floc $startpos($1) $endpos($1)) ~import:$1 }
| IMPORT uqualid
    { Typing.import_scope (floc $startpos $endpos) $2 }
| d = pure_decl | d = prog_decl | d = meta_decl
    { Typing.add_decl (floc $startpos $endpos) d;
      add_record_projections d
    }
| use_clone { () }

(* Use and clone *)

use_clone:
| USE EXPORT tqualid
    { Typing.add_decl (floc $startpos $endpos) (Duse $3) }
| CLONE EXPORT tqualid clone_subst
    { Typing.add_decl (floc $startpos $endpos) (Dclone ($3, $4)) }
| USE boption(IMPORT) m_as_list = comma_list1(use_as)
    { let loc = floc $startpos $endpos in
      let exists_as = List.exists (fun (_, q) -> q <> None) m_as_list in
      if $2 && not exists_as then Warning.emit ~loc
        "the keyword `import' is redundant here and can be omitted";
      let add_import (m, q) = let import = $2 || q = None in
        Typing.open_scope loc (use_as m q);
        Typing.add_decl loc (Duse m);
        Typing.close_scope loc ~import  in
      List.iter add_import m_as_list }
| CLONE boption(IMPORT) tqualid option(preceded(AS, uident)) clone_subst
    { let loc = floc $startpos $endpos in
      if $2 && $4 = None then Warning.emit ~loc
        "the keyword `import' is redundant here and can be omitted";
      let import = $2 || $4 = None in
      Typing.open_scope loc (use_as $3 $4);
      Typing.add_decl loc (Dclone ($3, $5));
      Typing.close_scope loc ~import }

use_as:
| n = tqualid q = option(preceded(AS, uident)) { (n, q) }

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
| AXIOM     DOT                 { CSprop  (Decl.Paxiom) }
| LEMMA     DOT                 { CSprop  (Decl.Plemma) }
| GOAL      DOT                 { CSprop  (Decl.Pgoal) }

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
| INTEGER           { Mint (Number.to_small_integer $1) }

(* Theory declarations *)

pure_decl:
| TYPE with_list1(type_decl)                { Dtype $2 }
| CONSTANT  constant_decl                   { Dlogic [$2] }
| FUNCTION  function_decl  with_logic_decl* { Dlogic ($2::$3) }
| PREDICATE predicate_decl with_logic_decl* { Dlogic ($2::$3) }
| INDUCTIVE   with_list1(inductive_decl)    { Dind (Decl.Ind, $2) }
| COINDUCTIVE with_list1(inductive_decl)    { Dind (Decl.Coind, $2) }
| AXIOM attrs(ident_nq) COLON term          { Dprop (Decl.Paxiom, $2, $4) }
| LEMMA attrs(ident_nq) COLON term          { Dprop (Decl.Plemma, $2, $4) }
| GOAL  attrs(ident_nq) COLON term          { Dprop (Decl.Pgoal, $2, $4) }

(* Type declarations *)

type_decl:
| attrs(lident_nq) ty_var* typedefn invariant* type_witness
  { let (vis, mut), def = $3 in
    { td_ident = $1; td_params = $2;
      td_vis = vis; td_mut = mut;
      td_inv = $4; td_wit = $5; td_def = def;
      td_loc = floc $startpos $endpos } }

type_witness:
| (* epsilon *)                           { [] }
| BY LEFTBRC field_list1(expr) RIGHTBRC   { $3 }

ty_var:
| attrs(quote_lident) { $1 }

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
| EQUAL LT RANGE int_constant int_constant GT
    { (Public, false), TDrange ($4, $5) }
| EQUAL LT FLOAT INTEGER INTEGER GT
    { (Public, false),
      TDfloat (Number.to_small_integer $4, Number.to_small_integer $5) }

int_constant:
| INTEGER       { Number.compute_int_literal $1 }
| MINUS INTEGER { BigInt.minus (Number.compute_int_literal $2) }

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
| field_modifiers ref_amp_id cast
  { let mut, ghs = $1 and rff, id = $2 in
    let ty = if rff then PTref [$3] else $3 in
    { f_ident = id; f_mutable = mut; f_ghost = ghs;
      f_pty = ty; f_loc = floc $startpos $endpos } }

%inline field_modifiers:
| (* epsilon *) { false, false }
| MUTABLE       { true,  false }
| GHOST         { false, true  }
| GHOST MUTABLE { true,  true  }
| MUTABLE GHOST { true,  true  }

(* we have to use lqualid instead of REF after field_modifiers
   to avoid a conflict with ty. However, if the given lqualid
   is not REF, then we want to fail as soon as possible: either
   at AMP, if it occurs after the lqualid, or else at COLON. *)
ref_amp_id:
| lq_as_ref AMP attrs(lident_nq)  { true,  double_ref $3 }
| lq_as_ref_id attr*              { true,  add_attr $1 $2 }
| AMP attrs(lident_nq)            { false, set_ref $2 }
| attrs(lident_nq)                { false, $1 }

lq_as_ref:    lqualid             { lq_as_ref $1 }
lq_as_ref_id: lqualid lident_nq   { lq_as_ref $1; set_ref $2 }

type_case:
| attrs(uident_nq) params { floc $startpos $endpos, $1, $2 }

(* Logic declarations *)

constant_decl:
| attrs(lident_rich) cast preceded(EQUAL,term)?
  { { ld_ident = $1;
      ld_params = []; ld_type = Some $2;
      ld_def = $3; ld_loc = floc $startpos $endpos } }

function_decl:
| attrs(lident_rich) params cast preceded(EQUAL,term)?
  { { ld_ident = $1; ld_params = $2; ld_type = Some $3;
      ld_def = $4; ld_loc = floc $startpos $endpos } }

predicate_decl:
| attrs(lident_rich) params preceded(EQUAL,term)?
  { { ld_ident = $1; ld_params = $2; ld_type = None;
      ld_def = $3; ld_loc = floc $startpos $endpos } }

with_logic_decl:
| WITH attrs(lident_rich) params cast? preceded(EQUAL,term)?
  { { ld_ident = $2; ld_params = $3; ld_type = $4;
      ld_def = $5; ld_loc = floc $startpos $endpos } }

(* Inductive declarations *)

inductive_decl:
| attrs(lident_rich) params ind_defn
  { { in_ident = $1; in_params = $2;
      in_def = $3; in_loc = floc $startpos $endpos } }

ind_defn:
| (* epsilon *)             { [] }
| EQUAL bar_list1(ind_case) { $2 }

ind_case:
| attrs(ident_nq) COLON term  { floc $startpos $endpos, $1, $3 }

(* Type expressions *)

ty:
| ty_arg          { $1 }
| lqualid ty_arg+ { PTtyapp ($1, $2) }
| ty ARROW ty     { PTarrow ($1, $3) }

ty_arg:
| lqualid                           { PTtyapp ($1, []) }
| quote_lident                      { PTtyvar $1 }
| uqualid DOT ty_block              { PTscope ($1, $3) }
| ty_block                          { $1 }

ty_block:
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

params1: param+  { List.concat $1 }

binders: binder+ { List.concat $1 }

param:
| special_binder
    { error_param (floc $startpos $endpos) }
| lident_nq attr+
    { error_param (floc $startpos $endpos) }
| ty_arg
    { [floc $startpos $endpos, None, false, $1] }
| LEFTPAR GHOST ty RIGHTPAR
    { [floc $startpos $endpos, None, true, $3] }
| LEFTPAR binder_vars_rest RIGHTPAR
    { match snd $2 with [l,_] -> error_param l
      | _ -> error_loc (floc $startpos($3) $endpos($3)) }
| LEFTPAR GHOST binder_vars_rest RIGHTPAR
    { match snd $3 with [l,_] -> error_param l
      | _ -> error_loc (floc $startpos($4) $endpos($4)) }
| LEFTPAR binder_vars cast RIGHTPAR
    { let r = fst $2 in let ty = if r then PTref [$3] else $3 in
      List.map (fun (l,i) -> l, set_ref_opt l r i, false, ty) (snd $2) }
| LEFTPAR GHOST binder_vars cast RIGHTPAR
    { let r = fst $3 in let ty = if r then PTref [$4] else $4 in
      List.map (fun (l,i) -> l, set_ref_opt l r i, true, ty) (snd $3) }

binder:
| special_binder
    { let l,i = $1 in [l, i, false, None] }
| lident_nq attr+
    { [floc $startpos $endpos, Some (add_attr $1 $2), false, None] }
| ty_arg
    { match $1 with
      | PTparen (PTtyapp (Qident {id_str="ref"}, [PTtyapp (Qident id, [])])) ->
              [floc $startpos $endpos, binder_of_id (set_ref id), false, None]
      | PTtyapp (Qident id, [])
      | PTparen (PTtyapp (Qident id, [])) ->
              [floc $startpos $endpos, binder_of_id id, false, None]
      | _ ->  [floc $startpos $endpos, None, false, Some $1] }
| LEFTPAR GHOST ty RIGHTPAR
    { match $3 with
      | PTtyapp (Qident {id_str="ref"}, [PTtyapp (Qident id, [])]) ->
              [floc $startpos $endpos, binder_of_id (set_ref id), true, None]
      | PTtyapp (Qident id, []) ->
              [floc $startpos $endpos, binder_of_id id, true, None]
      | _ ->  [floc $startpos $endpos, None, true, Some $3] }
| LEFTPAR binder_vars_rest RIGHTPAR
    { match snd $2 with [l,i] -> [l, set_ref_opt l (fst $2) i, false, None]
      | _ -> error_loc (floc $startpos($3) $endpos($3)) }
| LEFTPAR GHOST binder_vars_rest RIGHTPAR
    { match snd $3 with [l,i] -> [l, set_ref_opt l (fst $3) i, true, None]
      | _ -> error_loc (floc $startpos($4) $endpos($4)) }
| LEFTPAR binder_vars cast RIGHTPAR
    { let r = fst $2 in let ty = if r then PTref [$3] else $3 in
      List.map (fun (l,i) -> l, set_ref_opt l r i, false, Some ty) (snd $2) }
| LEFTPAR GHOST binder_vars cast RIGHTPAR
    { let r = fst $3 in let ty = if r then PTref [$4] else $4 in
      List.map (fun (l,i) -> l, set_ref_opt l r i, true, Some ty) (snd $3) }

binder_vars:
| binder_vars_head  { fst $1, match snd $1 with
                        | [] -> raise Error
                        | bl -> List.rev bl }
| binder_vars_rest  { $1 }

binder_vars_rest:
| binder_vars_head attr+ binder_var*
    { let l2 = floc $startpos($2) $endpos($2) in
      fst $1, List.rev_append (match snd $1 with
        | (l, Some id) :: bl ->
            (Loc.join l l2, Some (add_attr id $2)) :: bl
        | _ -> error_loc l2) $3 }
| binder_vars_head special_binder binder_var*
    { fst $1, List.rev_append (snd $1) ($2 :: $3) }
| special_binder binder_var*
    { false, $1 :: $2 }

binder_vars_head:
| ty {
    let of_id id = id.id_loc, binder_of_id id in
    let push acc = function
      | PTtyapp (Qident id, []) -> of_id id :: acc
      | _ -> raise Error in
    match $1 with
      | PTtyapp (Qident {id_str = "ref"}, l) ->
          true, List.fold_left push [] l
      | PTtyapp (Qident id, l) ->
          false, List.fold_left push [of_id id] l
      | _ -> raise Error }

binder_var:
| attrs(lident_nq)      { floc $startpos $endpos, Some $1 }
| special_binder        { $1 }

special_binder:
| UNDERSCORE            { floc $startpos $endpos, None }
| AMP attrs(lident_nq)  { floc $startpos $endpos, Some (set_ref $2) }

(* Logical terms *)

mk_term(X): d = X { mk_term d $startpos $endpos }

term:
| single_term %prec below_COMMA   { $1 }
| single_term COMMA term_
    { mk_term (Ttuple ($1::$3)) $startpos $endpos }

term_:
| single_term %prec below_COMMA   { [$1] }
| single_term COMMA term_         { $1::$3 }

single_term: t = mk_term(single_term_) { t }

single_term_:
| term_arg_
    { match $1 with (* break the infix relation chain *)
      | Tinfix (l,o,r) -> Tinnfix (l,o,r)
      | Tbinop (l,o,r) -> Tbinnop (l,o,r)
      | d -> d }
| NOT single_term
    { Tnot $2 }
| OLD single_term
    { Tat ($2, mk_id Dexpr.old_label $startpos($1) $endpos($1)) }
| single_term AT uident
    { Tat ($1, $3) }
| prefix_op single_term %prec prec_prefix_op
    { Tidapp (Qident $1, [$2]) }
| MINUS INTEGER
    { Tconst (Number.ConstInt (mk_int_const true $2)) }
| MINUS REAL
    { Tconst (Number.ConstReal (mk_real_const true $2)) }
| l = single_term ; o = bin_op ; r = single_term
    { Tbinop (l, o, r) }
| l = single_term ; o = infix_op_1 ; r = single_term
    { Tinfix (l, o, r) }
| l = single_term ; o = infix_op_234 ; r = single_term
    { Tidapp (Qident o, [l; r]) }
| term_arg located(term_arg)+
    { let join f (a,_,e) = mk_term (Tapply (f,a)) $startpos e in
      (List.fold_left join $1 $2).term_desc }
| IF term THEN term ELSE term
    { Tif ($2, $4, $6) }
| LET pattern EQUAL term IN term
    { let re_pat pat d = { pat with pat_desc = d } in
      let cast t ty = { t with term_desc = Tcast (t,ty) } in
      let rec unfold d p = match p.pat_desc with
        | Pparen p | Pscope (_,p) -> unfold d p
        | Pcast (p,ty) -> unfold (cast d ty) p
        | Ptuple [] -> unfold (cast d (PTtuple [])) (re_pat p Pwild)
        | Pvar id -> Tlet (id, d, $6)
        | Pwild -> Tlet (id_anonymous p.pat_loc, d, $6)
        | _ -> Tcase (d, [$2, $6]) in
      unfold $4 $2 }
| LET attrs(lident_op_nq) EQUAL term IN term
    { Tlet ($2, $4, $6) }
| LET attrs(lident_nq) mk_term(lam_defn) IN term
    { Tlet ($2, $3, $5) }
| LET attrs(lident_op_nq) mk_term(lam_defn) IN term
    { Tlet ($2, $3, $5) }
| MATCH term WITH match_cases(term) END
    { Tcase ($2, $4) }
| quant comma_list1(quant_vars) triggers DOT term
    { let l = List.concat $2 in
      Tquant ($1, l, $3, $5) }
| FUN binders ARROW term
    { Tquant (Dterm.DTlambda, $2, [], $4) }
| EPSILON eps_var DOT term
    { Teps ($2, $4) }
| attr single_term %prec prec_attr
    { Tattr ($1, $2) }
| single_term cast
    { Tcast ($1, $2) }

lam_defn:
| binders EQUAL term  { Tquant (Dterm.DTlambda, $1, [], $3) }

term_arg: mk_term(term_arg_) { $1 }
term_dot: mk_term(term_dot_) { $1 }

term_arg_:
| qualid                    { Tident $1 }
| AMP qualid                { Tasref $2 }
| numeral                   { Tconst $1 }
| TRUE                      { Ttrue }
| FALSE                     { Tfalse }
| o = oppref ; a = term_arg { Tidapp (Qident o, [a]) }
| term_sub_                 { $1 }

term_dot_:
| lqualid                   { Tident $1 }
| o = oppref ; a = term_dot { Tidapp (Qident o, [a]) }
| term_sub_                 { $1 }

term_block_:
| BEGIN term END                                    { $2.term_desc }
| LEFTPAR term RIGHTPAR                             { $2.term_desc }
| BEGIN END                                         { Ttuple [] }
| LEFTPAR RIGHTPAR                                  { Ttuple [] }
| LEFTBRC field_list1(term) RIGHTBRC                { Trecord $2 }
| LEFTBRC term_arg WITH field_list1(term) RIGHTBRC  { Tupdate ($2,$4) }

term_sub_:
| term_block_                                       { $1 }
| uqualid DOT mk_term(term_block_)                  { Tscope ($1, $3) }
| term_dot DOT lqualid_rich                         { Tidapp ($3,[$1]) }
| term_arg LEFTSQ term rightsq
    { Tidapp (get_op $4 $startpos($2) $endpos($2), [$1;$3]) }
| term_arg LEFTSQ term LARROW term rightsq
    { Tidapp (upd_op $6 $startpos($2) $endpos($2), [$1;$3;$5]) }
| term_arg LEFTSQ term DOTDOT term rightsq
    { Tidapp (cut_op $6 $startpos($2) $endpos($2), [$1;$3;$5]) }
| term_arg LEFTSQ term DOTDOT rightsq
    { Tidapp (rcut_op $5 $startpos($2) $endpos($2), [$1;$3]) }
| term_arg LEFTSQ DOTDOT term rightsq
    { Tidapp (lcut_op $5 $startpos($2) $endpos($2), [$1;$4]) }

field_list1(X):
| fl = semicolon_list1(separated_pair(lqualid, EQUAL, X)) { fl }

match_cases(X):
| cl = bar_list1(match_case(X)) { cl }

match_case(X):
| mc = separated_pair(pattern, ARROW, X) { mc }

quant_vars:
| binder_var+ cast? { List.map (fun (l,i) -> l, i, false, $2) $1 }

eps_var:
| attrs(lident) cast { ($1, $2) }

triggers:
| (* epsilon *)                                                         { [] }
| LEFTSQ separated_nonempty_list(BAR,comma_list1(single_term)) RIGHTSQ  { $2 }

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
| INTEGER { Number.ConstInt (mk_int_const false $1) }
| REAL    { Number.ConstReal (mk_real_const false $1) }

(* Program declarations *)

prog_decl:
| VAL ghost kind attrs(lident_rich) mk_expr(fun_decl)
    { Dlet ($4, ghost $2, $3, apply_partial $2 $5) }
| VAL ghost kind sym_binder mk_expr(const_decl)
    { Dlet ($4, ghost $2, $3, apply_partial $2 $5) }
| VAL ghost REF ref_binder mk_expr(const_decl)
    { let rf = mk_expr Eref $startpos($3) $endpos($3) in
      let ee = { $5 with expr_desc = Eapply (rf, $5) } in
      Dlet ($4, ghost $2, Expr.RKnone, apply_partial $2 ee) }
| LET ghost kind attrs(lident_rich) mk_expr(fun_defn)
    { Dlet ($4, ghost $2, $3, apply_partial $2 $5) }
| LET ghost kind sym_binder const_defn
    { Dlet ($4, ghost $2, $3, apply_partial $2 $5) }
| LET ghost REF ref_binder const_defn
    { let rf = mk_expr Eref $startpos($3) $endpos($3) in
      let ee = { $5 with expr_desc = Eapply (rf, $5) } in
      Dlet ($4, ghost $2, Expr.RKnone, apply_partial $2 ee) }
| LET REC with_list1(rec_defn)
    { Drec $3 }
| EXCEPTION attrs(uident_nq)
    { Dexn ($2, PTtuple [], Ity.MaskVisible) }
| EXCEPTION attrs(uident_nq) return
    { Dexn ($2, fst $3, snd $3) }

ghost:
| (* epsilon *) { Regular }
| PARTIAL       { Partial }
| GHOST         { Ghost }
| GHOST PARTIAL
| PARTIAL GHOST { Loc.errorm ~loc:(floc $startpos $endpos)
                    "Ghost functions cannot be partial" }

kind:
| (* epsilon *) { Expr.RKnone }
| FUNCTION      { Expr.RKfunc }
| CONSTANT      { Expr.RKfunc }
| PREDICATE     { Expr.RKpred }
| LEMMA         { Expr.RKlemma }

(* Function definitions *)

rec_defn:
| ghost kind attrs(lident_rich) binders return_opt spec EQUAL spec seq_expr
    { let pat, ty, mask = $5 in
      let spec = apply_return pat (spec_union $6 $8) in
      let id = mk_id return_id $startpos($7) $endpos($7) in
      let e = { $9 with expr_desc = Eoptexn (id, mask, $9) } in
      $3, ghost $1, $2, $4, ty, mask, apply_partial_sp $1 spec, e }

fun_defn:
| binders return_opt spec EQUAL spec seq_expr
    { let pat, ty, mask = $2 in
      let spec = apply_return pat (spec_union $3 $5) in
      let id = mk_id return_id $startpos($4) $endpos($4) in
      let e = { $6 with expr_desc = Eoptexn (id, mask, $6) } in
      Efun ($1, ty, mask, spec, e) }

fun_decl:
| params1 return_opt spec
    { let pat, ty, mask = $2 in
      Eany ($1, Expr.RKnone, ty, mask, apply_return pat $3) }

const_decl:
| return_opt spec
    { let pat, ty, mask = $1 in
      Eany ([], Expr.RKnone, ty, mask, apply_return pat $2) }

const_defn:
| cast EQUAL seq_expr   { { $3 with expr_desc = Ecast ($3, $1) } }
| EQUAL seq_expr        { $2 }

(* Program expressions *)

mk_expr(X): d = X { mk_expr d $startpos $endpos }

seq_expr:
| contract_expr %prec below_SEMI  { $1 }
| contract_expr SEMICOLON         { $1 }
| contract_expr SEMICOLON seq_expr
    { mk_expr (Esequence ($1, $3)) $startpos $endpos }

contract_expr:
| assign_expr %prec prec_no_spec  { $1 }
| assign_expr single_spec spec
    { let d = Efun ([], None, Ity.MaskVisible, spec_union $2 $3, $1) in
      let d = Eattr (ATstr Vc.wb_attr, mk_expr d $startpos $endpos) in
      mk_expr d $startpos $endpos }

assign_expr:
| expr %prec below_LARROW         { $1 }
| expr LARROW expr
    { let loc = floc $startpos $endpos in
      let rec down ll rl = match ll, rl with
        | ({expr_desc = Eident q} as e1)::ll, e2::rl ->
            let e1 = {e1 with expr_desc = Easref q} in
            (e1, None, e2) :: down ll rl
        | {expr_desc = Eidapp (q, [e1])}::ll, e2::rl ->
            (e1, Some q, e2) :: down ll rl
        | {expr_desc = Eidapp (Qident id, [_;_]); expr_loc = loc}::_, _::_ ->
            begin match Ident.sn_decode id.id_str with
              | Ident.SNget _ -> Loc.errorm ~loc
                  "Parallel array assignments are not allowed"
              | _ -> Loc.errorm ~loc
                  "Invalid left expression in an assignment"
            end
        | {expr_loc = loc}::_, _::_ -> Loc.errorm ~loc
            "Invalid left expression in an assignment"
        | [], [] -> []
        | _ -> Loc.errorm ~loc "Invalid parallel assignment" in
      let d = match $1.expr_desc, $3.expr_desc with
        | Eidapp (Qident id, [e1;e2]), _ ->
            begin match Ident.sn_decode id.id_str with
              | Ident.SNget q ->
                  Eidapp (Qident {id with id_str = Ident.op_set q}, [e1;e2;$3])
              | _ -> Loc.errorm ~loc:$1.expr_loc
                  "Invalid left expression in an assignment"
            end
        | Etuple ll, Etuple rl -> Eassign (down ll rl)
        | Etuple _, _ -> Loc.errorm ~loc "Invalid parallel assignment"
        | _, _ -> Eassign (down [$1] [$3]) in
      { expr_desc = d; expr_loc = loc } }

expr:
| single_expr %prec below_COMMA   { $1 }
| single_expr COMMA expr_list1
    { mk_expr (Etuple ($1::$3)) $startpos $endpos }

expr_list1:
| single_expr %prec below_COMMA   { [$1] }
| single_expr COMMA expr_list1    { $1::$3 }

single_expr: e = mk_expr(single_expr_)  { e }

single_expr_:
| expr_arg_
    { match $1 with (* break the infix relation chain *)
      | Einfix (l,o,r) -> Einnfix (l,o,r) | d -> d }
| single_expr AMPAMP single_expr
    { Eand ($1, $3) }
| single_expr BARBAR single_expr
    { Eor ($1, $3) }
| NOT single_expr
    { Enot $2 }
| prefix_op single_expr %prec prec_prefix_op
    { Eidapp (Qident $1, [$2]) }
| MINUS INTEGER
    { Econst (Number.ConstInt (mk_int_const true $2)) }
| MINUS REAL
    { Econst (Number.ConstReal (mk_real_const true $2)) }
| l = single_expr ; o = infix_op_1 ; r = single_expr
    { Einfix (l,o,r) }
| l = single_expr ; o = infix_op_234 ; r = single_expr
    { Eidapp (Qident o, [l;r]) }
| expr_arg located(expr_arg)+
    { let join f (a,_,e) = mk_expr (Eapply (f,a)) $startpos e in
      (List.fold_left join $1 $2).expr_desc }
| IF seq_expr THEN contract_expr ELSE contract_expr
    { Eif ($2, $4, $6) }
| IF seq_expr THEN contract_expr %prec prec_no_else
    { Eif ($2, $4, mk_expr (Etuple []) $startpos $endpos) }
| LET ghost kind let_pattern EQUAL seq_expr IN seq_expr
    { let re_pat pat d = { pat with pat_desc = d } in
      let cast e ty = { e with expr_desc = Ecast (e,ty) } in
      let rec push pat = re_pat pat (match pat.pat_desc with
        | Ptuple (p::pl) -> Ptuple (push p :: pl)
        | Pcast (p,ty) -> Pcast (push p, ty)
        | Pas (p,v,g) -> Pas (push p, v, g)
        | Por (p,q) -> Por (push p, q)
        | _ -> Pghost pat) in
      let pat = if ghost $2 then push $4 else $4 in
      let rec unfold gh d p = match p.pat_desc with
        | Pparen p | Pscope (_,p) -> unfold gh d p
        | Pghost p -> unfold true d p
        | Pcast (p,ty) -> unfold gh (cast d ty) p
        | Ptuple [] -> unfold gh (cast d (PTtuple [])) (re_pat p Pwild)
        | Pvar id -> Elet (id, gh, $3, d, $8)
        | Pwild -> Elet (id_anonymous p.pat_loc, gh, $3, d, $8)
        | _ when $3 = Expr.RKnone -> Ematch (d, [pat, $8], [])
        | _ -> Loc.errorm ~loc:(floc $startpos($3) $endpos($3))
            "illegal kind qualifier" in
      unfold false (apply_partial $2 $6) pat }
| LET ghost kind attrs(lident_op_nq) const_defn IN seq_expr
    { Elet ($4, ghost $2, $3, apply_partial $2 $5, $7) }
| LET ghost kind attrs(lident_nq) mk_expr(fun_defn) IN seq_expr
    { Elet ($4, ghost $2, $3, apply_partial $2 $5, $7) }
| LET ghost kind attrs(lident_op_nq) mk_expr(fun_defn) IN seq_expr
    { Elet ($4, ghost $2, $3, apply_partial $2 $5, $7) }
| LET ghost REF ref_binder const_defn IN seq_expr
    { let rf = mk_expr Eref $startpos($3) $endpos($3) in
      let ee = { $5 with expr_desc = Eapply (rf, $5) } in
      Elet ($4, ghost $2, Expr.RKnone, apply_partial $2 ee, $7) }
| LET REC with_list1(rec_defn) IN seq_expr
    { Erec ($3, $5) }
| FUN binders spec ARROW spec seq_expr
    { let id = mk_id return_id $startpos($4) $endpos($4) in
      let e = { $6 with expr_desc = Eoptexn (id, Ity.MaskVisible, $6) } in
      Efun ($2, None, Ity.MaskVisible, spec_union $3 $5, e) }
| ANY return_named spec
    { let pat, ty, mask = $2 in
      let loc = floc $startpos $endpos in
      let spec = apply_return pat $3 in
      if spec.sp_writes <> [] then Loc.errorm ~loc
        "this expression should not produce side effects";
      if spec.sp_xpost <> [] then Loc.errorm ~loc
        "this expression should not raise exceptions";
      if spec.sp_alias <> [] then Loc.errorm ~loc
        "this expression cannot have alias restrictions";
      if spec.sp_diverge || spec.sp_partial then Loc.errorm ~loc
        "this expression must terminate";
      let pre = pre_of_any loc ty spec.sp_post in
      let spec = { spec with sp_pre = spec.sp_pre @ pre } in
      Eany ([], Expr.RKnone, Some ty, mask, spec) }
| VAL ghost kind attrs(lident_rich) mk_expr(fun_decl) IN seq_expr
    { Elet ($4, ghost $2, $3, apply_partial $2 $5, $7) }
| VAL ghost kind sym_binder mk_expr(const_decl) IN seq_expr
    { Elet ($4, ghost $2, $3, apply_partial $2 $5, $7) }
| VAL ghost REF ref_binder mk_expr(const_decl) IN seq_expr
    { let rf = mk_expr Eref $startpos($3) $endpos($3) in
      let ee = { $5 with expr_desc = Eapply (rf, $5) } in
      Elet ($4, ghost $2, Expr.RKnone, apply_partial $2 ee, $7) }
| MATCH seq_expr WITH ext_match_cases END
    { let bl, xl = $4 in Ematch ($2, bl, xl) }
| EXCEPTION attrs(uident) IN seq_expr
    { Eexn ($2, PTtuple [], Ity.MaskVisible, $4) }
| EXCEPTION attrs(uident) return IN seq_expr
    { Eexn ($2, fst $3, snd $3, $5) }
| LABEL id = attrs(uident) IN e = seq_expr
    { let cont e =
        let id = { id with id_str = id.id_str ^ continue_id } in
        { e with expr_desc = Eoptexn (id, Ity.MaskVisible, e) } in
      let rec over_loop e = { e with expr_desc = over_loop_desc e }
      and over_loop_desc e = match e.expr_desc with
        | Escope (q, e1) -> Escope (q, over_loop e1)
        | Eattr (l, e1) -> Eattr (l, over_loop e1)
        | Ecast (e1, t) -> Ecast (over_loop e1, t)
        | Eghost e1 -> Eghost (over_loop e1)
        | Esequence (e1, e2) -> Esequence (over_loop e1, e2)
        | Eoptexn (id, mask, e1) -> Eoptexn (id, mask, over_loop e1)
        | Ewhile (e1, inv, var, e2) ->
            let e = { e with expr_desc = Ewhile (e1, inv, var, cont e2) } in
            let id = { id with id_str = id.id_str ^ break_id } in
            Eoptexn (id, Ity.MaskVisible, e)
        | Efor (i, ef, dir, et, inv, e1) ->
            let e = { e with expr_desc = Efor (i,ef,dir,et,inv,cont e1) } in
            let id = { id with id_str = id.id_str ^ break_id } in
            Eoptexn (id, Ity.MaskVisible, e)
        | d -> d in
      Elabel (id, over_loop e) }
| WHILE seq_expr DO loop_annotation loop_body DONE
    { let id_b = mk_id break_id $startpos($3) $endpos($3) in
      let id_c = mk_id continue_id $startpos($3) $endpos($3) in
      let e = { $5 with expr_desc = Eoptexn (id_c, Ity.MaskVisible, $5) } in
      let e = mk_expr (Ewhile ($2, fst $4, snd $4, e)) $startpos $endpos in
      Eoptexn (id_b, Ity.MaskVisible, e) }
| FOR var_binder EQUAL seq_expr for_dir seq_expr DO invariant* loop_body DONE
    { let id_b = mk_id break_id $startpos($7) $endpos($7) in
      let id_c = mk_id continue_id $startpos($7) $endpos($7) in
      let e = { $9 with expr_desc = Eoptexn (id_c, Ity.MaskVisible, $9) } in
      let e = mk_expr (Efor ($2, $4, $5, $6, $8, e)) $startpos $endpos in
      Eoptexn (id_b, Ity.MaskVisible, e) }
| ABSURD
    { Eabsurd }
| RAISE uqualid expr_arg?
    { Eraise ($2, $3) }
| RAISE LEFTPAR uqualid expr_arg? RIGHTPAR
    { Eraise ($3, $4) }
| RETURN ioption(contract_expr)
    { let id = mk_id return_id $startpos($1) $endpos($1) in
      Eraise (Qident id, $2) }
| BREAK ioption(uident)
    { let id = match $2 with
        | Some id -> { id with id_str = id.id_str ^ break_id }
        | None -> mk_id break_id $startpos($1) $endpos($1) in
      Eraise (Qident id, None) }
| CONTINUE ioption(uident)
    { let id = match $2 with
        | Some id -> { id with id_str = id.id_str ^ continue_id }
        | None -> mk_id continue_id $startpos($1) $endpos($1) in
      Eraise (Qident id, None) }
| TRY seq_expr WITH bar_list1(exn_handler) END
    { Ematch ($2, [], $4) }
| GHOST single_expr
    { Eghost $2 }
| assertion_kind LEFTBRC term RIGHTBRC
    { Eassert ($1, $3) }
| attr single_expr %prec prec_attr
    { Eattr ($1, $2) }
| single_expr cast
    { Ecast ($1, $2) }

expr_arg: e = mk_expr(expr_arg_) { e }
expr_dot: e = mk_expr(expr_dot_) { e }

expr_arg_:
| qualid                    { Eident $1 }
| AMP qualid                { Easref $2 }
| numeral                   { Econst $1 }
| TRUE                      { Etrue }
| FALSE                     { Efalse }
| o = oppref ; a = expr_arg { Eidapp (Qident o, [a]) }
| expr_sub_                 { $1 }

expr_dot_:
| lqualid                   { Eident $1 }
| o = oppref ; a = expr_dot { Eidapp (Qident o, [a]) }
| expr_sub_                 { $1 }

expr_block_:
| BEGIN single_spec spec seq_expr END
    { Efun ([], None, Ity.MaskVisible, spec_union $2 $3, $4) }
| BEGIN single_spec spec END
    { let e = mk_expr (Etuple []) $startpos $endpos in
      Efun ([], None, Ity.MaskVisible, spec_union $2 $3, e) }
| BEGIN seq_expr END                                { $2.expr_desc }
| LEFTPAR seq_expr RIGHTPAR                         { $2.expr_desc }
| BEGIN END                                         { Etuple [] }
| LEFTPAR RIGHTPAR                                  { Etuple [] }
| LEFTBRC field_list1(expr) RIGHTBRC                { Erecord $2 }
| LEFTBRC expr_arg WITH field_list1(expr) RIGHTBRC  { Eupdate ($2, $4) }

expr_pure_:
| LEFTBRC qualid RIGHTBRC                           { Eidpur $2 }
| uqualid DOT LEFTBRC ident RIGHTBRC                { Eidpur (Qdot ($1, $4)) }

expr_sub_:
| expr_block_                                       { $1 }
| expr_pure_                                        { $1 }
| uqualid DOT mk_expr(expr_block_)                  { Escope ($1, $3) }
| expr_dot DOT mk_expr(expr_pure_)                  { Eapply ($3, $1) }
| expr_dot DOT lqualid_rich                         { Eidapp ($3, [$1]) }
| PURE LEFTBRC term RIGHTBRC                        { Epure $3 }
| expr_arg LEFTSQ expr rightsq
    { Eidapp (get_op $4 $startpos($2) $endpos($2), [$1;$3]) }
| expr_arg LEFTSQ expr LARROW expr rightsq
    { Eidapp (upd_op $6 $startpos($2) $endpos($2), [$1;$3;$5]) }
| expr_arg LEFTSQ expr DOTDOT expr rightsq
    { Eidapp (cut_op $6 $startpos($2) $endpos($2), [$1;$3;$5]) }
| expr_arg LEFTSQ expr DOTDOT rightsq
    { Eidapp (rcut_op $5 $startpos($2) $endpos($2), [$1;$3]) }
| expr_arg LEFTSQ DOTDOT expr rightsq
    { Eidapp (lcut_op $5 $startpos($2) $endpos($2), [$1;$4]) }

loop_body:
| (* epsilon *)   { mk_expr (Etuple []) $startpos $endpos }
| seq_expr        { $1 }

loop_annotation:
| (* epsilon *)
    { [], [] }
| invariant loop_annotation
    { let inv, var = $2 in $1 :: inv, var }
| variant loop_annotation
    { let inv, var = $2 in inv, variant_union $1 var }

ext_match_cases:
| ioption(BAR) ext_match_cases1  { $2 }

ext_match_cases1:
| match_case(seq_expr)  ext_match_cases0  { let bl,xl = $2 in $1::bl, xl }
| EXCEPTION exn_handler ext_match_cases0  { let bl,xl = $3 in bl, $2::xl }

ext_match_cases0:
| (* epsilon *)         { [], [] }
| BAR ext_match_cases1  { $2 }

exn_handler:
| uqualid pat_arg? ARROW seq_expr { $1, $2, $4 }

assertion_kind:
| ASSERT  { Expr.Assert }
| ASSUME  { Expr.Assume }
| CHECK   { Expr.Check }

for_dir:
| TO      { Expr.To }
| DOWNTO  { Expr.DownTo }

(* Specification *)

spec:
| (* epsilon *) %prec prec_no_spec  { empty_spec }
| single_spec spec                  { spec_union $1 $2 }

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
| WRITES LEFTBRC comma_list0(single_term) RIGHTBRC
    { { empty_spec with sp_writes = $3; sp_checkrw = true } }
| ALIAS LEFTBRC comma_list0(alias) RIGHTBRC
    { { empty_spec with sp_alias = $3; sp_checkrw = true } }
| RAISES LEFTBRC comma_list1(xsymbol) RIGHTBRC
    { { empty_spec with sp_xpost = [floc $startpos($3) $endpos($3), $3] } }
| DIVERGES
    { { empty_spec with sp_diverge = true } }
| variant
    { { empty_spec with sp_variant = $1 } }

alias:
| term WITH term  { $1, $3 }

ensures:
| term
    { let id = mk_id "result" $startpos $endpos in
      [mk_pat (Pvar id) $startpos $endpos, $1] }

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
| single_term preceded(WITH,lqualid)?  { $1, $2 }

return_opt:
| (* epsilon *)       { mk_pat Pwild $startpos $endpos, None, Ity.MaskVisible }
| COLON return_named  { let pat, ty, mask = $2 in pat, Some ty, mask }

return_named:
| LEFTPAR ret_cast RIGHTPAR
    { $2 }
| LEFTPAR comma_list2(ret_cast) RIGHTPAR
    { mk_pat (Ptuple (List.map (fun (pat,_,_) -> pat) $2)) $startpos $endpos,
      PTtuple (List.map (fun (_,ty,_) -> ty) $2),
      Ity.MaskTuple (List.map (fun (_,_,mask) -> mask) $2) }
| return
    { let ty, mask = $1 in mk_pat Pwild $startpos $endpos, ty, mask }

ret_cast:
|       ret_ident cast  { $1, $2, Ity.MaskVisible }
| GHOST ret_ident cast  { $2, $3, Ity.MaskGhost }

ret_ident:
| id = attrs(lident_nq)
    { let ats = ATstr Dterm.attr_w_unused_var_no :: id.id_ats in
      mk_pat (Pvar {id with id_ats = ats}) $startpos $endpos }
| UNDERSCORE
    { mk_pat Pwild $startpos $endpos }

return:
|               ty            { $1, Ity.MaskVisible }
|         GHOST ty            { $2, Ity.MaskGhost }
| LEFTPAR GHOST ty RIGHTPAR   { $3, Ity.MaskGhost }
| LEFTPAR ret_ghost RIGHTPAR  { PTtuple (fst $2), Ity.MaskTuple (snd $2) }

ret_ghost:
|       ty COMMA GHOST ty     { [$1; $4], [Ity.MaskVisible; Ity.MaskGhost] }
|       ty COMMA ret_ghost    { $1::fst $3, Ity.MaskVisible::snd $3 }
| GHOST ty COMMA ret_rest     { $2::fst $4, Ity.MaskGhost::snd $4 }

ret_rest:
|       ty COMMA ret_rest     { $1::fst $3, Ity.MaskVisible::snd $3 }
| GHOST ty COMMA ret_rest     { $2::fst $4, Ity.MaskGhost::snd $4 }
|       ty                    { [$1], [Ity.MaskVisible] }
| GHOST ty                    { [$2], [Ity.MaskGhost] }

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
| GHOST mk_pat(pat_uni_)                { Pghost $2 }
| mk_pat(pat_uni_) AS boption(GHOST) var_binder
                                        { Pas ($1,$4,$3) }
| mk_pat(pat_uni_) cast                 { Pcast ($1,$2) }

pat_arg_:
| UNDERSCORE                            { Pwild }
| var_binder                            { Pvar $1 }
| uqualid                               { Papp ($1,[]) }
| uqualid DOT mk_pat(pat_block_)        { Pscope ($1,$3) }
| pat_block_                            { $1 }

pat_block_:
| LEFTPAR RIGHTPAR                      { Ptuple [] }
| LEFTPAR pattern RIGHTPAR              { Pparen $2 }
| LEFTBRC field_list1(pattern) RIGHTBRC { Prec $2 }

(* let-patterns cannot start with "ghost" *)

let_pattern: mk_pat(let_pattern_) { $1 }

let_pattern_:
| let_pat_conj_                         { $1 }
| mk_pat(let_pat_conj_) BAR pattern     { Por ($1,$3) }

let_pat_conj_:
| let_pat_uni_                          { $1 }
| mk_pat(let_pat_uni_) COMMA comma_list1(mk_pat(pat_uni_))
                                        { Ptuple ($1::$3) }

let_pat_uni_:
| pat_arg_                              { $1 }
| uqualid pat_arg+                      { Papp ($1,$2) }
| mk_pat(let_pat_uni_) AS boption(GHOST) var_binder
                                        { Pas ($1,$4,$3) }
| mk_pat(let_pat_uni_) cast             { Pcast ($1,$2) }

(* One-variable binders *)

sym_binder: (* let and val without parameters *)
|     attrs(lident_rich)  { $1 }
| AMP attrs(lident_nq)    { set_ref $2 }

var_binder: (* pattern variables *)
|     attrs(lident_nq)    { $1 }
| AMP attrs(lident_nq)    { set_ref $2 }

ref_binder: (* let ref and val ref *)
|     attrs(lident_nq)    { set_ref $1 }
| AMP attrs(lident_nq)    { double_ref $2 }

(* Qualified idents *)

qualid:
| ident                   { Qident $1 }
| uqualid DOT ident       { Qdot ($1, $3) }

uqualid:
| uident                  { Qident $1 }
| uqualid DOT uident      { Qdot ($1, $3) }

lqualid:
| lident                  { Qident $1 }
| uqualid DOT lident      { Qdot ($1, $3) }

lqualid_rich:
| lident                  { Qident $1 }
| lident_op               { Qident $1 }
| uqualid DOT lident      { Qdot ($1, $3) }
| uqualid DOT lident_op   { Qdot ($1, $3) }

tqualid:
| uident                  { Qident $1 }
| squalid DOT uident      { Qdot ($1, $3) }

squalid:
| sident                  { Qident $1 }
| squalid DOT sident      { Qdot ($1, $3) }

(* Idents *)

ident:
| uident          { $1 }
| lident          { $1 }
| lident_op       { $1 }

ident_nq:
| uident_nq       { $1 }
| lident_nq       { $1 }
| lident_op_nq    { $1 }

lident_rich:
| lident_nq       { $1 }
| lident_op_nq    { $1 }

uident:
| UIDENT          { mk_id $1 $startpos $endpos }
| CORE_UIDENT     { mk_id $1 $startpos $endpos }

uident_nq:
| UIDENT          { mk_id $1 $startpos $endpos }
| CORE_UIDENT     { let loc = floc $startpos($1) $endpos($1) in
                    Loc.errorm ~loc core_ident_error $1 }

lident:
| LIDENT          { mk_id $1 $startpos $endpos }
| lident_keyword  { mk_id $1 $startpos $endpos }
| CORE_LIDENT     { mk_id $1 $startpos $endpos }
| REF             { mk_id "ref" $startpos $endpos }
(* we don't put REF in lident_keyword, because we do not
   want it in lident_nq, not even with an error message.
   This avoids a conflict in "let ref x = ...". *)

lident_nq:
| LIDENT          { mk_id $1 $startpos $endpos }
| lident_keyword  { mk_id $1 $startpos $endpos }
| CORE_LIDENT     { let loc = floc $startpos($1) $endpos($1) in
                    Loc.errorm ~loc core_ident_error $1 }

lident_keyword:
| RANGE           { "range" }
| FLOAT           { "float" }

sident:
| lident          { $1 }
| uident          { $1 }
| STRING          { mk_id $1 $startpos $endpos }
(* TODO: we can add all keywords and save on quotes *)

quote_lident:
| QUOTE_LIDENT    { mk_id $1 $startpos $endpos }

(* Symbolic operation names *)

lident_op:
| LEFTPAR lident_op_str RIGHTPAR
    { mk_id $2 $startpos($2) $endpos($2) }
| LEFTPAR lident_op_str RIGHTPAR_USCORE
    { mk_id ($2^$3) $startpos $endpos }
| LEFTPAR lident_op_str RIGHTPAR_QUOTE
    { mk_id ($2^$3) $startpos $endpos }

lident_op_nq:
| LEFTPAR lident_op_str RIGHTPAR
    { mk_id $2 $startpos($2) $endpos($2) }
| LEFTPAR lident_op_str RIGHTPAR_USCORE
    { mk_id ($2^$3) $startpos $endpos }
| LEFTPAR lident_op_str RIGHTPAR_QUOTE
    { let loc = floc $startpos $endpos in
      Loc.errorm ~loc "Symbol (%s)%s cannot be user-defined" $2 $3 }

lident_op_str:
| op_symbol                         { Ident.op_infix $1 }
| op_symbol UNDERSCORE              { Ident.op_prefix $1 }
| MINUS     UNDERSCORE              { Ident.op_prefix "-" }
| EQUAL                             { Ident.op_infix "=" }
| MINUS                             { Ident.op_infix "-" }
| OPPREF UNDERSCORE?                { Ident.op_prefix $1 }
| LEFTSQ rightsq                    { Ident.op_get $2 }
| LEFTSQ rightsq LARROW             { Ident.op_set $2 }
| LEFTSQ LARROW rightsq             { Ident.op_update $3 }
| LEFTSQ DOTDOT rightsq             { Ident.op_cut $3 }
| LEFTSQ UNDERSCORE DOTDOT rightsq  { Ident.op_rcut $4 }
| LEFTSQ DOTDOT UNDERSCORE rightsq  { Ident.op_lcut $4 }

rightsq:
| RIGHTSQ         { "" }
| RIGHTSQ_QUOTE   { $1 }

op_symbol:
| OP1 { $1 }
| OP2 { $1 }
| OP3 { $1 }
| OP4 { $1 }
| LT  { "<" }
| GT  { ">" }

%inline oppref:
| o = OPPREF { mk_id (Ident.op_prefix o)  $startpos $endpos }

prefix_op:
| op_symbol { mk_id (Ident.op_prefix $1)  $startpos $endpos }
| MINUS     { mk_id (Ident.op_prefix "-") $startpos $endpos }

%inline infix_op_1:
| o = OP1   { mk_id (Ident.op_infix o)    $startpos $endpos }
| EQUAL     { mk_id (Ident.op_infix "=")  $startpos $endpos }
| LTGT      { mk_id (Ident.op_infix "<>") $startpos $endpos }
| LT        { mk_id (Ident.op_infix "<")  $startpos $endpos }
| GT        { mk_id (Ident.op_infix ">")  $startpos $endpos }

%inline infix_op_234:
| o = OP2   { mk_id (Ident.op_infix o)    $startpos $endpos }
| o = OP3   { mk_id (Ident.op_infix o)    $startpos $endpos }
| o = OP4   { mk_id (Ident.op_infix o)    $startpos $endpos }
| MINUS     { mk_id (Ident.op_infix "-")  $startpos $endpos }

(* Attributes and position markers *)

attrs(X): X attr* { add_attr $1 $2 }

attr:
| ATTRIBUTE { ATstr (Ident.create_attribute $1) }
| POSITION  { ATpos $1 }

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

(* Parsing of a list of qualified identifiers for the ITP *)

qualid_eof:
| qualid EOF { $1 }

qualid_comma_list_eof:
| comma_list1(qualid) EOF { $1 }

ident_comma_list_eof:
| comma_list1(ident) EOF { $1 }

term_comma_list_eof:
| comma_list1(single_term) EOF { $1 }
(* we use single_term to avoid conflict with tuples, that
   do not need parentheses *)
