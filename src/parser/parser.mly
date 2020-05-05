(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

%{
  open Ptree

  let floc s e = Loc.extract (s,e)

  let add_attr id l = (* id.id_ats is usually nil *)
    { id with id_ats = List.rev_append id.id_ats l }

  let id_anonymous loc = { id_str = "_"; id_ats = []; id_loc = loc }

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
      | Efun (_::_ as bl, op, p, m, s, ex) ->
          Efun (bl, op, p, m, apply_partial_sp part s, ex)
      | Eany (_::_ as pl, rsk, op, p,  m, s) ->
          Eany (pl, rsk, op, p, m, apply_partial_sp part s)
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
    | Error -> Format.fprintf fmt "syntax error %s" (Parser_messages.message 1)
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

  let name_term id_opt def t =
    let name = Opt.fold (fun _ id -> id.id_str) def id_opt in
    let attr = ATstr (Ident.create_attribute ("hyp_name:" ^ name)) in
    { term_loc = t.term_loc; term_desc = Tattr (attr, t) }

  let re_pat pat d = { pat with pat_desc = d }

  let rec simplify_let_pattern ?loc kind d pat e =
    let cast e ty = { e with expr_desc = Ecast (e,ty) } in
    let rec unfold gh d p = match p.pat_desc with
      | Pparen p | Pscope (_,p) -> unfold gh d p
      | Pghost p -> unfold true d p
      | Pcast (p,ty) -> unfold gh (cast d ty) p
      | Ptuple [] -> unfold gh (cast d (PTtuple [])) (re_pat p Pwild)
      | Pvar id -> Elet (id, gh, kind, d, e)
      | Pwild -> Elet (id_anonymous p.pat_loc, gh, kind, d, e)
      | _ when kind = Expr.RKnone -> Ematch (d, [pat, e], [])
      | _ -> Loc.errorm ?loc "illegal kind qualifier" in
    unfold false d pat

%}

(* Tokens *)

%token <string> LIDENT CORE_LIDENT UIDENT CORE_UIDENT
%token <Number.int_constant> INTEGER
%token <string> OP1 OP2 OP3 OP4 OPPREF
%token <Number.real_constant> REAL
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

%start <Ptree.term> term_eof
%start <Ptree.qualid> qualid_eof
%start <Ptree.qualid list> qualid_comma_list_eof
%start <Ptree.term list> term_comma_list_eof
%start <Ptree.ident list> ident_comma_list_eof

%%

(* parsing of a single term or a single decl *)

term_eof:
| term EOF { $1 }

(* Theory declarations *)

%public pure_decl:
| TYPE with_list1(type_decl)                { Dtype $2 }
| CONSTANT  constant_decl                   { Dlogic [$2] }
| FUNCTION  function_decl  with_logic_decl* { Dlogic ($2::$3) }
| PREDICATE predicate_decl with_logic_decl* { Dlogic ($2::$3) }
| INDUCTIVE   with_list1(inductive_decl)    { Dind (Decl.Ind, $2) }
| COINDUCTIVE with_list1(inductive_decl)    { Dind (Decl.Coind, $2) }
| AXIOM attrs(ident_nq) COLON term          { Dprop (Decl.Paxiom, { $2 with id_ats = (Ptree.ATstr Ident.useraxiom_attr)::$2.id_ats; }, $4) }
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
(* other rules arr defined in mlw_parser *)

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
| INTEGER       { $1.Number.il_int }
| MINUS INTEGER { BigInt.minus ($2.Number.il_int) }

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

%public binders: binder+ { List.concat $1 }

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
| minus_numeral
    { Tconst $1 }
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
    { let cast t ty = { t with term_desc = Tcast (t,ty) } in
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
| EPSILON
    { Loc.errorm "Epsilon terms are currently not supported in WhyML" }
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
| STRING                    { Tconst (Constant.ConstStr $1) }
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

minus_numeral:
| MINUS INTEGER { Constant.(ConstInt (Number.neg_int $2)) }
| MINUS REAL    { Constant.(ConstReal (Number.neg_real $2))}

numeral:
| INTEGER { Constant.ConstInt $1 }
| REAL    { Constant.ConstReal $1 }

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
      $3, ghost $1, $2, $4, ty, pat, mask, apply_partial_sp $1 spec, e }

fun_defn:
| binders return_opt spec EQUAL spec seq_expr
    { let pat, ty, mask = $2 in
      let spec = apply_return pat (spec_union $3 $5) in
      let id = mk_id return_id $startpos($4) $endpos($4) in
      let e = { $6 with expr_desc = Eoptexn (id, mask, $6) } in
      Efun ($1, ty, pat, mask, spec, e) }

fun_decl:
| params1 return_opt spec
    { let pat, ty, mask = $2 in
      Eany ($1, Expr.RKnone, ty, pat, mask, apply_return pat $3) }

const_decl:
| return_opt spec
    { let pat, ty, mask = $1 in
      Eany ([], Expr.RKnone, ty, pat, mask, apply_return pat $2) }

const_defn:
| cast EQUAL seq_expr   { { $3 with expr_desc = Ecast ($3, $1) } }
| EQUAL seq_expr        { $2 }


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

%public qualid:
| ident                   { Qident $1 }
| uqualid DOT ident       { Qdot ($1, $3) }

%public uqualid:
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

%public tqualid:
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

%public uident:
| UIDENT          { mk_id $1 $startpos $endpos }
| CORE_UIDENT     { mk_id $1 $startpos $endpos }

%public uident_nq:
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

%public sident:
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

%public %inline infix_op_234:
| o = OP2   { mk_id (Ident.op_infix o)    $startpos $endpos }
| o = OP3   { mk_id (Ident.op_infix o)    $startpos $endpos }
| o = OP4   { mk_id (Ident.op_infix o)    $startpos $endpos }
| MINUS     { mk_id (Ident.op_infix "-")  $startpos $endpos }

(* Attributes and position markers *)

%public attrs(X): X attr* { add_attr $1 $2 }

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

%public comma_list1(X):
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
