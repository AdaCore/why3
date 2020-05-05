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

%}

(* Additional tokens *)


(* Additional entry points *)

%start <Pmodule.pmodule Wstdlib.Mstr.t> mlw_file
%start <Ptree.decl> decl_eof


%%

decl_eof:
| pure_decl EOF { $1 }
| prog_decl EOF { $1 }

(* Modules and scopes *)

mlw_file:
| EOF
| mlw_module mlw_module_no_decl* EOF
    { Typing.close_file () }
| module_decl module_decl_no_head* EOF
    { let loc = floc $startpos($3) $endpos($3) in
      Typing.close_module loc; Typing.close_file () }

mlw_module:
| module_head module_decl_no_head* END
    { Typing.close_module (floc $startpos($3) $endpos($3)) }

module_head:
| THEORY attrs(uident_nq)  { Typing.open_module $2 }
| MODULE attrs(uident_nq)  { Typing.open_module $2 }

scope_head:
| SCOPE boption(IMPORT) attrs(uident_nq)
    { Typing.open_scope (floc $startpos $endpos) $3; $2 }

module_decl:
| scope_head module_decl* END
    { Typing.close_scope (floc $startpos($1) $endpos($1)) ~import:$1 }
| IMPORT uqualid
    { Typing.add_decl (floc $startpos $endpos) (Dimport($2)) }
| d = pure_decl | d = prog_decl | d = meta_decl
    { Typing.add_decl (floc $startpos $endpos) d;
      add_record_projections d
    }
| use_clone { () }

(* Do not open inside another module *)

mlw_module_no_decl:
| SCOPE | IMPORT | USE | CLONE | pure_decl | prog_decl | meta_decl
   { let loc = floc $startpos $endpos in
     Loc.errorm ~loc "trying to open a module inside another module" }
| mlw_module
   { $1 }

module_decl_no_head:
| THEORY | MODULE
   { let loc = floc $startpos $endpos in
     Loc.errorm ~loc "trying to open a module inside another module" }
| module_decl
   { $1 }


(* Use and clone *)

use_clone:
| USE EXPORT tqualid
    { let loc = floc $startpos $endpos in
      let decl = Ptree.Duseexport $3 in
      Typing.add_decl loc decl
    }
| CLONE EXPORT tqualid clone_subst
    { let loc = floc $startpos $endpos in
      let decl = Ptree.Dcloneexport($3,$4) in
      Typing.add_decl loc decl
    }
| USE boption(IMPORT) m_as_list = comma_list1(use_as)
    { let loc = floc $startpos $endpos in
      let exists_as = List.exists (fun (_, q) -> q <> None) m_as_list in
      let import = $2 in
      if import && not exists_as then Warning.emit ~loc
        "the keyword `import' is redundant here and can be omitted";
      let decl = Ptree.Duseimport(loc,import,m_as_list) in
      Typing.add_decl loc decl
    }
| CLONE boption(IMPORT) tqualid option(preceded(AS, uident)) clone_subst
    { let loc = floc $startpos $endpos in
      let import = $2 in
      let as_opt = $4 in
      if import && as_opt = None then Warning.emit ~loc
        "the keyword `import' is redundant here and can be omitted";
      let decl = Ptree.Dcloneimport(loc,import,$3,as_opt,$5) in
      Typing.add_decl loc decl
    }

%public use_as:
| n = tqualid q = option(preceded(AS, uident)) { (n, q) }

%public clone_subst:
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

%public meta_decl:
| META sident comma_list1(meta_arg)  { Dmeta ($2, $3) }

meta_arg:
| TYPE      ty      { Mty $2 }
| CONSTANT  qualid  { Mfs $2 }
| FUNCTION  qualid  { Mfs $2 }
| PREDICATE qualid  { Mps $2 }
| AXIOM     qualid  { Max $2 }
| LEMMA     qualid  { Mlm $2 }
| GOAL      qualid  { Mgl $2 }
| VAL       qualid  { Mval $2 }
| STRING            { Mstr $1 }
| INTEGER           { Mint (Number.to_small_integer $1) }



(* Program declarations *)

%public prog_decl:
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

(* Type witness, extending rules from term parser *)
type_witness:
| BY LEFTBRC field_list1(expr) RIGHTBRC   { $3 }

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
    { let p = mk_pat Pwild $startpos $endpos in
      let d = Efun ([], None, p, Ity.MaskVisible, spec_union $2 $3, $1) in
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
| minus_numeral
    { Econst $1 }
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
    { let rec push pat = re_pat pat (match pat.pat_desc with
        | Ptuple (p::pl) -> Ptuple (push p :: pl)
        | Pcast (p,ty) -> Pcast (push p, ty)
        | Pas (p,v,g) -> Pas (push p, v, g)
        | Por (p,q) -> Por (push p, q)
        | _ -> Pghost pat) in
      let pat = if ghost $2 then push $4 else $4 in
      let loc = floc $startpos($3) $endpos($3) in
      simplify_let_pattern ~loc $3 (apply_partial $2 $6) pat $8 }
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
      let p = mk_pat Pwild $startpos $endpos in
      Efun ($2, None, p, Ity.MaskVisible, spec_union $3 $5, e) }
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
      let p = mk_pat Pwild $startpos $endpos in
      Eany ([], Expr.RKnone, Some ty, p, mask, spec) }
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
| FOR pattern IN seq_expr WITH uident iterator
  DO loop_annotation loop_body DONE
    { let id_b = mk_id break_id $startpos($8) $endpos($8) in
      let id_c = mk_id continue_id $startpos($8) $endpos($8) in
      let mk d = mk_expr d $startpos $endpos in
      let q s = Qdot (Qident $6, mk_id s $startpos($6) $endpos($6)) in
      let next = mk (Eidapp (q "next", [mk (Eident (Qident $7))])) in
      let e = mk (simplify_let_pattern Expr.RKnone next $2 $10) in
      let e = { e with expr_desc = Eoptexn (id_c, Ity.MaskVisible, e) } in
      let e = mk (Ewhile (mk Etrue, fst $9, snd $9, e)) in
      let e = mk (Eoptexn (id_b, Ity.MaskVisible, e)) in
      let unit = mk_expr (Etuple []) $startpos($10) $endpos($10) in
      let e = mk (Ematch (e, [], [q "Done", None, unit])) in
      let create = mk (Eidapp (q "create", [$4])) in
      Elet ($7, false, Expr.RKnone, create, e) }
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
| assertion_kind option(ident_nq) LEFTBRC term RIGHTBRC
    { Eassert (snd $1, name_term $2 (fst $1) $4) }
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
| STRING                    { Econst (Constant.ConstStr $1) }
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
    { let p = mk_pat Pwild $startpos $endpos in
      Efun ([], None, p, Ity.MaskVisible, spec_union $2 $3, $4) }
| BEGIN single_spec spec END
    { let e = mk_expr (Etuple []) $startpos $endpos in
      let p = mk_pat Pwild $startpos $endpos in
      Efun ([], None, p, Ity.MaskVisible, spec_union $2 $3, e) }
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

iterator:
| (* epsilon *) { mk_id "it" $startpos $endpos}
| AS lident     { $2 }

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
| ASSERT  { "Assert", Expr.Assert }
| ASSUME  { "Assume", Expr.Assume }
| CHECK   { "Check", Expr.Check }

for_dir:
| TO      { Expr.To }
| DOWNTO  { Expr.DownTo }

(* Specification *)

spec:
| (* epsilon *) %prec prec_no_spec  { empty_spec }
| single_spec spec                  { spec_union $1 $2 }

single_spec:
| REQUIRES option(ident_nq) LEFTBRC term RIGHTBRC
    { { empty_spec with sp_pre = [name_term $2 "Requires" $4] } }
| ENSURES option(ident_nq) LEFTBRC ensures RIGHTBRC
    { let bindings = List.map (fun (p, t) -> p, name_term $2 "Ensures" t) $4 in
      { empty_spec with sp_post = [floc $startpos($4) $endpos($4), bindings] } }
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
| single_term WITH single_term  { $1, $3 }

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
| INVARIANT option(ident_nq) LEFTBRC term RIGHTBRC
    { name_term $2 "LoopInvariant" $4 }

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
    { mk_pat (Pvar (id_anonymous (floc $startpos $endpos))) $startpos $endpos }

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
