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

open Format
open Tptp_ast

open Why3
open Wstdlib
open Ident
open Ty
open Term
open Decl
open Theory

let error = Loc.error
let errorm = Loc.errorm

exception DuplicateVar of string
exception TypeExpected
exception TermExpected
exception FmlaExpected
exception InvalidDummy
exception MalformedLet
exception DependentTy
exception NonNumeric
exception BadArity

let () = Exn_printer.register (fun fmt e -> match e with
  | DuplicateVar s -> fprintf fmt "variable %s is used twice" s
  | TypeExpected -> fprintf fmt "type expression expected"
  | TermExpected -> fprintf fmt "term expression expected"
  | FmlaExpected -> fprintf fmt "formula expression expected"
  | InvalidDummy -> fprintf fmt "unexpected type placeholder"
  | MalformedLet -> fprintf fmt "malformed let-expression"
  | DependentTy  -> fprintf fmt "dependent type"
  | NonNumeric   -> fprintf fmt "non-numeric argument"
  | BadArity     -> fprintf fmt "bad arity"
  | _ -> raise e)

type symbol =
  | STSko of ty
  | STVar of tvsymbol
  | SVar  of vsymbol
  | SType of tysymbol
  | SFunc of tvsymbol list * tvsymbol list * Stv.t * lsymbol
  | SPred of tvsymbol list * tvsymbol list * Stv.t * lsymbol
  | SletF of tvsymbol list * Stv.t * vsymbol list * term
  | SletP of tvsymbol list * Stv.t * vsymbol list * term
  | Sdobj of lsymbol
  | Suse  of theory

(* dead code
type env = symbol Mstr.t

type implicit = symbol Hstr.t
*)

(** Defined symbols : arithmetic etc... *)

type denv = {
  de_env   : Env.env;

  th_univ  : theory;
  ts_univ  : tysymbol;
  ty_univ  : ty;

  th_ghost : theory;
  ts_ghost : tysymbol;
  fs_ghost : lsymbol;

  th_int   : theory;
  th_real  : theory;
  th_rat   : theory;
  ts_rat   : tysymbol;
}

let make_denv env =
  let get_theory s = Env.read_theory env ["tptp"] s in
  let th_univ = get_theory "Univ" in
  let th_ghost = get_theory "Ghost" in
  let th_rat = get_theory "Rat" in
  let ts_univ = ns_find_ts th_univ.th_export ["iType"] in
  { de_env   = env;

    th_univ  = th_univ;
    ts_univ  = ts_univ;
    ty_univ  = ty_app ts_univ [];

    th_ghost = th_ghost;
    ts_ghost = ns_find_ts th_ghost.th_export ["gh"];
    fs_ghost = ns_find_ls th_ghost.th_export ["gh"];

    th_int   = get_theory "Int";
    th_real  = get_theory "Real";
    th_rat   = th_rat;
    ts_rat   = ns_find_ts th_rat.th_export ["rat"];
  }

let add_theory env impl th =
  let s = "$th$" ^ th.th_name.id_string in
  if not (Mstr.mem s env) then Hstr.replace impl s (Suse th)

let defined_ty ~loc denv env impl dw tyl =
  let ts = match dw with
    | DT DTuniv -> denv.ts_univ
    | DT DTint -> ts_int
    | DT DTreal -> ts_real
    | DT DTrat -> add_theory env impl denv.th_rat; denv.ts_rat
    | DT DTdummy -> error ~loc InvalidDummy
    | DT (DTtype|DTprop) | DF _ | DP _ -> error ~loc TypeExpected
  in
  Loc.try2 ~loc ty_app ts tyl

let defined_arith ~loc denv env impl dw tl =
  let ts = match tl with
    | { t_ty = Some {ty_node = Tyapp (ts,[]) }}::_ -> ts
    | _::_ -> error ~loc NonNumeric
    | [] -> error ~loc BadArity in
  let get_theory s = Env.read_theory denv.de_env ["tptp"] s in
  let get_int_theory = function
    | DF DFquot -> errorm ~loc "$quotient/2 is not defined on $int"
    | DF (DFquot_e|DFrem_e) -> get_theory "IntDivE"
    | DF (DFquot_t|DFrem_t) -> get_theory "IntDivT"
    | DF (DFquot_f|DFrem_f) -> get_theory "IntDivF"
    | DF (DFfloor|DFceil|DFtrunc|DFround|DFtoint)
    | DP (DPisint|DPisrat) -> get_theory "IntTrunc"
    | DF DFtorat -> get_theory "IntToRat"
    | DF DFtoreal -> get_theory "IntToReal"
    | _ -> denv.th_int in
  let get_rat_theory = function
    | DF (DFquot_e|DFrem_e) -> get_theory "RatDivE"
    | DF (DFquot_t|DFrem_t) -> get_theory "RatDivT"
    | DF (DFquot_f|DFrem_f) -> get_theory "RatDivF"
    | DF (DFfloor|DFceil|DFtrunc|DFround|DFtoint) -> get_theory "RatTrunc"
    | DF DFtoreal -> get_theory "RatToReal"
    | _ -> denv.th_rat in
  let get_real_theory = function
    | DF (DFquot_e|DFrem_e) -> get_theory "RealDivE"
    | DF (DFquot_t|DFrem_t) -> get_theory "RealDivT"
    | DF (DFquot_f|DFrem_f) -> get_theory "RealDivF"
    | DF (DFfloor|DFceil|DFtrunc|DFround|DFtoint)
    | DP (DPisint|DPisrat) -> get_theory "RealTrunc"
    | DF DFtorat -> get_theory "RealToRat"
    | _ -> denv.th_real in
  let th =
    if ts_equal ts ts_int then get_int_theory dw else
    if ts_equal ts denv.ts_rat then get_rat_theory dw else
    if ts_equal ts ts_real then get_real_theory dw else
    error ~loc NonNumeric
  in
  add_theory env impl th;
  let ls = match dw with
    | DF DFumin -> ns_find_ls th.th_export [op_prefix "-"]
    | DF DFsum -> ns_find_ls th.th_export [op_infix "+"]
    | DF DFdiff -> ns_find_ls th.th_export [op_infix "-"]
    | DF DFprod -> ns_find_ls th.th_export [op_infix "*"]
    | DF DFquot -> ns_find_ls th.th_export [op_infix "/"]
    | DF DFquot_e -> ns_find_ls th.th_export ["div"]
    | DF DFquot_t -> ns_find_ls th.th_export ["div_t"]
    | DF DFquot_f -> ns_find_ls th.th_export ["div_f"]
    | DF DFrem_e -> ns_find_ls th.th_export ["mod"]
    | DF DFrem_t -> ns_find_ls th.th_export ["mod_t"]
    | DF DFrem_f -> ns_find_ls th.th_export ["mod_f"]
    | DF DFfloor -> ns_find_ls th.th_export ["floor"]
    | DF DFceil -> ns_find_ls th.th_export ["ceiling"]
    | DF DFtrunc -> ns_find_ls th.th_export ["truncate"]
    | DF DFround -> ns_find_ls th.th_export ["round"]
    | DF DFtoint -> ns_find_ls th.th_export ["to_int"]
    | DF DFtorat -> ns_find_ls th.th_export ["to_rat"]
    | DF DFtoreal -> ns_find_ls th.th_export ["to_real"]
    | DP DPless -> ns_find_ls th.th_export [op_infix "<"]
    | DP DPlesseq -> ns_find_ls th.th_export [op_infix "<="]
    | DP DPgreater -> ns_find_ls th.th_export [op_infix ">"]
    | DP DPgreatereq -> ns_find_ls th.th_export [op_infix ">="]
    | DP DPisint -> ns_find_ls th.th_export ["is_int"]
    | DP DPisrat -> ns_find_ls th.th_export ["is_rat"]
    | DP (DPtrue|DPfalse|DPdistinct) | DT _ -> assert false
  in
  Loc.try2 ~loc t_app_infer ls tl

let defined_expr ~loc is_fmla denv env impl dw tl = match dw, tl with
  | (DT DTdummy), _ -> error ~loc InvalidDummy
  | (DF _|DT _), _ when is_fmla -> error ~loc FmlaExpected
  | (DP _|DT _), _ when not is_fmla -> error ~loc TermExpected
  | (DP DPtrue|DP DPfalse), _::_ -> error ~loc BadArity
  | DP DPtrue, [] -> t_true
  | DP DPfalse, [] -> t_false
  | DP DPdistinct, _ ->
      let rec dist acc = function
        | t::tl ->
            let add acc s = t_and_simp acc (t_neq t s) in
            dist (List.fold_left add acc tl) tl
        | _ -> acc
      in
      Loc.try2 ~loc dist t_true tl
  | _ -> defined_arith ~loc denv env impl dw tl

(** TPTP environment *)

let find_tv ~loc env impl s =
  let tv = try Mstr.find s env with Not_found ->
    try Hstr.find impl s with Not_found ->
      let tv = STVar (create_tvsymbol (id_user s loc)) in
      Hstr.add impl s tv;
      tv in
  match tv with
    | STVar tv -> ty_var tv
    | STSko ty -> ty
    | _ -> error ~loc TypeExpected

let find_vs ~loc denv env impl s =
  let vs = try Mstr.find s env with Not_found ->
    try Hstr.find impl s with Not_found ->
      let vs = SVar (create_vsymbol (id_user s loc) denv.ty_univ) in
      Hstr.add impl s vs;
      vs in
  match vs with
    | SVar vs -> t_var vs
    | _ -> error ~loc TermExpected

let find_ts ~loc env impl s args =
  let ts = try Mstr.find s env with Not_found ->
    try Hstr.find impl s with Not_found ->
      let args = List.map (fun _ -> create_tvsymbol (id_fresh "a")) args in
      let ss = if s = "int" || s = "real" then "_" ^ s else s in
      let ts = SType (create_tysymbol (id_user ss loc) args NoDef) in
      Hstr.add impl s ts;
      ts in
  match ts with
    | SType ts -> ts
    | _ -> error ~loc TypeExpected

let find_fs ~loc denv env impl s args =
  try Mstr.find s env with Not_found ->
    try Hstr.find impl s with Not_found ->
      let args = List.map (fun _ -> denv.ty_univ) args in
      let fs = create_fsymbol (id_user s loc) args denv.ty_univ in
      let fs = SFunc ([],[],Stv.empty,fs) in
      Hstr.add impl s fs;
      fs

let find_ps ~loc denv env impl s args =
  try Mstr.find s env with Not_found ->
    try Hstr.find impl s with Not_found ->
      let args = List.map (fun _ -> denv.ty_univ) args in
      let ps = create_psymbol (id_user s loc) args in
      let ps = SPred ([],[],Stv.empty,ps) in
      Hstr.add impl s ps;
      ps

let find_dobj ~loc denv env impl s =
  let ds = "$do$" ^ s in
  let fs = try Mstr.find ds env with Not_found ->
    try Hstr.find impl ds with Not_found ->
      let id = id_user ("do_" ^ s) loc in
      let fs = Sdobj (create_fsymbol id [] denv.ty_univ) in
      Hstr.add impl ds fs;
      fs in
  match fs with
    | Sdobj fs -> fs_app fs [] denv.ty_univ
    | _ -> assert false (* impossible *)

let ty_check loc s ty1 t =
  Loc.try3 ~loc ty_match s ty1 (Opt.get t.t_ty)

let rec ty denv env impl { e_loc = loc; e_node = n } = match n with
  | Eapp (aw,al) ->
      let ts = find_ts ~loc env impl aw al in
      let tyl = List.map (ty denv env impl) al in
      Loc.try2 ~loc ty_app ts tyl
  | Edef (dw,al) ->
      let tyl = List.map (ty denv env impl) al in
      defined_ty ~loc denv env impl dw tyl
  | Evar v ->
      find_tv ~loc env impl v
  | Elet _ | Eite _ | Eqnt _ | Ebin _
  | Enot _ | Eequ _ | Edob _ | Enum _ -> error ~loc TypeExpected

let t_int_const s =
  t_const (Number.(ConstInt { ic_negative = false; ic_abs = int_literal_dec s})) ty_int

(* unused
let t_real_const r = t_const (Number.ConstReal r)
*)

let rec term denv env impl { e_loc = loc; e_node = n } = match n with
  | Eapp (aw,al) ->
      begin match find_fs ~loc denv env impl aw al with
        | SFunc (tvl,gl,mvs,fs) -> ls_args denv env impl loc fs tvl gl mvs al
        | SletF (tvl,mvs,vl,e) -> let_args denv env impl loc e tvl mvs vl al
        | SVar v -> t_var v
        | _ -> error ~loc TermExpected
      end
  | Edef (dw,al) ->
      let tl = List.map (term denv env impl) al in
      defined_expr ~loc false denv env impl dw tl
  | Evar v ->
      find_vs ~loc denv env impl v
  | Edob s ->
      find_dobj ~loc denv env impl s
  | Enum (Nint s) -> t_int_const s
  | Enum (Nreal (i,f,e)) ->
      t_const (Number.(ConstReal { rc_negative = false ;
                                   rc_abs = real_const_dec i (Opt.get_def "0" f) e})) ty_real
  | Enum (Nrat (n,d)) ->
      let n = t_int_const n and d = t_int_const d in
      let frac = ns_find_ls denv.th_rat.th_export ["frac"] in
      add_theory env impl denv.th_rat;
      t_app_infer frac [n;d]
  | Elet (def,e) ->
      let env,s = let_defn denv env impl def in
      begin match Mstr.find s env with
        | SletF ([],_,[],t) ->
            let id = id_user s def.e_loc in
            let vs = create_vsymbol id (Opt.get t.t_ty) in
            let env = Mstr.add s (SVar vs) env in
            let t1 = term denv env impl e in
            t_let_close vs t t1
        | _ ->
            term denv env impl e
      end
  | Eite (e1,e2,e3) ->
      (* we can't fix the polarity of the condition here,
         hence type quantifiers are forbidden in terms *)
      let cn,_ = fmla denv env impl None [] e1 in
      let th = term denv env impl e2 in
      let el = term denv env impl e3 in
      t_if cn th el
  | Eqnt _ | Ebin _ | Enot _ | Eequ _ -> error ~loc TermExpected

and fmla denv env impl pol tvl { e_loc = loc; e_node = n } = match n with
  | Eapp (aw,al) ->
      begin match find_ps ~loc denv env impl aw al with
        | SPred (tvl,gl,mvs,ps) -> ls_args denv env impl loc ps tvl gl mvs al
        | SletP (tvl,mvs,vl,e) -> let_args denv env impl loc e tvl mvs vl al
        | _ -> error ~loc FmlaExpected
      end, false
  | Edef (dw,al) ->
      let tl = List.map (term denv env impl) al in
      defined_expr ~loc true denv env impl dw tl, false
  | Elet (def,e) ->
      let env,s = let_defn denv env impl def in
      begin match Mstr.find s env with
        | SletF ([],_,[],t) ->
            let id = id_user s def.e_loc in
            let vs = create_vsymbol id (Opt.get t.t_ty) in
            let env = Mstr.add s (SVar vs) env in
            let f,b = fmla denv env impl pol tvl e in
            t_let_close vs t f, b
        | _ ->
            fmla denv env impl pol tvl e
      end
  | Eqnt (quant,vl,e1) ->
      let vlist (env,pol,tvl,vl,b) (s,e) =
        let loc = e.e_loc in
        if e.e_node = Edef (DT DTtype, []) then
          match pol,quant with
            | None, _ ->
                errorm ~loc "Invalid type quantifier"
            | Some true, Qexists  (* goals *)
            | Some false, Qforall (* premises *) ->
                let tv = create_tvsymbol (id_user s loc) in
                Mstr.add s (STVar tv) env, pol, tv::tvl, vl, true
            | Some true, Qforall  (* goals *)
            | Some false, Qexists (* premises *) ->
                let _,ln,cn,_ = Loc.get loc in
                let sk = Format.sprintf "_%s_%d_%d" s ln cn in
                let ts = create_tysymbol (id_user sk loc) tvl NoDef in
                let tv = ty_app ts (List.map ty_var tvl) in
                Hstr.add impl sk (SType ts);
                Mstr.add s (STSko tv) env, pol, tvl, vl, true
        else
          let ty = ty denv env impl e in
          let vs = create_vsymbol (id_user s loc) ty in
          Mstr.add s (SVar vs) env, None, [], vs::vl, b
      in
      let env,pol,tvl,vl,b = List.fold_left vlist (env,pol,tvl,[],false) vl in
      let f1,b1 = fmla denv env impl pol tvl e1 in
      let quant = match quant with
        | Qforall -> Tforall
        | Qexists -> Texists in
      t_quant_close quant (List.rev vl) [] f1, b || b1
  | Eite (e1,e2,e3) ->
      (* here we can treat type quantifiers in 'if' conditions,
         since [if C then T else E == (C => T) /\ (C \/ E)], but
         as for now we won't do it to stay consistent with terms *)
      let cn,_  = fmla denv env impl None [] e1 in
      let th,b1 = fmla denv env impl pol tvl e2 in
      let el,b2 = fmla denv env impl pol tvl e3 in
      t_if cn th el, b1 || b2
  | Ebin (BOequ,e1,e2) ->
      let f1,b1 = fmla denv env impl pol tvl e1 in
      let f2,b2 = fmla denv env impl pol tvl e2 in
      if b1 || b2 then
        let g1,_ = fmla denv env impl (Opt.map not pol) tvl e1 in
        let g2,_ = fmla denv env impl (Opt.map not pol) tvl e2 in
        t_and (t_implies g1 f2) (t_implies g2 f1), true
      else
        t_iff f1 f2, false
  | Ebin (BOnequ,e1,e2) ->
      let f1,b1 = fmla denv env impl pol tvl e1 in
      let f2,b2 = fmla denv env impl pol tvl e2 in
      if b1 || b2 then
        let g1,_ = fmla denv env impl (Opt.map not pol) tvl e1 in
        let g2,_ = fmla denv env impl (Opt.map not pol) tvl e2 in
        t_not (t_and (t_implies f1 g2) (t_implies f2 g1)), true
      else
        t_not (t_iff f1 f2), false
  | Ebin (BOimp,e1,e2) ->
      let f1,b1 = fmla denv env impl (Opt.map not pol) tvl e1 in
      let f2,b2 = fmla denv env impl pol tvl e2 in
      t_implies f1 f2, b1 || b2
  | Ebin (BOpmi,e1,e2) ->
      let f1,b1 = fmla denv env impl pol tvl e1 in
      let f2,b2 = fmla denv env impl (Opt.map not pol) tvl e2 in
      t_implies f2 f1, b1 || b2
  | Ebin (BOand,e1,e2) ->
      let f1,b1 = fmla denv env impl pol tvl e1 in
      let f2,b2 = fmla denv env impl pol tvl e2 in
      t_and f1 f2, b1 || b2
  | Ebin (BOor,e1,e2) ->
      let f1,b1 = fmla denv env impl pol tvl e1 in
      let f2,b2 = fmla denv env impl pol tvl e2 in
      t_or f1 f2, b1 || b2
  | Ebin (BOnand,e1,e2) ->
      let f1,b1 = fmla denv env impl (Opt.map not pol) tvl e1 in
      let f2,b2 = fmla denv env impl (Opt.map not pol) tvl e2 in
      t_not (t_and f1 f2), b1 || b2
  | Ebin (BOnor,e1,e2) ->
      let f1,b1 = fmla denv env impl (Opt.map not pol) tvl e1 in
      let f2,b2 = fmla denv env impl (Opt.map not pol) tvl e2 in
      t_not (t_or f1 f2), b1 || b2
  | Enot e1 ->
      let f1,b1 = fmla denv env impl (Opt.map not pol) tvl e1 in
      t_not f1, b1
  | Eequ (e1,e2) ->
      let t1 = term denv env impl e1 in
      let t2 = term denv env impl e2 in
      t_equ t1 t2, false
  | Evar _ | Edob _ | Enum _ -> error ~loc FmlaExpected

and let_defn denv env impl { e_node = n ; e_loc = loc } =
  let rec newenv env tvl vl = function
    | [] -> env, List.rev tvl, List.rev vl
    | (s,{ e_node = Edef (DT DTtype, []); e_loc = loc })::al ->
        if vl <> [] then errorm ~loc "Invalid type quantifier";
        let tv = create_tvsymbol (id_user s loc) in
        let env = Mstr.add s (STVar tv) env in
        newenv env (tv::tvl) vl al
    | (s,e)::al ->
        let ty = ty denv env impl e in
        let vs = create_vsymbol (id_user s e.e_loc) ty in
        let env = Mstr.add s (SVar vs) env in
        newenv env tvl (vs::vl) al
  in
  let rec check ss vl al = match vl,al with
    | [],[] -> ()
    | (v,_)::vl, { e_node = Evar u }::al when u = v ->
        let ss = Sstr.change (fun b ->
          not (b && error ~loc (DuplicateVar v))) v ss in
        check ss vl al
    | _,_ -> error ~loc MalformedLet in
  let dig vl d isf e = match d.e_node with
    | Eapp (s,al) ->
        check Sstr.empty vl al;
        let enw,tvl,vl = newenv env [] [] vl in
        let fvs s v = ty_freevars s v.vs_ty in
        let tvs = List.fold_left fvs Stv.empty vl in
        let add s v = if Stv.mem v tvs then s else Stv.add v s in
        let mvs = List.fold_left add Stv.empty tvl in
        if isf then
          let f,_ = fmla denv enw impl None [] e in
          Mstr.add s (SletP (tvl,mvs,vl,f)) env, s
        else
          let t = term denv enw impl e in
          Mstr.add s (SletF (tvl,mvs,vl,t)) env, s
    | _ -> assert false (* impossible *) in
  let rec down vl = function
    | Eqnt (Qforall,ul,d) -> down (vl @ ul) d.e_node
    | Ebin (BOequ,e1,e2) -> dig vl e1 true e2
    | Eequ (e1,e2) -> dig vl e1 false e2
    | _ -> assert false (* impossible *) in
  down [] n

and ls_args denv env impl loc fs tvl gl mvs al =
  let rec args tvm tvl al = match tvl,al with
    | (tv::tvl),({e_node = Edef (DT DTdummy,[]); e_loc = loc}::al) ->
        if Stv.mem tv mvs then error ~loc InvalidDummy;
        args tvm tvl al
    | (tv::tvl),(a::al) ->
        let ty = ty denv env impl a in
        let tvm = Mtv.add tv ty tvm in
        args tvm tvl al
    | [],al ->
        let ghost v =
          fs_app denv.fs_ghost [] (ty_app denv.ts_ghost [Mtv.find v tvm]) in
        let tl = List.map ghost gl @ List.map (term denv env impl) al in
        let tvm = List.fold_left2 (ty_check loc) tvm fs.ls_args tl in
        let ty = Opt.map (ty_inst tvm) fs.ls_value in
        t_app fs tl ty
    | _ -> error ~loc BadArity
  in
  args Mtv.empty tvl al

and let_args denv env impl loc e tvl mvs vl al =
  let rec args tvm vm tvl vl al = match tvl,vl,al with
    | (tv::tvl),_,({e_node = Edef (DT DTdummy,[]); e_loc = loc}::al) ->
        if Stv.mem tv mvs then error ~loc InvalidDummy;
        args tvm vm tvl vl al
    | (tv::tvl),_,(a::al) ->
        let ty = ty denv env impl a in
        let tvm = Mtv.add tv ty tvm in
        args tvm vm tvl vl al
    | _,(v::vl),(a::al) ->
        let t = term denv env impl a in
        let tvm = ty_check loc tvm v.vs_ty t in
        let vm = Mvs.add v t vm in
        args tvm vm tvl vl al
    | [],[],[] ->
        t_ty_subst tvm vm e
    | _ -> error ~loc BadArity
  in
  args Mtv.empty Mvs.empty tvl vl al

let typedecl denv env impl loc s (tvl,(el,e)) =
  if e.e_node = Edef (DT DTtype, []) then
    (* type constructor *)
    if tvl <> [] then error ~loc DependentTy else
    let ntv { e_node = n ; e_loc = loc } = match n with
      | Edef (DT DTtype, []) -> create_tvsymbol (id_fresh "a")
      | _ -> error ~loc DependentTy
    in
    let ss = if s = "int" || s = "real" then "_" ^ s else s in
    let ts = create_tysymbol (id_user ss loc) (List.map ntv el) NoDef in
    Hstr.add impl s (SType ts)
  else
    (* function/predicate symbol *)
    let ntv (s, { e_node = n ; e_loc = loc }) = match n with
      | Edef (DT DTtype, []) -> create_tvsymbol (id_fresh s)
      | _ -> error ~loc DependentTy
    in
    let tvl = List.map ntv tvl in
    let add e v =
      let s = v.tv_name.id_string in
      Mstr.add_new (DuplicateVar s) s (STVar v) e
    in
    let env = List.fold_left add env tvl in
    let tyl = List.map (ty denv env impl) el in
    let tvs = List.fold_left ty_freevars Stv.empty tyl in
    let add s v = if Stv.mem v tvs then s else Stv.add v s in
    let mvs = List.fold_left add Stv.empty tvl in
    let ghost v = ty_app denv.ts_ghost [ty_var v] in
    if e.e_node = Edef (DT DTprop, []) then
      let gvl = List.filter (fun v -> not (Stv.mem v tvs)) tvl in
      let tyl = List.map ghost gvl @ tyl in
      let ls = create_psymbol (id_user s loc) tyl in
      if gvl <> [] then add_theory env impl denv.th_ghost;
      Hstr.add impl s (SPred (tvl,gvl,mvs,ls))
    else
      let tyv = ty denv env impl e in
      let tvs = ty_freevars tvs tyv in
      let gvl = List.filter (fun v -> not (Stv.mem v tvs)) tvl in
      let tyl = List.map ghost gvl @ tyl in
      let ls = create_fsymbol (id_user s loc) tyl tyv in
      if gvl <> [] then add_theory env impl denv.th_ghost;
      Hstr.add impl s (SFunc (tvl,gvl,mvs,ls))

let flush_impl ~strict env uc impl =
  let update_th _ e uc = match e with
    | Suse th ->
        let uc = open_scope uc th.th_name.id_string in
        let uc = use_export uc th in
        close_scope uc ~import:false
    | _ -> uc
  in
  let update s e (env,uc) = match e with
    | SType ts ->
        Mstr.add s e env, add_ty_decl uc ts
    | SFunc (_,_,_,ls) | SPred (_,_,_,ls) ->
        Mstr.add s e env, add_param_decl uc ls
    | STVar tv when strict ->
        errorm ?loc:tv.tv_name.id_loc "Unbound type variable %s" s
    | SVar vs when strict ->
        errorm ?loc:vs.vs_name.id_loc "Unbound variable %s" s
    | STVar _ | SVar _ -> env,uc
    | Sdobj ls ->
        let uc = add_param_decl uc ls in
        let t = t_app ls [] ls.ls_value in
        let add _ s f = match s with
          | Sdobj fs -> t_and_simp f (t_neq (t_app fs [] fs.ls_value) t)
          | _ -> f in
        let f = Mstr.fold add env t_true in
        let uc = if t_equal f t_true then uc else
          let id = ls.ls_name.id_string ^ "_def" in
          let pr = create_prsymbol (id_fresh id) in
          add_prop_decl uc Paxiom pr f in
        Mstr.add s e env, uc
    | Suse _ ->
        Mstr.add s e env, uc
    (* none of these is possible in implicit *)
    | SletF _ | SletP _ | STSko _ -> assert false
  in
  let uc = Hstr.fold update_th impl uc in
  let res = Hstr.fold update impl (env,uc) in
  Hstr.clear impl;
  res

let typecheck lib path ast =
  (* initial environment *)
  let env  = Mstr.empty in
  let denv = make_denv lib in
  let impl = Hstr.create 17 in
  add_theory env impl denv.th_univ;
  (* parsing function *)
  let conj = ref [] in
  let input (env,uc) = function
    (* type declarations *)
    | Formula (_,_,Type,TypedAtom (s,e),loc) ->
        typedecl denv env impl loc s e;
        flush_impl ~strict:true env uc impl
    | Formula (_,_,Type,_,loc)
    | Formula (_,_,_,TypedAtom _,loc) ->
        errorm ~loc "Invalid type declaration"
    (* logical formulas *)
    | Formula (_,_,_,Sequent _,loc) -> (* TODO *)
        errorm ~loc "Sequents are not supported"
    | Formula (k,s,r,LogicFormula e,loc) ->
        let strict = k <> CNF in
        let goal = r = Conjecture in
        let f,_ = fmla denv env impl (Some goal) [] e in
        let f = if strict then f else
          let q = if goal then Texists else Tforall in
          let vl = Mvs.keys (t_vars f) in
          t_quant_close q vl [] f in
        let env,uc = flush_impl ~strict env uc impl in
        let pr = create_prsymbol (id_user s loc) in
        if goal then conj := (pr, f) :: !conj;
        env, if goal then uc else add_prop_decl uc Paxiom pr f
    (* includes *)
    | Include (_,_,loc) ->
        errorm ~loc "Inclusion is not supported"
  in
  (* FIXME: localize the identifier *)
  let uc = create_theory ~path (id_fresh "T") in
  let _,uc = List.fold_left input (env,uc) ast in
  (* In presence of conjectures, TPTP requires us to prove
     their conjunction, but no conjectures means |- false.
     This is awkward, and most provers treat conjectures
     disjunctively, as in a sequent. We follow TPTP here. *)
  let pr_false = create_prsymbol (id_fresh "contradiction") in
  let uc = match !conj with
    | g :: gl ->
        let combine (_, f) (pr, g) = pr, t_and g f in
        let pr, goal = List.fold_left combine g gl in
        if Stv.is_empty (t_ty_freevars Stv.empty goal) then
          add_prop_decl uc Pgoal pr goal
        else (* Why3 does not support polymorphic goals *)
          let uc = add_prop_decl uc Paxiom pr (t_not goal) in
          add_prop_decl uc Pgoal pr_false t_false
    | [] -> add_prop_decl uc Pgoal pr_false t_false
  in
  Mstr.singleton "T" (close_theory uc)
