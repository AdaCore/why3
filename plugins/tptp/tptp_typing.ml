(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Format
open Tptp_ast

open Why3
open Util
open Ident
open Ty
open Term
open Decl
open Theory

exception Message of string

let error ?loc e = match loc with
  | None -> raise e
  | Some loc -> raise (Loc.Located (loc,e))

let errorm ?loc f =
  let buf = Buffer.create 512 in
  let fmt = Format.formatter_of_buffer buf in
  Format.kfprintf (fun _ ->
    Format.pp_print_flush fmt ();
    let s = Buffer.contents buf in
    Buffer.clear buf;
    error ?loc (Message s)) fmt f

exception TypeExpected
exception TermExpected
exception FmlaExpected
exception InvalidDummy
exception MalformedLet
exception DependentTy
exception BadArity

let () = Exn_printer.register (fun fmt e -> match e with
  | Message s -> fprintf fmt "%s" s
  | TypeExpected -> fprintf fmt "type expression expected"
  | TermExpected -> fprintf fmt "term expression expected"
  | FmlaExpected -> fprintf fmt "formula expression expected"
  | InvalidDummy -> fprintf fmt "invalid type placeholder"
  | MalformedLet -> fprintf fmt "malformed let-expression"
  | DependentTy  -> fprintf fmt "dependent type"
  | BadArity     -> fprintf fmt "bad arity"
  | _ -> raise e)

type symbol =
  | STSko of ty
  | STVar of tvsymbol
  | SVar  of vsymbol
  | SType of tysymbol
  | SFunc of tvsymbol list * tvsymbol list * lsymbol
  | SPred of tvsymbol list * tvsymbol list * lsymbol
  | SletF of tvsymbol list * vsymbol list * term
  | SletP of tvsymbol list * vsymbol list * term

type env = symbol Mstr.t

type implicit = (string,symbol) Hashtbl.t

let ts_univ = create_tysymbol (id_fresh "$iType") [] None
let ty_univ = ty_app ts_univ []
let d_univ  = create_ty_decl [ts_univ, Tabstract]

let nm_ghost = "$ghost"
let tv_ghost = create_tvsymbol (id_fresh "a")
let fs_ghost = create_fsymbol (id_fresh nm_ghost) [] (ty_var tv_ghost)

let find_tv ~loc env impl s =
  let tv = try Mstr.find s env with Not_found ->
    try Hashtbl.find impl s with Not_found ->
      let tv = STVar (create_tvsymbol (id_user s loc)) in
      Hashtbl.add impl s tv;
      tv in
  match tv with
    | STVar tv -> ty_var tv
    | STSko ty -> ty
    | _ -> error ~loc TypeExpected

let find_vs ~loc env impl s =
  let vs = try Mstr.find s env with Not_found ->
    try Hashtbl.find impl s with Not_found ->
      let vs = SVar (create_vsymbol (id_user s loc) ty_univ) in
      Hashtbl.add impl s vs;
      vs in
  match vs with
    | SVar vs -> t_var vs
    | _ -> error ~loc TermExpected

let find_ts ~loc env impl s args =
  let ts = try Mstr.find s env with Not_found ->
    try Hashtbl.find impl s with Not_found ->
      let args = List.map (fun _ -> create_tvsymbol (id_fresh "a")) args in
      let ts = SType (create_tysymbol (id_user s loc) args None) in
      Hashtbl.add impl s ts;
      ts in
  match ts with
    | SType ts -> ts
    | _ -> error ~loc TypeExpected

let find_fs ~loc env impl s args =
  try Mstr.find s env with Not_found ->
    try Hashtbl.find impl s with Not_found ->
      let args = List.map (fun _ -> ty_univ) args in
      let fs = create_fsymbol (id_user s loc) args ty_univ in
      let fs = SFunc ([],[],fs) in
      Hashtbl.add impl s fs;
      fs

let find_ps ~loc env impl s args =
  try Mstr.find s env with Not_found ->
    try Hashtbl.find impl s with Not_found ->
      let args = List.map (fun _ -> ty_univ) args in
      let ps = create_psymbol (id_user s loc) args in
      let ps = SPred ([],[],ps) in
      Hashtbl.add impl s ps;
      ps

let ty_check loc s ty1 t =
  let ty1 = ty_inst s ty1 in
  let ty2 = of_option t.t_ty in
  if ty_equal ty1 ty2 then () else
  error ~loc (Ty.TypeMismatch (ty1,ty2))

let rec ty denv env impl { e_loc = loc; e_node = n } = match n with
  | Eapp (aw,al) ->
      let ts = find_ts ~loc env impl aw al in
      let tys = List.map (ty denv env impl) al in
      ty_app ts tys
  | Edef (dw,al) ->
      let ts = match dw with
        | DT DTuniv -> ts_univ (* TODO: arity of defined symbols *)
        | DT DTint
        | DT DTrat
        | DT DTreal -> assert false (* TODO: arithmetic *)
        | DT DTdummy -> error ~loc InvalidDummy
        | DT DTtype | DT DTprop | DF _ | DP _ -> error ~loc TypeExpected in
      let tys = List.map (ty denv env impl) al in
      ty_app ts tys
  | Evar v ->
      find_tv ~loc env impl v
  | Elet _ | Eite _ | Eqnt _ | Ebin _
  | Enot _ | Eequ _ | Edob _ | Enum _ -> error ~loc TypeExpected

let rec term denv env impl { e_loc = loc; e_node = n } = match n with
  | Eapp (aw,al) ->
      begin match find_fs ~loc env impl aw al with
        | SFunc (tvl,gl,fs) -> ls_args denv env impl loc fs tvl gl al
        | SletF (tvl,vl,e) -> let_args denv env impl loc e tvl vl al
        | SVar v -> t_var v
        | _ -> error ~loc TermExpected
      end
  | Edef (dw,al) ->
      let fs = match dw with
        | DF _ -> assert false (* TODO: arithmetic *)
        | DT DTdummy -> error ~loc InvalidDummy
        | DT _ | DP _ -> error ~loc TermExpected in
      let tl = List.map (term denv env impl) al in
      t_app_infer fs tl
  | Evar v ->
      find_vs ~loc env impl v
  | Edob _ ->
      (* TODO: distinct objects *)
      assert false
  | Enum _ ->
      (* TODO: arithmetic *)
      assert false
  | Elet (def,e) ->
      let env,s = let_defn denv env impl def in
      begin match Mstr.find s env with
        | SletF ([],[],t) ->
            let id = id_user s def.e_loc in
            let vs = create_vsymbol id (of_option t.t_ty) in
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
      begin match find_ps ~loc env impl aw al with
        | SPred (tvl,gl,ps) -> ls_args denv env impl loc ps tvl gl al, false
        | SletP (tvl,vl,e) -> let_args denv env impl loc e tvl vl al, false
        | _ -> error ~loc FmlaExpected
      end
  | Edef (dw,al) ->
      let ps = match dw with
        | DP _ -> assert false (* TODO: arithmetic *)
        | DT DTdummy -> error ~loc InvalidDummy
        | DT _ | DF _ -> error ~loc FmlaExpected in
      let tl = List.map (term denv env impl) al in
      ps_app ps tl, false
  | Elet (def,e) ->
      let env,s = let_defn denv env impl def in
      begin match Mstr.find s env with
        | SletF ([],[],t) ->
            let id = id_user s def.e_loc in
            let vs = create_vsymbol id (of_option t.t_ty) in
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
                let ts = create_tysymbol (id_user sk loc) tvl None in
                let tv = ty_app ts (List.map ty_var tvl) in
                Hashtbl.add impl sk (SType ts);
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
        let g1,_ = fmla denv env impl (option_map not pol) tvl e1 in
        let g2,_ = fmla denv env impl (option_map not pol) tvl e2 in
        t_and (t_implies g1 f2) (t_implies g2 f1), true
      else
        t_iff f1 f2, false
  | Ebin (BOnequ,e1,e2) ->
      let f1,b1 = fmla denv env impl pol tvl e1 in
      let f2,b2 = fmla denv env impl pol tvl e2 in
      if b1 || b2 then
        let g1,_ = fmla denv env impl (option_map not pol) tvl e1 in
        let g2,_ = fmla denv env impl (option_map not pol) tvl e2 in
        t_not (t_and (t_implies f1 g2) (t_implies f2 g1)), true
      else
        t_not (t_iff f1 f2), false
  | Ebin (BOimp,e1,e2) ->
      let f1,b1 = fmla denv env impl (option_map not pol) tvl e1 in
      let f2,b2 = fmla denv env impl pol tvl e2 in
      t_implies f1 f2, b1 || b2
  | Ebin (BOpmi,e1,e2) ->
      let f1,b1 = fmla denv env impl pol tvl e1 in
      let f2,b2 = fmla denv env impl (option_map not pol) tvl e2 in
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
      let f1,b1 = fmla denv env impl (option_map not pol) tvl e1 in
      let f2,b2 = fmla denv env impl (option_map not pol) tvl e2 in
      t_not (t_and f1 f2), b1 || b2
  | Ebin (BOnor,e1,e2) ->
      let f1,b1 = fmla denv env impl (option_map not pol) tvl e1 in
      let f2,b2 = fmla denv env impl (option_map not pol) tvl e2 in
      t_not (t_or f1 f2), b1 || b2
  | Enot e1 ->
      let f1,b1 = fmla denv env impl (option_map not pol) tvl e1 in
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
        let ss = Sstr.change v (fun b ->
          not (b && error ~loc MalformedLet)) ss in
        check ss vl al
    | _,_ -> error ~loc MalformedLet in
  let dig vl d isf e = match d.e_node with
    | Eapp (s,al) ->
        check Sstr.empty vl al;
        let enw,tvl,vl = newenv env [] [] vl in
        if isf then
          let f,_ = fmla denv enw impl None [] e in
          Mstr.add s (SletP (tvl,vl,f)) env, s
        else
          let t = term denv enw impl e in
          Mstr.add s (SletF (tvl,vl,t)) env, s
    | _ -> assert false (* impossible *) in
  let dig vl = function
    | Ebin (BOequ,e1,e2) -> dig vl e1 true e2
    | Eequ (e1,e2) -> dig vl e1 false e2
    | _ -> assert false (* impossible *) in
  match n with
    | Eqnt (Qforall,vl,d) -> dig vl d.e_node
    | d -> dig [] d

and ls_args denv env impl loc fs tvl gl al =
  let rec args tvm tvl al = match tvl,al with
    | (tv::tvl),(a::al) ->
        let ty = ty denv env impl a in
        let tvm = Mtv.add tv ty tvm in
        args tvm tvl al
    | [],al ->
        (* TODO: dummies *)
        let ghost v = fs_app fs_ghost [] (Mtv.find v tvm) in
        let ty = option_map (ty_inst tvm) fs.ls_value in
        let tl = List.map (term denv env impl) al in
        let tl = List.map ghost gl @ tl in
        List.iter2 (ty_check loc tvm) fs.ls_args tl;
        t_app fs tl ty
    | _ -> error ~loc BadArity
  in
  if gl <> [] && not (Mstr.mem nm_ghost env) then begin
    let ghfs = SFunc ([tv_ghost],[tv_ghost],fs_ghost) in
    Hashtbl.add impl nm_ghost ghfs
  end;
  args Mtv.empty tvl al

and let_args denv env impl loc e tvl vl al =
  let rec args tvm vm tvl vl al = match tvl,vl,al with
    | (tv::tvl),_,(a::al) ->
        let ty = ty denv env impl a in
        let tvm = Mtv.add tv ty tvm in
        args tvm vm tvl vl al
    | _,(v::vl),(a::al) ->
        let t = term denv env impl a in
        ty_check loc tvm v.vs_ty t;
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
    let ts = create_tysymbol (id_user s loc) (List.map ntv el) None in
    Hashtbl.add impl s (SType ts)
  else
    (* function/predicate symbol *)
    let ntv (s, { e_node = n ; e_loc = loc }) = match n with
      | Edef (DT DTtype, []) -> create_tvsymbol (id_fresh s)
      | _ -> error ~loc DependentTy
    in
    let tvl = List.map ntv tvl in
    let add e v = Mstr.add v.tv_name.id_string (STVar v) e in
    let env = List.fold_left add env tvl in
    let tyl = List.map (ty denv env impl) el in
    if e.e_node = Edef (DT DTprop, []) then
      let tvs = List.fold_left ty_freevars Stv.empty tyl in
      let gvl = List.filter (fun v -> not (Stv.mem v tvs)) tvl in
      let tyl = List.map ty_var gvl @ tyl in
      let ls = create_psymbol (id_user s loc) tyl in
      Hashtbl.add impl s (SPred (tvl,gvl,ls))
    else
      let tyv = ty denv env impl e in
      let tvs = List.fold_left ty_freevars Stv.empty (tyv::tyl) in
      let gvl = List.filter (fun v -> not (Stv.mem v tvs)) tvl in
      let tyl = List.map ty_var gvl @ tyl in
      let ls = create_fsymbol (id_user s loc) tyl tyv in
      Hashtbl.add impl s (SFunc (tvl,gvl,ls))

let flush_impl ~strict env uc impl =
  let update s e (env,uc) = match e with
    | SType ts ->
        Mstr.add s e env, add_ty_decl uc [ts,Tabstract]
    | SFunc (_,_,ls) | SPred (_,_,ls) ->
        Mstr.add s e env, add_logic_decl uc [ls,None]
    | STVar tv when strict ->
        errorm ?loc:tv.tv_name.id_loc "Unbound type variable %s" s
    | SVar vs when strict ->
        errorm ?loc:vs.vs_name.id_loc "Unbound variable %s" s
    | STVar _ | SVar _ -> env,uc
    (* none of these is possible in implicit *)
    | SletF _ | SletP _ | STSko _ -> assert false
  in
  let res = Hashtbl.fold update impl (env,uc) in
  Hashtbl.clear impl;
  res

let typecheck _genv path ast =
  (* TODO: built-ins *)
  let denv = () in
  let impl = Hashtbl.create 17 in
  let conj = ref false in
  let negc = ref false in
  let input (env,uc) = function
    (* illegal stuff *)
    | Formula (_,_,_,_,loc) when !conj ->
        errorm ~loc "No formula can appear below a conjecture"
    | Formula (_,_,r,_,loc) when !negc && r <> Negated_conjecture ->
        errorm ~loc "This formula cannot appear below a negated_conjecture"
    | Include (_,_,loc) when !conj || !negc ->
        errorm ~loc "Includes cannot appear below conjectures"
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
        if r = Conjecture then conj := true;
        if r = Negated_conjecture then negc := true;

        let strict = k <> CNF in
        let pol = r = Conjecture in
        let f,_ = fmla denv env impl (Some pol) [] e in
        let f = if strict then f else
          let q = if pol then Texists else Tforall in
          let vl = Mvs.keys f.t_vars in
          t_quant_close q vl [] f in
        let env,uc = flush_impl ~strict env uc impl in

        let pr = create_prsymbol (id_user s loc) in
        if r <> Conjecture then
          env, add_prop_decl uc Paxiom pr f
        else if Stv.is_empty (t_ty_freevars Stv.empty f) then
          env, add_prop_decl uc Pgoal pr f
        else
          (* Why3 does not support polymorphic goals *)
          let uc = add_prop_decl uc Paxiom pr (t_not f) in
          let pr = create_prsymbol (id_fresh "contradiction") in
          env, add_prop_decl uc Pgoal pr t_false
    (* includes *)
    | Include (_f,[],_loc) ->
        assert false (* TODO: include *)
    | Include (_,_,loc) ->
        errorm ~loc "Formula selection is not supported"
  in
  let env = Mstr.empty in
  (* FIXME: localize the identifier *)
  let uc = create_theory ~path (id_fresh "T") in
  let uc = add_decl uc d_univ in
  let _,uc = List.fold_left input (env,uc) ast in
  let uc = if not !negc then uc else
    let pr = create_prsymbol (id_fresh "contradiction") in
    add_prop_decl uc Pgoal pr t_false in
  Mstr.singleton "T" (close_theory uc)

