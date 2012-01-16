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

exception TypeInference
exception TypeExpected
exception TermExpected
exception FmlaExpected
exception TVarExpected
exception VarExpected
exception InvalidDummy
exception BadTyQuant
exception BadArity

let () = Exn_printer.register (fun fmt e -> match e with
  | Message s -> fprintf fmt "%s" s
  | TypeInference -> fprintf fmt "type inference is not supported"
  | TypeExpected -> fprintf fmt "type expression expected"
  | TermExpected -> fprintf fmt "term expression expected"
  | FmlaExpected -> fprintf fmt "formula expression expected"
  | TVarExpected -> fprintf fmt "type variable expected"
  | VarExpected  -> fprintf fmt "term variable expected"
  | InvalidDummy -> fprintf fmt "invalid type placeholder"
  | BadTyQuant -> fprintf fmt "forbidden type quantifier"
  | BadArity -> fprintf fmt "bad arity"
  | _ -> raise e)

type symbol =
  | STVar of ty
  | SVar  of vsymbol
  | SType of tysymbol
  | SFunc of tvsymbol list * lsymbol
  | SPred of tvsymbol list * lsymbol
  | SletF of tvsymbol list * vsymbol list * term
  | SletP of tvsymbol list * vsymbol list * term

type env = symbol Mstr.t

type implicit = (string,symbol) Hashtbl.t

let ts_univ = create_tysymbol (id_fresh "iType") [] None
let ty_univ = ty_app ts_univ []
let d_univ  = create_ty_decl [ts_univ, Tabstract]

let find_tv ~loc env impl s =
  let tv = try Mstr.find s env with Not_found ->
    try Hashtbl.find impl s with Not_found ->
      let tv = STVar (ty_var (create_tvsymbol (id_user s loc))) in
      Hashtbl.add impl s tv;
      tv in
  match tv with
    | STVar tv -> tv
    | _ -> error ~loc TVarExpected

let find_vs ~loc env impl s =
  let vs = try Mstr.find s env with Not_found ->
    try Hashtbl.find impl s with Not_found ->
      let vs = SVar (create_vsymbol (id_user s loc) ty_univ) in
      Hashtbl.add impl s vs;
      vs in
  match vs with
    | SVar vs -> vs
    | _ -> error ~loc VarExpected

let find_ts ~loc env impl s args =
  try Mstr.find s env with Not_found ->
    try Hashtbl.find impl s with Not_found ->
      let args = List.map (fun _ -> create_tvsymbol (id_fresh "a")) args in
      let ts = SType (create_tysymbol (id_user s loc) args None) in
      Hashtbl.add impl s ts;
      ts

let find_fs ~loc env impl s args =
  try Mstr.find s env with Not_found ->
    try Hashtbl.find impl s with Not_found ->
      let args = List.map (fun _ -> ty_univ) args in
      let fs = SFunc ([], create_fsymbol (id_user s loc) args ty_univ) in
      Hashtbl.add impl s fs;
      fs

let find_ps ~loc env impl s args =
  try Mstr.find s env with Not_found ->
    try Hashtbl.find impl s with Not_found ->
      let args = List.map (fun _ -> ty_univ) args in
      let ps = SPred ([], create_psymbol (id_user s loc) args) in
      Hashtbl.add impl s ps;
      ps

let rec ty denv env impl { e_loc = loc; e_node = n } = match n with
  | Eapp (aw,al) ->
      let ts = match find_ts ~loc env impl aw al with
        | SType ts -> ts
        | _ -> error ~loc TypeExpected in
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
        | SFunc (tvl,fs) -> ls_args denv env impl loc fs tvl al
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
      t_var (find_vs ~loc env impl v)
  | Edob _ ->
      (* TODO: distinct objects *)
      assert false
  | Enum _ ->
      (* TODO: arithmetic *)
      assert false
  | Elet (_def,_e) ->
      (* TODO: let *)
      assert false
  | Eite (e1,e2,e3) ->
      (* we can't fix the polarity of the condition here,
         and so type quantifiers are forbidden in terms *)
      let cn,_ = fmla denv env impl None [] e1 in
      let th = term denv env impl e2 in
      let el = term denv env impl e3 in
      t_if cn th el
  | Eqnt _ | Ebin _ | Enot _ | Eequ _ -> error ~loc TermExpected

and fmla denv env impl pol tvl { e_loc = loc; e_node = n } = match n with
  | Eapp (aw,al) ->
      begin match find_ps ~loc env impl aw al with
        | SPred (tvl,ps) -> ls_args denv env impl loc ps tvl al, false
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
  | Elet (_def,_e) ->
      (* TODO: let *)
      assert false
  | Eqnt (quant,vl,e1) ->
      let vlist (env,pol,tvl,vl,b) (s,e) =
        let loc = e.e_loc in
        if e.e_node = Edef (DT DTtype, []) then
          match pol,quant with
            | None, _ -> error ~loc BadTyQuant
            | Some true, Qexists  (* goals *)
            | Some false, Qforall (* premises *) ->
                let tv = create_tvsymbol (id_user s loc) in
                Mstr.add s (STVar (ty_var tv)) env, pol, tv::tvl, vl, true
            | Some true, Qforall  (* goals *)
            | Some false, Qexists (* premises *) ->
                let ts = create_tysymbol (id_user s loc) tvl None in
                let tv = ty_app ts (List.map ty_var tvl) in
                Hashtbl.add impl ("_sk_" ^ s) (SType ts);
                Mstr.add s (STVar tv) env, pol, tvl, vl, true
        else
          let ty = ty denv env impl e in
          let vs = create_vsymbol (id_user s loc) ty in
          Mstr.add s (SVar vs) env, None, [], vs::vl, b
      in
      let env,pol,tvl,vl,b = List.fold_left vlist (env,pol,tvl,[],false) vl in
      let f1,b1 = fmla denv env impl pol tvl e1 in
      let quant = match quant with
        | Qforall -> Tforall
        | Qexists -> Texists
      in
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

and ls_args denv env impl loc fs tvl al =
  let rec args tvm tvl al = match tvl,al with
    | (tv::tvl),(a::al) ->
        let ty = ty denv env impl a in
        let tvm = Mtv.add tv ty tvm in
        args tvm tvl al
    | [],al ->
        (* TODO: type checking + dummies *)
        let ty = option_map (ty_inst tvm) fs.ls_value in
        let tl = List.map (term denv env impl) al in
        t_app fs tl ty
    | _ -> error ~loc BadArity
  in
  args Mtv.empty tvl al

and let_args denv env impl loc e tvl vl al =
  let rec args tvm vm tvl vl al = match tvl,vl,al with
    | (tv::tvl),_,(a::al) ->
        let ty = ty denv env impl a in
        let tvm = Mtv.add tv ty tvm in
        args tvm vm tvl vl al
    | _,(v::vl),(a::al) ->
        let t = term denv env impl a in
        let vm = Mvs.add v t vm in
        args tvm vm tvl vl al
    | [],[],[] ->
        t_ty_subst tvm vm e
    | _ -> error ~loc BadArity
  in
  args Mtv.empty Mvs.empty tvl vl al

let typecheck _env _path _ast = Mstr.empty

