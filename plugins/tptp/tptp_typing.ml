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
  | BadArity -> fprintf fmt "bad arity"
  | _ -> raise e)

type symbol =
  | STVar of tvsymbol
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

let find_tv ~loc impl env s =
  let tv = try Mstr.find s env with Not_found ->
    try Hashtbl.find impl s with Not_found ->
      let tv = STVar (create_tvsymbol (id_user s loc)) in
      Hashtbl.add impl s tv;
      tv in
  match tv with
    | STVar tv -> tv
    | _ -> error ~loc TVarExpected

let find_vs ~loc impl env s =
  let vs = try Mstr.find s env with Not_found ->
    try Hashtbl.find impl s with Not_found ->
      let vs = SVar (create_vsymbol (id_user s loc) ty_univ) in
      Hashtbl.add impl s vs;
      vs in
  match vs with
    | SVar vs -> vs
    | _ -> error ~loc VarExpected

let find_ts ~loc impl env s args =
  try Mstr.find s env with Not_found ->
    try Hashtbl.find impl s with Not_found ->
      let args = List.map (fun _ -> create_tvsymbol (id_fresh "a")) args in
      let ts = SType (create_tysymbol (id_user s loc) args None) in
      Hashtbl.add impl s ts;
      ts

let find_fs ~loc impl env s args =
  try Mstr.find s env with Not_found ->
    try Hashtbl.find impl s with Not_found ->
      let args = List.map (fun _ -> ty_univ) args in
      let fs = SFunc ([], create_fsymbol (id_user s loc) args ty_univ) in
      Hashtbl.add impl s fs;
      fs

let find_ps ~loc impl env s args =
  try Mstr.find s env with Not_found ->
    try Hashtbl.find impl s with Not_found ->
      let args = List.map (fun _ -> ty_univ) args in
      let ps = SPred ([], create_psymbol (id_user s loc) args) in
      Hashtbl.add impl s ps;
      ps

let rec ty defenv impl env { e_loc = loc; e_node = n } = match n with
  | Eapp (aw,al) ->
      let ts = match find_ts ~loc impl env aw al with
        | SType ts -> ts
        | _ -> error ~loc TypeExpected in
      let tys = List.map (ty defenv impl env) al in
      ty_app ts tys
  | Edef (dw,al) ->
      let ts = match dw with
        | DT DTuniv -> ts_univ
        | DT DTint
        | DT DTrat
        | DT DTreal -> assert false (* TODO: arithmetic *)
        | DT DTdummy -> error ~loc InvalidDummy
        | DT DTtype | DT DTprop | DF _ | DP _ -> error ~loc TypeExpected in
      let tys = List.map (ty defenv impl env) al in
      ty_app ts tys
  | Evar v ->
      ty_var (find_tv ~loc impl env v)
  | Elet _ | Eite _ | Eqnt _ | Ebin _
  | Enot _ | Eequ _ | Edob _ | Enum _ -> error ~loc TypeExpected

(*
let rec term defenv impl env { e_loc = loc; e_node = n } = match n with
  | Eapp (aw,al) ->
      begin match find_fs ~loc impl env aw al with
        | SFunc (tvl,fs) ->
            let rec args tvm tvl al = match tvl,al with
              | (tv::tvl),(a::al) ->
                  let ty = ty defenv impl env a in
                  let tvm = Mtv.add tv ty tvm in
                  args tvm tvl al
              | [],al ->
                  (* TODO: type checking + dummies *)
                  let ty = option_map (ty_inst tvm) fs.ls_value in
                  let tl = List.map (term defenv impl env) al in
                  t_app fs tl ty
              | _ -> error ~loc BadArity
            in
            args Mtv.empty tvl al
        | SletF (tvl,vl,e) ->
            let rec args tvm vm tvl vl al = match tvl,vl,al with
              | (tv::tvl),_,(a::al) ->
                  let ty = ty defenv impl env a in
                  let tvm = Mtv.add tv ty tvm in
                  args tvm vm tvl vl al
              | _,(v::vl),(a::al) ->
                  let t = term defenv impl env a in
                  let vm = Mvs.add v t vm in
                  args tvm vm tvl vl al
              | [],[],[] ->
                  t_ty_subst tvm vm e
              | _ -> error ~loc BadArity
            in
            args Mtv.empty Mvs.empty tvl vl al
        | SVar v ->
            t_var v
        | _ -> error ~loc TermExpected
      end
  | Edef (dw,al) ->
      let fs = match dw with
        | DF _ -> assert false (* TODO: arithmetic *)
        | DT DTdummy -> error ~loc InvalidDummy
        | DT _ | DP _ -> error ~loc TermExpected in
      let tl = List.map (term defenv impl env) al in
      t_app_infer fs tl
  | Evar v ->
      t_var (find_vs ~loc impl env v)
  | Edob _ ->
      (* TODO: distinct objects *)
      assert false
  | Enum _ ->
      (* TODO: arithmetic *)
      assert false
  | Elet (def,e) ->
  | Eite (cn,th,el) ->
      let cn = fmla defenv impl env cn in
      let th = term defenv impl env th in
      let el = term defenv impl env el in
      t_if cn th el
  | Eqnt _ | Ebin _ | Enot _ | Eequ _ -> error ~loc TermExpected
*)

let typecheck _env _path _ast = Mstr.empty

