(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
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

open Util
open Ident
open Ty
open Term
open Task
open Theory
open Task
open Decl
open Encoding

let why_filename = ["transform" ; "encoding_decorate"]

(* From Encoding Polymorphism CADE07*)

type lconv = {tb2t : lsymbol;
              t2tb : lsymbol;
              tb   : ty}

type tenv = {kept          : Sts.t;
             clone_builtin : tysymbol -> Theory.tdecl list;
             specials      : lconv Hty.t;
             trans_lsymbol : lsymbol Hls.t;
             trans_tsymbol : tysymbol Hts.t}
(* trans_lsymbol ne depend pour l'instant pas du but, 
       comme specials_type ne depend pas*)
    

let load_prelude kept env =
  let task = None in
  let specials = Hty.create 17 in
  let builtin = Env.find_theory env why_filename "Bridge" in
  let type_t = Theory.ns_find_ts builtin.th_export ["t"] in
  let trans_tsymbol = Hts.create 17 in
  let clone_builtin ts =
    let name = ts.ts_name.id_string in
    let th_uc = create_theory (id_fresh ("bridge_for_"^name)) in
    let th_uc = 
      if ts_equal ts ts_int || ts_equal ts ts_real then th_uc
      else Theory.add_ty_decl th_uc [ts,Tabstract] in
    let th_inst = create_inst 
      ~ts:[type_t,ts] ~ls:[] ~lemma:[] ~goal:[] in
    let th_uc = Theory.clone_export th_uc builtin th_inst in
    let th = close_theory th_uc in
    let tb2t = ns_find_ls th.th_export ["tb2t"] in
    let t2tb = ns_find_ls th.th_export ["t2tb"] in
    let tb = ns_find_ts th.th_export ["tb"] in
    let lconv = { tb2t = tb2t; t2tb = t2tb; tb = ty_app tb []} in
    let task = Task.use_export None th in
    Hts.add trans_tsymbol ts tb;
    Hty.add specials (ty_app ts []) lconv;
    task_tdecls task in
  task,
  { kept = kept;
    clone_builtin = Wts.memoize 7 clone_builtin;
    specials = specials;
    trans_lsymbol = Hls.create 17;
    trans_tsymbol = trans_tsymbol}

(* Translate a type to a type without kept *)
let rec ty_of_ty tenv ty =
  match ty.ty_node with
    | Tyapp (ts,l) -> 
        let tts = try Hts.find tenv.trans_tsymbol ts 
          with Not_found -> ts in
        ty_app tts (List.map (ty_of_ty tenv) l)
    | Tyvar _ -> ty


(* Translate with the previous function except when the type is specials *)
let ty_of_ty_specials tenv ty =
  if Hty.mem tenv.specials ty then ty else ty_of_ty tenv ty

let is_kept tenv ts = ts.ts_args = [] && Sts.mem ts tenv.kept
    
(* Convert a logic symbols to the encoded one *)
let conv_ls tenv ls = 
  if ls_equal ls ps_equ
  then ls
  else
    let tyl = List.map (ty_of_ty_specials tenv) ls.ls_args in
    let ty_res = Util.option_map (ty_of_ty_specials tenv) ls.ls_value in
    if Util.option_eq ty_equal ty_res ls.ls_value 
      && List.for_all2 ty_equal tyl ls.ls_args 
    then ls
    else
      let preid = id_clone ls.ls_name in
      create_lsymbol preid tyl ty_res

(* Convert the argument of a function use the bridge if needed*)
let conv_arg tenv t aty = 
  let tty = t.t_ty in
  if ty_equal tty aty then t else
    try
      (* tb2t *)
      let tylconv = Hty.find tenv.specials aty in
      t_app tylconv.tb2t [t] aty
    with Not_found ->
      try
        (* polymorph specials t2tb *)
        let tylconv = Hty.find tenv.specials tty in
        t_app tylconv.t2tb [t] tylconv.tb
      with Not_found ->
        (* polymorph not specials *)
        t

(* Convert with a bridge an application if needed *)
let conv_res_app tenv p tl tty = 
  try
    (* tty is a special value *)
    let tylconv = Hty.find tenv.specials tty in
    let vty = Util.of_option p.ls_value in
    if ty_equal vty tty then (* vty too *) t_app p tl tty
    else
      (* p is polymorph *)
      let t = t_app p tl tylconv.tb in
      t_app tylconv.tb2t [t] tty
  with Not_found ->
    let tty = ty_of_ty tenv tty in
    t_app p tl tty

let rec rewrite_term tenv t =
  (*Format.eprintf "@[<hov 2>Term : %a =>@\n@?" Pretty.print_term t;*)
  let fnT = rewrite_term tenv in
  let fnF = rewrite_fmla tenv in
  match t.t_node with
    | Tapp(p,tl) ->
        let tl = List.map fnT tl in
        let p = Hls.find tenv.trans_lsymbol p in
        let tl = List.map2 (conv_arg tenv) tl p.ls_args in
        conv_res_app tenv p tl t.t_ty
    | _ -> t_map fnT fnF t

and rewrite_fmla tenv f =
  (* Format.eprintf "@[<hov 2>Fmla : %a =>@\n@?" Pretty.print_fmla f; *)
  let fnT = rewrite_term tenv in
  let fnF = rewrite_fmla tenv in
  match f.f_node with
    | Fapp(p, [t1;t2]) when ls_equal p ps_equ ->
        f_equ (fnT t1) (fnT t2)
    | Fapp(p, tl) -> 
        let tl = List.map fnT tl in
        let p = Hls.find tenv.trans_lsymbol p in
        let tl = List.map2 (conv_arg tenv) tl p.ls_args in
        f_app p tl
    | _ -> f_map fnT fnF f

let decl (tenv:tenv) d =
  (* let fnT = rewrite_term tenv in *)
  let fnF = rewrite_fmla tenv in
  match d.d_node with
    | Dtype [ts,Tabstract] when is_kept tenv ts -> 
        tenv.clone_builtin ts
    | Dtype [_,Tabstract] -> [create_decl d]
    | Dtype _ -> Printer.unsupportedDecl 
        d "encoding_decorate : I can work only on abstract \
            type which are not in recursive bloc."
    | Dlogic l ->
        let fn = function
          | _ls, Some _ -> 
              Printer.unsupportedDecl 
                d "encoding_decorate : I can't encode definition. \
                    Perhaps you could use eliminate_definition"
          | ls, None ->
              try
                let ls = Hls.find tenv.trans_lsymbol ls in
                ls,None
              with Not_found ->
                let ls_conv = conv_ls tenv ls in
                Hls.add tenv.trans_lsymbol ls ls_conv;
                ls_conv,None in
        [create_decl (create_logic_decl (List.map fn l))]
    | Dind _ -> Printer.unsupportedDecl
        d "encoding_decorate : I can't work on inductive"
        (* let fn (pr,f) = pr, fnF f in *)
        (* let fn (ps,l) = ps, List.map fn l in *)
        (* [create_ind_decl (List.map fn l)] *)
    | Dprop (k,pr,f) ->
        let f = fnF f in
        [create_decl (create_prop_decl k pr f)]

(*
let decl tenv d =
  Format.eprintf "@[<hov 2>Decl : %a =>@\n@?" Pretty.print_decl d;
  let res = decl tenv d in
  Format.eprintf "%a@]@." (Pp.print_list Pp.newline Pretty.print_task_tdecl)
    res;
  res
*)

let t env = Trans.on_meta meta_kept (fun tds ->
  let s = Task.find_tagged_ts meta_kept tds Sts.empty in
  let init_task,tenv = load_prelude s env in
  Trans.tdecl (decl tenv) init_task)

let () = register_enco_kept "bridge" t

