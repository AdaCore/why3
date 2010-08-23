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

type tenv = {kept          : Sty.t;
             specials      : lconv Hty.t;
             trans_lsymbol : lsymbol Hls.t;
             trans_tsymbol : tysymbol Hts.t}
(* trans_lsymbol ne depend pour l'instant pas du but, 
       comme specials_type ne depend pas*)
    

(* Translate a type to a type without kept *)
let rec ty_of_ty tenv ty =
  match ty.ty_node with
    | Tyapp (ts,[]) ->
      let tts = try Hts.find tenv.trans_tsymbol ts 
        with Not_found -> ts in
      ty_app tts []
    | Tyapp (ts,l) -> ty_app ts (List.map (ty_of_ty tenv) l)
    | Tyvar _ -> ty

let load_prelude kept env =
  let task = None in
  let specials = Hty.create 17 in
  let builtin = Env.find_theory env why_filename "Bridge" in
  let type_t = Theory.ns_find_ts builtin.th_export ["t"] in
  let type_tb = Theory.ns_find_ts builtin.th_export ["tb"] in
  let logic_tb2t = Theory.ns_find_ls builtin.th_export ["tb2t"] in
  let logic_t2tb = Theory.ns_find_ls builtin.th_export ["t2tb"] in
  let trans_tsymbol = Hts.create 17 in
  let tenv_tmp =
    { kept = Sty.empty;
      specials = specials;
      trans_lsymbol = Hls.create 17;
      trans_tsymbol = trans_tsymbol} in
  let clone_builtin ts (task,sty) =
    let ty = match ts.ts_def with 
      | Some ty -> ty 
      | None -> try ty_app ts [] with BadTypeArity(_,_,_) -> 
        failwith "kept without definition must be constant"  in
    let add_ts task ts = add_ty_decl task [ts,Tabstract] in
    let task = ty_s_fold add_ts task ty in
    let is_constant = 
      match ty.ty_node with 
        | Tyapp (_,[]) -> true
        | _ -> false in
    let ts_head =
      match ty.ty_node with 
        | Tyapp (ts,_) -> ts
        | _ -> assert false in
    let task = add_ts task ts in
    let tb = create_tysymbol (id_clone ts_head.ts_name) []
      (if is_constant then None else Some (ty_of_ty tenv_tmp ty)) in
    let task = add_ts task tb in
    let tytb = ty_app tb [] in 
    let tb2t = create_fsymbol (id_clone logic_tb2t.ls_name) [tytb] ty in
    let t2tb = create_fsymbol (id_clone logic_t2tb.ls_name) [ty] tytb in
    let task = add_logic_decl task [tb2t,None] in
    let task = add_logic_decl task [t2tb,None] in
    let th_inst = create_inst 
      ~ts:[type_t,ts;type_tb,tb]
      ~ls:[logic_t2tb,t2tb;logic_tb2t,tb2t] ~lemma:[] ~goal:[] in
    let task = Task.clone_export task builtin th_inst in
    let lconv = { tb2t = tb2t; t2tb = t2tb; tb = ty_app tb []} in
    (* Add the constant sort to trans_tsymbol *)
    if is_constant then Hts.add trans_tsymbol ts_head tb;
    Hty.add specials ty lconv;
    task,Sty.add ty sty in
  let task,kept = Sts.fold clone_builtin kept (task,Sty.empty) in
  task, { tenv_tmp with kept = kept}



(* Translate with the previous function except when the type is specials *)
let conv_ty tenv ty =
  if Hty.mem tenv.specials ty then ty else ty_of_ty tenv ty

(* let is_kept tenv ts = ts.ts_args = [] && Sty.mem ts tenv.kept *)

(* Convert a variable *)
let conv_vs tenv vs =
  let ty = conv_ty tenv vs.vs_ty in
  if ty_equal ty vs.vs_ty then vs else
      create_vsymbol (id_dup vs.vs_name) ty

(* Convert a logic symbols to the encoded one *)
let conv_ls tenv ls = 
  if ls_equal ls ps_equ
  then ls
  else
    let tyl = List.map (conv_ty tenv) ls.ls_args in
    let ty_res = Util.option_map (conv_ty tenv) ls.ls_value in
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
      (* polymorph specials t2tb *)
      let tylconv = Hty.find tenv.specials tty in
      match t.t_node with
      | Tapp (fs,[t']) when ls_equal fs tylconv.tb2t -> t'
      | _ -> t_app tylconv.t2tb [t] tylconv.tb
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

let rec rewrite_term tenv vsvar t =
  (* Format.eprintf "@[<hov 2>Term : %a =>@\n@?" Pretty.print_term t; *)
  let fnT = rewrite_term tenv in
  let fnF = rewrite_fmla tenv in
  let t = match t.t_node with
    | Tvar vs -> Mvs.find vs vsvar
    | Tapp(p,tl) ->
        let tl = List.map (fnT vsvar) tl in
        let p = Hls.find tenv.trans_lsymbol p in
        let tl = List.map2 (conv_arg tenv) tl p.ls_args in
        conv_res_app tenv p tl t.t_ty
    | Tlet (t1, b) -> 
        let u,t2,close = t_open_bound_cb b in
        let t1 = fnT vsvar t1 in
        let u' = conv_vs tenv u in
        let vsvar = Mvs.add u (t_var u') vsvar in
        let t2 = fnT vsvar t2 in
        t_let t1 (close u t2)
    | _ -> t_map (fnT vsvar) (fnF vsvar) t in
  (* Format.eprintf "@[<hov 2>Term : => %a : %a@\n@?" Pretty.print_term t *)
  (*   Pretty.print_ty t.t_ty; *)
    t

and rewrite_fmla tenv vsvar f =
  (* Format.eprintf "@[<hov 2>Fmla : %a =>@\n@?" Pretty.print_fmla f; *)
  let fnT = rewrite_term tenv in
  let fnF = rewrite_fmla tenv in
  match f.f_node with
    | Fapp(p, [t1;t2]) when ls_equal p ps_equ ->
        f_equ (fnT vsvar t1) (fnT vsvar t2)
    | Fapp(p, tl) -> 
        let tl = List.map (fnT vsvar) tl in
        let p = Hls.find tenv.trans_lsymbol p in
        let tl = List.map2 (conv_arg tenv) tl p.ls_args in
        f_app p tl
    | Fquant (q, b) ->
        let vl, tl, f1, close = f_open_quant_cb b in
        let conv_vs (vsvar,l) vs =
          let vs' = conv_vs tenv vs in
          Mvs.add vs (t_var vs') vsvar,vs'::l in
        let (vsvar,vl) = List.fold_left conv_vs (vsvar,[]) vl in
        let f1 = fnF vsvar f1 in 
        (* Ici un trigger qui ne match pas assez de variables 
           peut être généré *)
        let tl = tr_map (fnT vsvar) (fnF vsvar) tl in
        let vl = List.rev vl in
        f_quant q (close vl tl f1)
    | Flet (t1, b) ->
        let u,f2,close = f_open_bound_cb b in
        let t1 = fnT vsvar t1 in
        let u' = conv_vs tenv u in
        let vsvar = Mvs.add u (t_var u') vsvar in
        let f2 = fnF vsvar f2 in 
        f_let t1 (close u f2)
    | _ -> f_map (fnT vsvar) (fnF vsvar) f

let decl (tenv:tenv) d =
  (* let fnT = rewrite_term tenv in *)
  let fnF = rewrite_fmla tenv in
  match d.d_node with
    (* | Dtype [ts,Tabstract] when is_kept tenv ts ->  *)
    (*     tenv.clone_builtin ts *)
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
        let f = fnF Mvs.empty f in
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

