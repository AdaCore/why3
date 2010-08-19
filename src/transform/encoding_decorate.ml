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

type tenv = {kept : Sts.t;
             keptty : Sty.t;
             deco : ty;
             undeco : ty;
             sort : lsymbol;
             ty : ty;
             trans_lsymbol : lsymbol Hls.t;
             trans_tsymbol : lsymbol Hts.t;
             trans_consts   : lsymbol Hterm.t} 
    (* trans_lsymbol ne depend pour l'instant pas du but, 
       comme specials_type ne depend pas*)
    

let load_prelude kept env =
  let prelude = Env.find_theory env why_filename "Prelude" in
  let sort = Theory.ns_find_ls prelude.th_export ["sort"] in
  let tyty = ty_app (Theory.ns_find_ts prelude.th_export ["ty"]) [] in
  let deco = ty_app (Theory.ns_find_ts prelude.th_export ["deco"]) [] in
  let undeco = ty_app (Theory.ns_find_ts prelude.th_export ["undeco"]) [] in
  let task = None in
  let task = Task.use_export task prelude in
  let trans_tsymbol = Hts.create 17 in
  let add ts sty = match ts.ts_def with
    | Some ty -> Sty.add ty sty
    | None -> Sty.add (ty_app ts []) sty in
  let kepty = Sts.fold add kept Sty.empty in
  let add_ts sts ts = Sts.add ts sts in
  let add_ts ty sts = ty_s_fold add_ts sts ty in
  let kept = Sty.fold add_ts kepty Sts.empty in
  task,
  { kept = kept;
    keptty = kepty;
    deco = deco;
    undeco = undeco;
    ty = tyty;
    sort = sort;
    trans_lsymbol = Hls.create 17;
    trans_tsymbol = trans_tsymbol;
    trans_consts = Hterm.create 3;
  }

(* Translate a type to a term *)
let rec term_of_ty tenv tvar ty =
  match ty.ty_node with
    | Tyapp (ts,l) -> 
        let tts = Hts.find tenv.trans_tsymbol ts in
        t_app tts (List.map (term_of_ty tenv tvar) l) tenv.ty
    | Tyvar tv -> 
        t_var (try Htv.find tvar tv
              with Not_found -> 
                (let var = create_vsymbol 
                   (id_fresh ("tv"^tv.tv_name.id_string))
                  tenv.ty in
                 Htv.add tvar tv var;
                 var))
    
let sort_app tenv tvar t ty =
  let tty = term_of_ty tenv tvar ty in
  t_app tenv.sort [tty;t] tenv.deco

(* Convert a type at the right of an arrow *)
let conv_ty_neg tenv ty =
  if Sty.mem ty tenv.keptty then
    ty
  else
    tenv.deco

(* Convert a type at the left of an arrow *)
let conv_ty_pos tenv ty =
  if Sty.mem ty tenv.keptty then
    ty
  else
    tenv.undeco

(* Convert a logic symbols to the encoded one *)
let conv_ls tenv ls = 
  if ls_equal ls ps_equ
  then ls
  else
    let tyl = List.map (conv_ty_neg tenv) ls.ls_args in
    let ty_res = Util.option_map (conv_ty_pos tenv) ls.ls_value in
    if Util.option_eq ty_equal ty_res ls.ls_value 
      && List.for_all2 ty_equal tyl ls.ls_args 
    then ls
    else
      let preid = id_clone ls.ls_name in
      create_lsymbol preid tyl ty_res


let conv_ts tenv ts =
  let preid = id_clone ts.ts_name in
  let tyl = List.map (fun _ -> tenv.ty) ts.ts_args in
  create_fsymbol preid tyl tenv.ty

(* Convert to undeco or to a specials an application *)
let conv_res_app tenv tvar t ty =
  let tty = t.t_ty in
  if Sty.mem tty tenv.keptty then t 
  else sort_app tenv tvar t ty

let conv_vs tenv tvar (vsvar,acc) vs =
  let tres,vsres =
    let ty_res = conv_ty_pos tenv vs.vs_ty in
    if ty_equal ty_res vs.vs_ty then
      t_var vs,vs
    else 
      let tty = term_of_ty tenv tvar vs.vs_ty in
      let vsres = (create_vsymbol (id_clone vs.vs_name) ty_res) in
      let t = t_var vsres in 
      t_app tenv.sort [tty;t] tenv.deco, vsres in
  (Mvs.add vs tres vsvar,vsres::acc)

let conv_vs_let vsvar vs ty_res =
  let tres,vsres =
    (* let ty_res = conv_ty_neg tenv vs.vs_ty in *)
    if ty_equal ty_res vs.vs_ty then
      t_var vs,vs
    else 
      let vsres = (create_vsymbol (id_clone vs.vs_name) ty_res) in
      let t = t_var vsres in 
      t, vsres in              
  (Mvs.add vs tres vsvar,vsres)

let conv_const tenv consts tvar t =
  let fs = 
    try Hterm.find tenv.trans_consts t
    with Not_found -> 
      let s = "const_"^Pp.string_of Pretty.print_term t in
      let fs = create_fsymbol (id_fresh s) [] tenv.undeco in
      Hterm.add tenv.trans_consts t fs; fs in
  Hls.replace consts fs ();
  conv_res_app tenv tvar (t_app fs [] tenv.undeco) t.t_ty

let rec rewrite_term tenv consts tvar vsvar t =
  (* Format.eprintf "@[<hov 3>Term : %a : %a =>@\n@?" *)
  (*   Pretty.print_term t Pretty.print_ty t.t_ty; *)
  let fnT = rewrite_term tenv consts tvar in
  let fnF = rewrite_fmla tenv consts tvar vsvar in
  match t.t_node with
    | Tconst _ when Sty.mem t.t_ty tenv.keptty -> t
    | Tconst _ -> conv_const tenv consts tvar t
    | Tvar x -> Mvs.find x vsvar
    | Tapp(p,tl) ->
        let tl = List.map (fnT vsvar) tl in
        let p = Hls.find tenv.trans_lsymbol p in
        let t' = t_app_infer p tl in
        conv_res_app tenv tvar t' t.t_ty
    | Tif (f, t1, t2) -> 
        t_if (fnF f) (fnT vsvar t1) (fnT vsvar t2)
    | Tlet (t1, b) -> 
        let u,t2,close = t_open_bound_cb b in
        let t1 = fnT vsvar t1 in
        let (vsvar,u) = conv_vs_let vsvar u t1.t_ty in
        let t2 = fnT vsvar t2 in
        t_let t1 (close u t2)
    | Tcase _ | Teps _ | Tbvar _ ->
        Printer.unsupportedTerm t
          "Encoding decorate : I can't encode this term"

and rewrite_fmla tenv consts tvar vsvar f =
  (* Format.eprintf "@[<hov>Fmla : %a =>@]@." Pretty.print_fmla f; *)
  let fnT = rewrite_term tenv consts tvar vsvar in
  let fnF = rewrite_fmla tenv consts tvar in
  match f.f_node with
    | Fapp(p, [a1;a2]) when ls_equal p ps_equ ->
        let a1 = fnT a1 in let a2 = fnT a2 in
        (* Format.eprintf "@[<hov>%a : %a = %a : %a@]@." *)
        (*   Pretty.print_term a1 Pretty.print_ty a1.t_ty *)
        (*   Pretty.print_term a2 Pretty.print_ty a2.t_ty; *)
        f_equ a1 a2
    | Fapp(p, tl) -> 
        let tl = List.map fnT tl in
        let p = Hls.find tenv.trans_lsymbol p in
        f_app p tl
    | Fquant (q, b) ->
        let vl, tl, f1, close = f_open_quant_cb b in
        let (vsvar,vl) = List.fold_left (conv_vs tenv tvar) (vsvar,[]) vl in
        let f1 = fnF vsvar f1 in 
        (* Ici un trigger qui ne match pas assez de variables 
           peut être généré *)
        let tl = tr_map (rewrite_term tenv consts tvar vsvar) (fnF vsvar) tl in
        let vl = List.rev vl in
        f_quant q (close vl tl f1)
    | Flet (t1, b) ->
        let u,f2,close = f_open_bound_cb b in
        let t1 = fnT t1 in
        let (vsvar,u) = conv_vs_let vsvar u t1.t_ty in
        let f2 = fnF vsvar f2 in 
        f_let t1 (close u f2)
    | _ -> f_map fnT (fnF vsvar) f

let decl (tenv:tenv) d =
  (* let fnT = rewrite_term tenv in *)
  let fnF = rewrite_fmla tenv in
  match d.d_node with
    | Dtype [{ts_def = Some _},_] -> []
    | Dtype [ts,Tabstract] -> 
        let tty = 
          try 
            Hts.find tenv.trans_tsymbol ts 
          with Not_found -> 
            let tty = conv_ts tenv ts in
            Hts.add tenv.trans_tsymbol ts tty;
            tty in
        let td = [create_decl (create_logic_decl [(tty,None)])] in
        if Sts.mem ts tenv.kept then (create_decl d)::td else td
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
        let tvar = Htv.create 17 in
        let consts = Hls.create 3 in
        let f = fnF consts tvar Mvs.empty f in
        let tvl = Htv.fold (fun _ tv acc -> tv::acc) tvar [] in
        let f = f_forall_close tvl [] f in
        let add fs () acc = (create_decl (create_logic_decl [fs,None]))::acc in
        Hls.fold add consts [create_decl (create_prop_decl k pr f)]


(* let decl tenv d = *)
(*   Format.eprintf "@[<hov 2>Decl : %a =>@\n@?" Pretty.print_decl d; *)
(*   let res = decl tenv d in *)
(*   Format.eprintf "%a@]@." (Pp.print_list Pp.newline Pretty.print_tdecl) *)
(*     res; *)
(*   res *)

let t env = Trans.on_meta meta_kept (fun tds ->
  let s = Task.find_tagged_ts meta_kept tds Sts.empty in
  let init_task,tenv = load_prelude s env in
  Trans.tdecl (decl tenv) init_task)

let () = register_enco_poly "decorate" t
