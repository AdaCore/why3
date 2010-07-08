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

(* This is a copy of encoding_decorate, it should be merged to it
   when it is done *)

open Util
open Ident
open Ty
open Term
open Task
open Theory
open Task
open Decl

let why_filename = ["transform" ; "encoding_decorate"]
let kept_tag = "encoding_decorate : kept"

(* From Encoding Polymorphism CADE07*)
type tenv = {query : Driver.driver_query;
             unsorted : ty;
             sort : lsymbol;
             real_to_int : lsymbol;
             trans_lsymbol : lsymbol Hls.t;
             trans_tsymbol : lsymbol Hts.t} 

let load_prelude query env =
  let prelude = Env.find_theory env why_filename "Prelude_mono" in
  let sort = Theory.ns_find_ls prelude.th_export ["sort"] in
  let int = Theory.ns_find_ls prelude.th_export ["int"] in
  let real_to_int = Theory.ns_find_ls prelude.th_export ["real_to_int"] in
  let task = None in
  let task = Task.use_export task prelude in
  let trans_tsymbol = Hts.create 17 in
  Hts.add trans_tsymbol Ty.ts_int int;
  task,
  { query = query;
    unsorted = ty_int;
    sort = sort;
    real_to_int = real_to_int;
    trans_lsymbol = Hls.create 17;
    trans_tsymbol = trans_tsymbol}

(* Translate a type to a term *)
let rec term_of_ty tenv tvar ty =
  match ty.ty_node with
    | Tyapp (ts,l) -> 
        let tts = Hts.find tenv.trans_tsymbol ts in
        t_app tts (List.map (term_of_ty tenv tvar) l) tenv.unsorted
    | Tyvar tv -> 
        t_var (try Htv.find tvar tv
              with Not_found -> 
                (let var = create_vsymbol 
                   (id_fresh ("tv"^tv.tv_name.id_string))
                  tenv.unsorted in
                 Htv.add tvar tv var;
                 var))
    
let sort_app tenv tvar t ty =
  let tty = term_of_ty tenv tvar ty in
  t_app tenv.sort [tty;t] tenv.unsorted

(* Convert a type at the right of an arrow *)
let conv_ty_neg tenv _ty = tenv.unsorted

(* Convert a type at the left of an arrow *)
let conv_ty_pos tenv _ty = tenv.unsorted

(* Convert a logic symbols to the encoded one *)
let conv_ls tenv ls = 
  if ls_equal ls ps_equ
  then ls
  else
    let tyl = List.map (conv_ty_neg tenv) ls.ls_args in
    let ty_res = Util.option_map (conv_ty_pos tenv) ls.ls_value in
    let preid = id_clone ls.ls_name in
    create_lsymbol preid tyl ty_res


let conv_ts tenv ts =
  let preid = id_clone ts.ts_name in
  let tyl = List.map (fun _ -> tenv.unsorted) ts.ts_args in
  create_fsymbol preid tyl tenv.unsorted

(* Convert the argument of a function from specials to deco or deco to
   specials if needed*)
let conv_arg _tenv _tvar t _ty = t

(* Convert to undeco or to a specials an application *)
let conv_res_app tenv tvar p tl ty = 
  let tty = Util.of_option p.ls_value in
  assert (ty_equal tty tenv.unsorted);
  let t = t_app p tl tenv.unsorted in
  sort_app tenv tvar t ty
  
let conv_vs tenv tvar (vsvar,acc) vs =
  let tres,vsres =
    let ty_res = conv_ty_pos tenv vs.vs_ty in
    let tty = term_of_ty tenv tvar vs.vs_ty in
    let vsres = (create_vsymbol (id_clone vs.vs_name) ty_res) in
    let t = t_var vsres in 
    t_app tenv.sort [tty;t] tenv.unsorted, vsres in
  (Mvs.add vs tres vsvar,vsres::acc)

let conv_vs_let tenv vsvar vs =
  let tres,vsres =
    let ty_res = conv_ty_neg tenv vs.vs_ty in
    if ty_equal ty_res vs.vs_ty then
      t_var vs,vs
    else 
      let vsres = (create_vsymbol (id_clone vs.vs_name) ty_res) in
      let t = t_var vsres in 
      t, vsres in              
  (Mvs.add vs tres vsvar,vsres)


let rec rewrite_term tenv tvar vsvar t =
  (*Format.eprintf "@[<hov 2>Term : %a =>@\n@?" Pretty.print_term t;*)
  let fnT = rewrite_term tenv tvar in
  let fnF = rewrite_fmla tenv tvar vsvar in
  match t.t_node with
    | Tconst ConstInt _ -> sort_app tenv tvar t t.t_ty
    | Tconst ConstReal _ -> 
      let t2 = t_app tenv.real_to_int [t] tenv.unsorted in
      sort_app tenv tvar t2 t.t_ty
    | Tvar x -> Mvs.find x vsvar
    | Tapp(p,tl) ->
        let tl = List.map (fnT vsvar) tl in
        let p = Hls.find tenv.trans_lsymbol p in
        let tl = List.map2 (conv_arg tenv tvar) tl p.ls_args in
        conv_res_app tenv tvar p tl t.t_ty
    | Tif (f, t1, t2) -> 
        t_if (fnF f) (fnT vsvar t1) (fnT vsvar t2)
    | Tlet (t1, b) -> let u,t2 = t_open_bound b in
      let (vsvar',u) = conv_vs_let tenv vsvar u in
      let t1' = fnT vsvar t1 in let t2' = fnT vsvar' t2 in
      if t_equal t1' t1 && t_equal t2' t2 then t else t_let u t1' t2'
    | Tcase _ | Teps _ | Tbvar _ ->
        Register.unsupportedTerm t
          "Encoding decorate : I can't encode this term"

and rewrite_fmla tenv tvar vsvar f =
(*  Format.eprintf "@[<hov 2>Fmla : %a =>@\n@?" Pretty.print_fmla f;*)
  let fnT = rewrite_term tenv tvar vsvar in
  let fnF = rewrite_fmla tenv tvar in
  match f.f_node with
    | Fapp(p, tl) when ls_equal p ps_equ ->
      let tl = List.map fnT tl in
      let ty = tenv.unsorted in
      let tl = List.map2 (conv_arg tenv tvar) tl [ty;ty] in
      f_app p tl
    | Fapp(p, tl) -> 
      let tl = List.map fnT tl in
      let p = Hls.find tenv.trans_lsymbol p in
      let tl = List.map2 (conv_arg tenv tvar) tl p.ls_args in
      f_app p tl
    | Fquant (q, b) -> let vl, tl, f1 = f_open_quant b in
      let (vsvar',vl) = List.fold_left (conv_vs tenv tvar) (vsvar,[]) vl in
      let f1' = fnF vsvar' f1 in 
      (* Ici un trigger qui ne match pas assez de variables 
         peut être généré *)
      let tl = tr_map (rewrite_term tenv tvar vsvar') (fnF vsvar') tl in
        (*if f_equal f1' f1 &&  vsvar' == vsvar (*&& tr_equal tl' tl*) then f
        else *)
          let vl = List.rev vl in
          f_quant q vl tl f1'
    | Flet (t1, b) -> let u,f2 = f_open_bound b in
      let (vsvar,u) = conv_vs_let tenv vsvar u in
      let t1' = fnT t1 in let f2' = fnF vsvar f2 in
      assert (u.vs_ty == t1'.t_ty);
      (*if t_equal t1' t1 && f_equal f2' f2 then f else *)
        f_let u t1' f2'
    | _ -> f_map fnT (fnF vsvar) f

let is_kept ls = List.for_all (fun ty -> ty_equal ty_int ty) ls.ls_args
  && option_apply true (ty_equal ty_int) ls.ls_value

let decl (tenv:tenv) d =
  (* let fnT = rewrite_term tenv in *)
  let fnF = rewrite_fmla tenv in
  match d.d_node with
    | Dtype [ts,Tabstract] when ts_equal ts ts_int -> []
    | Dtype [ts,Tabstract] -> 
        let tty = 
          try 
            Hts.find tenv.trans_tsymbol ts 
          with Not_found -> 
            let tty = conv_ts tenv ts in
            Hts.add tenv.trans_tsymbol ts tty;
            tty in
        [create_decl (create_logic_decl [(tty,None)])]
    | Dtype _ -> Register.unsupportedDecl 
        d "encoding_decorate : I can work only on abstract\
            type which are not in recursive bloc."
    | Dlogic l ->
        let fn acc = function
          | _ls, Some _ -> 
              Register.unsupportedDecl 
                d "encoding_decorate : I can't encode definition. \
Perhaps you could use eliminate_definition"
          | ls1, None ->
            let ls2 = 
              try
                Hls.find tenv.trans_lsymbol ls1
              with Not_found -> conv_ls tenv ls1 in
            let acc = create_logic_decl [ls2,None] :: acc in
            let acc = match Driver.query_syntax tenv.query ls1.ls_name with
              | Some _ when is_kept ls1 -> 
                let make _ = create_vsymbol (id_fresh "x") ty_int in
                let vars = List.map make ls1.ls_args in
                let terms1 = List.map t_var vars in
                let tvar = Htv.create 0 in
                let terms2 = List.map 
                  (fun t -> sort_app tenv tvar t ty_int) terms1 in
                let fmla = 
                  match ls1.ls_value with
                    | None ->
                      let f1 = f_app ls1 terms1 in
                      let f2 = f_app ls2 terms2 in
                      f_iff f1 f2
                    | Some _ ->
                      let t1 = t_app ls1 terms1 ty_int in
                      let t2 = t_app ls2 terms2 ty_int in
                      f_equ t1 t2  in
                let fmla = f_forall vars [] fmla in
                let name = create_prsymbol (id_clone ls1.ls_name) in
                (create_prop_decl Paxiom name fmla)::d::acc
              | _ -> acc in
            Hls.replace tenv.trans_lsymbol ls1 ls2;
            acc in
        List.rev_map create_decl (List.fold_left fn [] l)
    | Dind _ -> Register.unsupportedDecl
        d "encoding_decorate : I can't work on inductive"
        (* let fn (pr,f) = pr, fnF f in *)
        (* let fn (ps,l) = ps, List.map fn l in *)
        (* [create_ind_decl (List.map fn l)] *)
    | Dprop (k,pr,f) ->
        let tvar = Htv.create 17 in
        let f = fnF tvar Mvs.empty f in
        let tvl = Htv.fold (fun _ tv acc -> tv::acc) tvar [] in
        let f = f_forall tvl [] f in
        [create_decl (create_prop_decl k pr f)]

(*
let decl tenv d =
  Format.eprintf "@[<hov 2>Decl : %a =>@\n@?" Pretty.print_decl d;
  let res = decl tenv d in
  Format.eprintf "%a@]@." (Pp.print_list Pp.newline Pretty.print_task_tdecl)
    res;
  res
*)

let t = Register.store_query 
  (fun query -> 
     let env = Driver.query_env query in
     let init_task,tenv = load_prelude query env in
     Trans.tdecl (decl tenv) init_task)

let () = Register.register_transform "encoding_decorate_mono" t
