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

open Ident
open Ty
open Term
open Task
open Theory
open Decl

let why_filename = ["transform" ; "encoding_decorate"]

(* From Encoding Polymorphism CADE07*)

module Prelude = 
struct
(*  let create_ty s = ty_app (create_tysymbol (id_fresh s) [] None) [] in
  let deco = create_ty "deco" in
  let undeco = create_ty "undeco" in
  let ty = create_ty "ty" in
  let csort = create_fsymbol (id_fresh "csort") [ty;undeco] deco in
*)

     
(*  let spec_conv ts =
    let name = ts.ts_name.id_short in
    let d2ty = create_fsymbol (id_fresh ("d2"^name)) [deco] (ty_app ts []) in
    let ty2u = create_fsymbol (id_fresh (name^"2u")) [(ty_app ts [])] undeco in
    let axiom = 
      
    let l = 
    List.fold_left (fun acc ty -> Sty.add ty acc) Sty.empty l
*)
end
  
type lconv = {d2t : lsymbol;
              t2u : lsymbol;
              tty : term}

type tenv = {specials : lconv Mty.t;
             deco : ty;
             undeco : ty;
             sort : lsymbol;
             ty : ty;
             trans_lsymbol : lsymbol Hls.t;
             trans_tsymbol : lsymbol Hts.t} 
    (* trans_lsymbol ne depend pour l'instant pas du but, 
       comme specials_type ne depend pas*)
    

let load_prelude env =
  let specials_type = [ts_int;ts_real] in
  let prelude = Env.find_theory env why_filename "Prelude" in
  let sort = Theory.ns_find_ls prelude.th_export ["sort"] in
  let tyty = ty_app (Theory.ns_find_ts prelude.th_export ["ty"]) [] in
  let deco = ty_app (Theory.ns_find_ts prelude.th_export ["deco"]) [] in
  let undeco = ty_app (Theory.ns_find_ts prelude.th_export ["undeco"]) [] in
  let task = None in
  let task = Task.use_export task prelude in
  let builtin = Env.find_theory env why_filename "Builtin" in
  let type_t = Theory.ns_find_ts builtin.th_export ["t"] in
  let logic_d2t = Theory.ns_find_ls builtin.th_export ["d2t"] in
  let logic_t2u = Theory.ns_find_ls builtin.th_export ["t2u"] in
  let logic_tty = Theory.ns_find_ls builtin.th_export ["tty"] in
  let trans_tsymbol = Hts.create 17 in
  let clone_builtin (task,spmap) ts =
    let name = ts.ts_name.id_short in
    let th_uc = create_theory (id_fresh ("encoding_decorate_for_"^name)) in
    let th_uc = use_export th_uc prelude in
    let ty = (ty_app ts []) in
    let add_fsymbol fs task =
      let decl = create_logic_decl [fs,None] in
      add_decl task decl in
    let tty = create_fsymbol (id_clone ts.ts_name) [] tyty in
    let d2ty = create_fsymbol (id_fresh ("d2"^name)) [deco]  ty in
    let ty2u = create_fsymbol (id_fresh (name^"2u")) [ty] undeco in
    let th_uc = add_fsymbol d2ty (add_fsymbol ty2u (add_fsymbol tty th_uc)) in
    let th_inst = create_inst 
      ~ts:[type_t,ts]
      ~ls:[logic_d2t,d2ty;logic_t2u,ty2u;logic_tty,tty]
      ~lemma:[] ~goal:[] in
    let lconv = { d2t = d2ty; t2u = ty2u; tty = t_app tty [] tyty} in
    let th_uc = Theory.clone_export th_uc builtin th_inst in
    let th = close_theory th_uc in
    let task = Task.use_export task th in
    Hts.add trans_tsymbol ts tty;
      task,Mty.add (ty_app ts []) lconv spmap
  in
  let task,specials = 
    List.fold_left clone_builtin (task,Mty.empty) specials_type in
  task,
  { specials = specials;
    deco = deco;
    undeco = undeco;
    ty = tyty;
    sort = sort;
    trans_lsymbol = Hls.create 17;
    trans_tsymbol = trans_tsymbol}


(* Translate a type to a term *)
let rec term_of_ty tenv tvar ty =
  match ty.ty_node with
    | Tyapp (ts,l) -> 
        let tts = Hts.find tenv.trans_tsymbol ts in
        t_app tts (List.map (term_of_ty tenv tvar) l) tenv.ty
    | Tyvar tv -> 
        t_var (try Htv.find tvar tv
              with Not_found -> 
                (let var = create_vsymbol (id_fresh ("tv"^tv.tv_name.id_short))
                  tenv.ty in
                 Htv.add tvar tv var;
                 var))
    
let sort_app tenv tvar t ty =
  let tty = term_of_ty tenv tvar ty in
  t_app tenv.sort [tty;t] tenv.deco

(* Convert a type at the right of an arrow *)
let conv_ty_neg tenv ty =
  if Mty.mem ty tenv.specials then
    ty
  else
    tenv.deco

(* Convert a type at the left of an arrow *)
let conv_ty_pos tenv ty =
  if Mty.mem ty tenv.specials then
    ty
  else
    tenv.undeco

(* Convert a logic symbols to the encoded one *)
let conv_ls tenv ls = 
  if ls == ps_equ
  then ls
  else
    let tyl = List.map (conv_ty_neg tenv) ls.ls_args in
    let ty_res = Util.option_map (conv_ty_pos tenv) ls.ls_value in
    if Util.option_eq (==) ty_res ls.ls_value 
      && List.for_all2 (==) tyl ls.ls_args 
    then ls
    else
      let preid = id_clone ls.ls_name in
      create_lsymbol preid tyl ty_res


let conv_ts tenv ts =
  let preid = id_clone ts.ts_name in
  let tyl = List.map (fun _ -> tenv.ty) ts.ts_args in
  create_fsymbol preid tyl tenv.ty

(* Convert the argument of a function from specials to deco or deco to
   specials if needed*)
let conv_arg tenv tvar t ty = 
  let tty = t.t_ty in
  if tty == ty then t else
    if ty == tenv.deco then
      let tylconv = Mty.find tty tenv.specials in
      let t = (t_app tylconv.t2u [t] tenv.undeco) in
      sort_app tenv tvar t tty
    else (* tty is tenv.deco *)
      begin
        assert (tty == tenv.deco);
        let tylconv = Mty.find ty tenv.specials in       
        t_app tylconv.d2t [t] ty
      end

(* Convert to undeco or to a specials an application *)
let conv_res_app tenv tvar p tl ty = 
  let tty = Util.of_option p.ls_value in
  if tty == ty then t_app p tl tty else
    begin
      assert (tty == tenv.undeco);
      let t = t_app p tl tenv.undeco in
      sort_app tenv tvar t ty
    end

let rec rewrite_term tenv tvar vsvar t =
  let fnT = rewrite_term tenv tvar vsvar in
  let fnF = rewrite_fmla tenv tvar vsvar in
  match t.t_node with
    | Tconst _ -> t
    | Tvar x -> Mvs.find x vsvar
    | Tapp(p,tl) ->
        let tl = List.map fnT tl in
        let p = Hls.find tenv.trans_lsymbol p in
        let tl = List.map2 (conv_arg tenv tvar) tl p.ls_args in
        conv_res_app tenv tvar p tl t.t_ty
    | Tif (f, t1, t2) -> 
        t_if (fnF f) (fnT t1) (fnT t2)
    | Tlet (t1, b) -> let u,t2 = t_open_bound b in
      let t1' = fnT t1 in let t2' = fnT t2 in
      if t1' == t1 && t2' == t2 then t else t_let u t1' t2'
    | Tcase _ | Teps _ | Tbvar _ ->
        Trans.unsupportedExpression
                 (Term t) "Encoding decorate : I can't encode this term"

and rewrite_fmla tenv tvar vsvar f =
  let fnT = rewrite_term tenv tvar vsvar in
  let fnF = rewrite_fmla tenv tvar in
  match f.f_node with
    | Fapp(p, tl) when p == ps_equ ->
        let tl = List.map fnT tl in
        begin
          match tl with
            | [a1;a2] ->
                let ty = 
                  if a1.t_ty == ty_int || a2.t_ty == ty_int 
                  then ty_int 
                  else tenv.deco in
                let tl = List.map2 (conv_arg tenv tvar) tl [ty;ty] in
                f_app p tl
            | _ -> assert false
        end
    | Fapp(p, tl) -> 
        let tl = List.map fnT tl in
        let p = Hls.find tenv.trans_lsymbol p in
        let tl = List.map2 (conv_arg tenv tvar) tl p.ls_args in
        f_app p tl
    | Fquant (q, b) -> let vl, _tl, f1 = f_open_quant b in
      let conv_vs (vsvar,acc) vs =
        let tres,vsres =
          let ty_res = conv_ty_pos tenv vs.vs_ty in
          if ty_res == vs.vs_ty then
            t_var vs,vs
          else 
            let tty = term_of_ty tenv tvar vs.vs_ty in
            let vsres = (create_vsymbol (id_clone vs.vs_name) ty_res) in
            let t = t_var vsres in 
            t_app tenv.sort [tty;t] tenv.deco, vsres in              
        (Mvs.add vs tres vsvar,vsres::acc) in
      let (vsvar,vl) = List.fold_left conv_vs (vsvar,[]) vl in
      let f1' = fnF vsvar f1 in 
      let tl' = [] (* TODO *) in
        if f1' == f1 (*&& tr_equal tl' tl*) then f
        else 
          let vl = List.rev vl in
          f_quant q vl tl' f1'
    | _ -> f_map fnT (fnF vsvar) f

let decl (tenv:tenv) d =
  (* let fnT = rewrite_term tenv in *)
  let fnF = rewrite_fmla tenv in
  match d.d_node with
    | Dtype [ts,Tabstract] -> 
        let tty = 
          try 
            Hts.find tenv.trans_tsymbol ts 
          with Not_found -> 
            let tty = conv_ts tenv ts in
            Hts.add tenv.trans_tsymbol ts tty;
            tty in
        [create_logic_decl [(tty,None)]]
    | Dtype _ -> Trans.unsupportedDeclaration 
        d "encoding_decorate : I can work only on abstract\
            type which are not in recursive bloc."
    | Dlogic l ->
        let fn = function
          | _ls, Some _ -> 
              Trans.unsupportedDeclaration 
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
        [create_logic_decl (List.map fn l)]
    | Dind _ -> Trans.unsupportedDeclaration
        d "encoding_decorate : I can't work on inductive"
        (* let fn (pr,f) = pr, fnF f in *)
        (* let fn (ps,l) = ps, List.map fn l in *)
        (* [create_ind_decl (List.map fn l)] *)
    | Dprop (k,pr,f) ->
        let tvar = Htv.create 17 in
        let f = fnF tvar Mvs.empty f in
        let tvl = Htv.fold (fun _ tv acc -> tv::acc) tvar [] in
        let f = f_forall tvl [] f in
        [create_prop_decl k pr f]

(*
let decl tenv d =
  Format.printf "@[<hov 2>Decl : %a =>@\n" Pretty.print_decl d;
  let res = decl tenv d in
  Format.printf "%a@]@." (Pp.print_list Pp.newline Pretty.print_decl) res;
  res
*)

let t = Register.store_env 
  (fun env -> 
     let init_task,tenv = load_prelude env in
     Trans.decl (decl tenv) init_task)

let () = Register.register_transform "encoding_decorate" t
