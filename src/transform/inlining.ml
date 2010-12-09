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
open Term
open Decl
open Task

type env = { fs : (vsymbol list * term) Mls.t;
             ps : (vsymbol list * fmla) Mls.t}

let empty_env = { fs = Mls.empty;
                  ps = Mls.empty}
open Format
(*
let print_env fmt env =
  let print_map iter pterm pfs = Pp.print_iter2 iter Pp.newline Pp.comma pfs
    (Pp.print_pair (Pp.print_list Pp.comma Pretty.print_vsymbol) pterm) in
  fprintf fmt "fs:@[<hov>%a@]@\nps:@[<hov>%a@]@\n"
    (print_map Mls.iter Pretty.print_term Pretty.print_lsymbol) env.fs
    (print_map Mls.iter Pretty.print_fmla Pretty.print_lsymbol) env.ps
*)
let rec replacet env t =
  let t = substt env t in
  match t.t_node with
    | Tapp (fs,tl) ->
        begin try
          let (vs,t) = Mls.find fs env.fs in
          let add (mt,mv) x y =
            (Ty.ty_match mt x.vs_ty y.t_ty, Mvs.add x y mv)
          in
          let (mt,mv) = List.fold_left2 add (Ty.Mtv.empty, Mvs.empty) vs tl in
          let mt = Ty.ty_match mt (of_option fs.ls_value) t.t_ty  in
          t_ty_subst mt mv t
        with Not_found -> t end
    | _ -> t

and replacep env f =
  let f = substp env f in
  match f.f_node with
    | Fapp (ps,tl) ->
        begin try
          let (vs,f) = Mls.find ps env.ps in
          let add (mt,mv) x y =
            (Ty.ty_match mt x.vs_ty y.t_ty, Mvs.add x y mv)
          in
          let (mt,mv) = List.fold_left2 add (Ty.Mtv.empty, Mvs.empty) vs tl in
          f_ty_subst mt mv f
        with Not_found -> f end
    | _ -> f

and substt env d = t_map (replacet env) (replacep env) d
and substp env d = f_map (replacet env) (replacep env) d

let addfs env ls vs t = {env with fs = Mls.add ls (vs,t) env.fs}
let addps env ls vs f = {env with ps = Mls.add ls (vs,f) env.ps}

let fold notdeft notdeff notls d (env, task) =
(*  Format.printf "I see : %a@\n%a@\n" Pretty.print_decl d print_env env;*)
  match d.d_node with
    | Dlogic [ls,ld] when not (notls ls) -> begin
        match ld with
          | None -> env,add_decl task d
          | Some ld ->
              let vs,e = open_ls_defn ld in
              match e with
                | Term t ->
                    let t = replacet env t in
                    if notdeft t || t_s_any ffalse (ls_equal ls) t
                    then env, add_decl task
                      (create_logic_decl [make_fs_defn ls vs t])
                    else (addfs env ls vs t),task
                | Fmla f ->
                    let f = replacep env f in
                    if notdeff f || f_s_any ffalse (ls_equal ls) f
                    then env, add_decl task
                      (create_logic_decl [make_ps_defn ls vs f])
                    else (addps env ls vs f),task
      end
    | Dind dl ->
        env, add_decl task (create_ind_decl
          (List.map (fun (ps,fmlal) -> ps, List.map
            (fun (pr,f) -> pr, replacep env f) fmlal) dl))
    | Dlogic dl ->
        env,
        add_decl task (create_logic_decl
           (List.map (fun (ls,ld) -> match ld with
              | None -> ls, None
              | Some ld ->
                let vs,e = open_ls_defn ld in
                let e = e_map (replacet env) (replacep env) e in
                make_ls_defn ls vs e) dl))
    | Dtype _ -> env,add_decl task d
    | Dprop (k,pr,f) ->
        env,add_decl task (create_prop_decl k pr (replacep env f))

let fold notdeft notdeff notls task0 (env, task) =
  match task0.task_decl with
    | { Theory.td_node = Theory.Decl d } ->
        fold notdeft notdeff notls d (env, task)
    | td -> env, add_tdecl task td

let meta = Theory.register_meta "inline : no" [Theory.MTlsymbol]

let t ?(use_meta=true) ~notdeft ~notdeff ~notls =
  let trans notls =
    Trans.fold_map (fold notdeft notdeff notls) empty_env None in
  if use_meta then
    Trans.on_meta meta (fun ml ->
      let sls = List.fold_left (fun acc e ->
        match e with
          | [Theory.MAls ls] -> Sls.add ls acc
          |_ -> assert false) Sls.empty ml in
      let notls ls = Sls.mem ls sls || notls ls in
      trans notls)
  else trans notls

(*
let fold_on_logic f task env =
  match task.Task.task_decl with
    | { Theory.td_node = Theory.Decl d } ->
        begin
          match d.d_node with
            | Dlogic dl ->
                List.fold_left
                  (fun acc (ls,ld) -> f ls ld acc)
                  env dl
            | _ -> env
        end
    | _ -> env
*)

let get_goal task =
  match task.Task.task_decl with
    | { Theory.td_node = Theory.Decl d } ->
        begin
          match d.d_node with
            | Dprop(Pgoal,_pr,f) ->
                begin
                  match f.f_node with
                    | Fapp(ps,_tl) ->
                        try
                          match
                            (Mid.find ps.ls_name task.Task.task_known).d_node
                          with
                            | Dlogic dl ->
                                let def = List.assoc ps dl in
                                begin
                                  match def with
                                    | Some _def -> assert false (* TODO *)
                                    | None ->
                                        Printer.unsupportedFmla f "has no definition"
                                end
                            | Dind _ ->
                                Printer.unsupportedFmla f
                                  "inductive def cannot be inlined"
                            | Dprop _ | Dtype _ -> assert false
                        with Not_found -> assert false
                end
            | _ -> assert false
        end
    | _ -> assert false

let all = t ~use_meta:true ~notdeft:ffalse ~notdeff:ffalse ~notls:ffalse

(** TODO : restrict to linear substitution,
    ie each variable appear exactly once *)
let trivial = t
  ~use_meta:true
  ~notdeft:(fun m -> match m.t_node with
                    | Tconst _ | Tvar _ -> false
                    | Tapp (_,tl) when List.for_all
                        (fun m -> match m.t_node with
                           | Tvar _ -> true
                           | _ -> false) tl -> false
                    | _ -> true )
  ~notdeff:(fun m -> match m.f_node with
                    | Ftrue | Ffalse -> false
                    | Fapp (_,tl) when List.for_all
                        (fun m -> match m.t_node with
                           | Tvar _ -> true
                           | _ -> false) tl -> false
                    | _ -> true)
  ~notls:ffalse

let () =
  Trans.register_transform "inline_all" all;
  Trans.register_transform "inline_trivial" trivial

