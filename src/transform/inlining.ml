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
open Term
open Termlib
open Theory
open Context

let ttrue _ = true
let ffalse _ = false

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
          let m = List.fold_left2 (fun acc x y -> Mvs.add x y acc)
            Mvs.empty vs tl in
          t_subst m t
        with Not_found -> t end
    | _ -> t

and replacep env f = 
  let f = substp env f in
  match f.f_node with
    | Fapp (ps,tl) ->
        begin try 
          let (vs,t) = Mls.find ps env.ps in
          let m = List.fold_left2 (fun acc x y -> Mvs.add x y acc) 
            Mvs.empty vs tl in
          f_subst m f
        with Not_found -> f end
    | _ -> f

and substt env d = t_map (replacet env) (replacep env) d
and substp env d = f_map (replacet env) (replacep env) d

let fold isnotinlinedt isnotinlinedf ctxt0 (env, ctxt) = 
(*  Format.printf "I see : %a@\n%a@\n" Pretty.print_decl d print_env env;*)
  let d = ctxt0.ctxt_decl in
  match d.d_node with
    | Dlogic [ls,ld] -> begin
        match ld with
          | None -> env,add_decl ctxt d
          | Some ld ->
              let vs,e = open_ls_defn ld in
              match e with
                | Term t ->
                    let t = replacet env t in
                    if t_s_any ffalse ((==) ls) t || isnotinlinedt t
                    then env, add_decl ctxt 
                      (create_logic_decl [make_fs_defn ls vs t])
                    else {env with fs = Mls.add ls (vs,t) env.fs},ctxt
                | Fmla f -> 
                    let f = replacep env f in
                    if f_s_any ffalse ((==) ls) f || isnotinlinedf f
                    then env, add_decl ctxt 
                      (create_logic_decl [make_ps_defn ls vs f])
                    else {env with ps = Mls.add ls (vs,f) env.ps},ctxt
      end
    | Dind dl ->
        env, add_decl ctxt (create_ind_decl 
          (List.map (fun (ps,fmlal) -> ps, List.map 
            (fun (pr,f) -> pr, replacep env f) fmlal) dl))
    | Dlogic dl -> 
        env,
        add_decl ctxt (create_logic_decl 
           (List.map (fun (ls,ld) -> match ld with 
              | None -> ls, None
              | Some ld ->
                let vs,e = open_ls_defn ld in
                let e = e_map (replacet env) (replacep env) e in
                make_ls_defn ls vs e) dl))
    | Dtype dl -> env,add_decl ctxt d
    | Dprop (k,pr,f) -> 
        env,add_decl ctxt (create_prop_decl k pr (replacep env f))
    | Duse _ | Dclone _ -> env,add_decl ctxt d
        
let t ~isnotinlinedt ~isnotinlinedf = 
  Trans.fold_map (fold isnotinlinedt isnotinlinedf) (fun _ -> empty_env)

let all () = t ~isnotinlinedt:(fun _ -> false) ~isnotinlinedf:(fun _ -> false)

let trivial () = t 
  ~isnotinlinedt:(fun m -> match m.t_node with
                    | Tconst _ | Tvar _ -> false
                    | Tapp (ls,tl) when List.for_all 
                        (fun m -> match m.t_node with 
                           | Tvar _ -> true 
                           | _ -> false) tl -> false
                    | _ -> true )
  ~isnotinlinedf:(fun m -> match m.f_node with 
                    | Ftrue | Ffalse -> false
                    | Fapp (ls,tl) when List.for_all 
                        (fun m -> match m.t_node with 
                           | Tvar _ -> true 
                           | _ -> false) tl -> false
                    | _ -> true)

let () =
  Driver.register_transform "inline_all" all;
  Driver.register_transform "inline_trivial" trivial
