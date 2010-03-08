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

let fold isnotinlinedt isnotinlinedf _ env ctxt d = 
(*  Format.printf "I see : %a@\n%a@\n" Pretty.print_decl d print_env env;*)
  match d.d_node with
    | Dlogic [l] -> begin
        match l with
          | Lfunction (fs,None) -> env,add_decl ctxt d 
          | Lfunction (fs,Some fmla) -> 
              let _,vs,t = open_fs_defn fmla in
              let t = replacet env t in
              if t_s_any ffalse ((==) fs) t || isnotinlinedt t
              then  env,
              add_decl ctxt 
                (create_logic_decl [Lfunction(fs,
                                         Some (make_fs_defn fs vs t))])
              else {env with fs = Mls.add fs (vs,t) env.fs},ctxt
          | Lpredicate (ps,None) -> env,add_decl ctxt d
          | Lpredicate (ps,Some fmla) -> 
              let _,vs,f = open_ps_defn fmla in
              let f = replacep env f in
              if f_s_any ffalse ((==) ps) f || isnotinlinedf f
              then  env,
              add_decl ctxt 
                (create_logic_decl [Lpredicate(ps,Some (make_ps_defn ps vs f))])
              else {env with ps = Mls.add ps (vs,f) env.ps},ctxt
      end
    | Dind dl ->
        env, add_decl ctxt (create_ind_decl 
          (List.map (fun (ps,fmlal) -> ps, List.map (fun pr ->
            create_prop (id_dup pr.pr_name) (replacep env pr.pr_fmla)) 
          fmlal) dl))
    | Dlogic dl -> env,
        add_decl ctxt (create_logic_decl 
           (List.map 
              (function
                 | Lfunction (fs,None) as a -> a 
                 | Lfunction (fs,Some fmla) -> 
                     let _,vs,t = open_fs_defn fmla in
                     let t = replacet env t in
                     Lfunction (fs,Some (make_fs_defn fs vs t))
                 | Lpredicate (ps,None) as a -> a
                 | Lpredicate (ps,Some fmla) ->
                     let _,vs,t = open_ps_defn  fmla in
                     let t = replacep env t in
                     Lpredicate (ps,Some (make_ps_defn ps vs t))
              ) dl))
    | Dtype dl -> env,add_decl ctxt d
    | Dprop (k,pr) -> env,add_decl ctxt (create_prop_decl k
        (create_prop (id_dup pr.pr_name) (replacep env pr.pr_fmla)))
    | Duse _ | Dclone _ -> env,add_decl ctxt d
        
let t ~isnotinlinedt ~isnotinlinedf = 
  Transform.fold_map_up (fold isnotinlinedt isnotinlinedf) empty_env

let all = t ~isnotinlinedt:(fun _ -> false) ~isnotinlinedf:(fun _ -> false)

let trivial = t 
  ~isnotinlinedt:(fun m -> match m.t_node with
                    | Tconst _ | Tvar _ -> false
                    | Tapp (ls,tl) when List.for_all 
                        (fun m -> match m.t_node with Tvar _ -> true | _ -> false) tl -> true
                    | _ -> true )
  ~isnotinlinedf:(fun m -> match m.f_node with Ftrue | Ffalse | Fapp _ -> false
                    | _ -> true)
