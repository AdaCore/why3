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

let why_filename = "encoding_decorate"

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
              t2u : lsymbol}

type tenv = {specials : lconv Mts.t;
            deco : ty;
            undeco : ty;
            sort : lsymbol;
            ty : ty}
            

let load_prelude env =
  let specials_type = [ts_int;ts_real] in
  let prelude = Env.find_theory env [why_filename] "Prelude" in
  let sort = Theory.ns_find_ls prelude.th_export ["sort"] in
  let ty = ty_app (Theory.ns_find_ts prelude.th_export ["ty"]) [] in
  let deco = ty_app (Theory.ns_find_ts prelude.th_export ["deco"]) [] in
  let undeco = ty_app (Theory.ns_find_ts prelude.th_export ["undeco"]) [] in
  let task = None in
  let task = flat_theory task prelude in
  let builtin = Env.find_theory env [why_filename] "Builtin" in
  let type_t = Theory.ns_find_ts builtin.th_export ["t"] in
  let logic_d2t = Theory.ns_find_ls builtin.th_export ["d2t"] in
  let logic_t2u = Theory.ns_find_ls builtin.th_export ["t2u"] in
  let clone_builtin (task,spmap) ts =
    let name = ts.ts_name.id_short in
    let th_uc = create_theory (id_fresh ("encoding_decorate_for_"^name)) in
    let ty = (ty_app ts []) in
    let add_fsymbol fs task =
      let decl = Decl.create_logic_decl [fs,None] in
      add_decl task decl in
    let d2ty = create_fsymbol (id_fresh ("d2"^name)) [deco]  ty in
    let ty2u = create_fsymbol (id_fresh (name^"2u")) [ty] undeco in
    let th_uc = add_fsymbol d2ty (add_fsymbol ty2u th_uc) in
    let th_inst = create_inst 
      ~ts:[type_t,ts]
      ~ls:[logic_d2t,d2ty;logic_t2u,ty2u]
      ~lemma:[] ~goal:[] in
    let lconv = { d2t = d2ty; t2u = ty2u} in
    let th_uc = clone_export th_uc builtin th_inst in
    let th = close_theory th_uc in
    let task = flat_theory task th in
      task,Mts.add ts lconv spmap
  in
  let task,specials = 
    List.fold_left clone_builtin (task,Mts.empty) specials_type in
  task,
  { specials = specials;
    deco = deco;
    undeco = undeco;
    ty = ty;
    sort = sort}
    


let decl (tenv:tenv) d = [d]
  (* match d.d_node with *)
  (*   | Dtype t when Mts.mem tenv.specials t -> [d] *)
  (*   | Dtype t when Mts.mem tenv.specials t -> [d] *)
  (*   | Dlogic l -> *)
  (*       let fn = function *)
  (*         | ls, Some ld -> *)
  (*             let vl,e = open_ls_defn ld in *)
  (*             make_ls_defn ls vl (e_map fnT fnF e) *)
  (*         | ld -> ld *)
  (*       in *)
  (*       create_logic_decl (List.map fn l) *)
  (*   | Dind l -> *)
  (*       let fn (pr,f) = pr, fnF f in *)
  (*       let fn (ps,l) = ps, List.map fn l in *)
  (*       create_ind_decl (List.map fn l) *)
  (*   | Dprop (k,pr,f) -> *)
  (*       create_prop_decl k pr (fnF f) *)

let t = Register.store_env 
  (fun () env -> 
     let init_task,tenv = load_prelude env in
     Trans.decl (decl tenv) init_task)

let () = Driver.register_transform "encoding_decorate" t
