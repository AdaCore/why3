(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Term
open Decl
open Theory

let meta_elim_ls = register_meta "ls:eliminate" [MTlsymbol]
    ~desc:"Removes@ any@ expression@ containing@ a@ specific@ lsymbol."

let eliminate_symbol _env =
  Trans.on_tagged_ls meta_elim_ls
    (fun ls_elim ->
       let elim_ls ls = Sls.exists (ls_equal ls) ls_elim in
       let rec elim (t:term) =
         match t.t_node with
         | Tvar _ | Tconst _ | Ttrue | Tfalse -> false
         | Tapp (ls,_) when elim_ls ls -> true
         | _ -> t_any elim t
       in
       Trans.decl (fun d -> match d.d_node with
           | Dparam l when (elim_ls l) -> []
           | Dlogic l when
               List.exists (fun (l,def) ->
                   elim_ls l
                || let _,t = open_ls_defn def in elim t) l -> []
           | Dprop (Pgoal,pr,t) when (elim t) ->
             [create_prop_decl Pgoal pr t_false]
           | Dprop (_,_,t) when (elim t) -> []
           | _ -> [d])
         None)

let () =
  Trans.register_env_transform "eliminate_symbol" eliminate_symbol
    ~desc:"Eliminate@ tagged@ symbol."
