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

open Wstdlib
open Ty
open Theory
open Task
open Trans

let meta_select_kept = register_meta_excl "select_kept" [MTstring]
  ~desc:"Specify@ the@ types@ to@ mark@ with@ 'encoding:kept':@;  \
    @[\
      - none: @[don't@ mark@ any@ type@ automatically@]@\n\
      - goal: @[mark@ every@ closed@ type@ in@ the@ goal@]@\n\
      - all:  @[mark@ every@ closed@ type@ in@ the@ task.@]\
    @]"

let meta_select_kept_default =
  register_meta_excl "select_kept_default" [MTstring]
  ~desc:"Default@ setting@ for@ select_kept"

let meta_enco_kept = register_meta_excl "enco_kept" [MTstring]
  ~desc:"Specify@ the@ type@ protection@ transformation:@;  \
    @[\
      - @[<hov 2>twin: use@ conversion@ functions@ between@ the@ kept@ types@ \
            and@ the@ universal@ type@]\
    @]"

let meta_enco_poly = register_meta_excl "enco_poly" [MTstring]
  ~desc:"Specify@ the@ type@ encoding@ transformation:@;  \
    @[\
      - @[<hov 2>tags: protect@ variables@ in@ equalities@ \
            with@ type@ annotations@]@\n\
      - @[<hov 2>guards: protect@ variables@ in@ equalities@ \
            with@ type@ conditions@]@\n\
      - @[<hov 2>tags_full: put@ type@ annotations@ on@ top@ \
            of@ every@ term@]@\n\
      - @[<hov 2>guards_full: add@ type@ conditions@ for@ every@ variable.@]\
    @]"

let def_enco_select_smt  = "none"
let def_enco_kept_smt    = "twin"
let def_enco_poly_smt    = "guards"
let def_enco_poly_tptp   = "tags"

let ft_select_kept = ((Hstr.create 17) : (Env.env,Sty.t) Trans.flag_trans)
let ft_enco_kept   = ((Hstr.create 17) : (Env.env,task)  Trans.flag_trans)
let ft_enco_poly   = ((Hstr.create 17) : (Env.env,task)  Trans.flag_trans)

let select_kept def env =
  let def = Trans.on_flag meta_select_kept_default ft_select_kept def in
  let select = Trans.on_flag_t meta_select_kept ft_select_kept def env in
  let trans task =
    let add ty acc = create_meta Libencoding.meta_kept [MAty ty] :: acc in
    let decls = Sty.fold add (Trans.apply select task) [] in
    Trans.apply (Trans.add_tdecls decls) task
  in
  Trans.store trans

let forget_kept = Trans.fold (fun hd task ->
  match hd.task_decl.td_node with
    | Meta (m,_) when meta_equal m Libencoding.meta_kept -> task
    | _ -> add_tdecl task hd.task_decl) None

let encoding_smt env = Trans.seq [
  Libencoding.monomorphise_goal;
  select_kept def_enco_select_smt env;
  Trans.print_meta Libencoding.debug Libencoding.meta_kept;
  Trans.trace_goal "meta_enco_kept" (Trans.on_flag meta_enco_kept ft_enco_kept def_enco_kept_smt env);
  Trans.on_flag meta_enco_poly ft_enco_poly def_enco_poly_smt env]

let encoding_tptp env = Trans.seq [
  Libencoding.monomorphise_goal;
  forget_kept;
  Trans.on_flag meta_enco_poly ft_enco_poly def_enco_poly_tptp env]

let () = register_env_transform "encoding_smt" encoding_smt
  ~desc:"Encode@ polymorphic@ types@ for@ provers@ with@ sorts."

let () = register_env_transform "encoding_tptp" encoding_tptp
  ~desc:"Encode@ polymorphic@ types@ for@ provers@ without@ sorts."


(* encoding only if polymorphism occurs *)

let encoding_smt_if_poly env =
  Trans.on_meta Detect_polymorphism.meta_monomorphic_types_only
    (function
    | [] -> encoding_smt env
    | _ -> Trans.identity)

let () =
  Trans.register_env_transform "encoding_smt_if_poly"
    encoding_smt_if_poly
    ~desc:"Same@ as@ encoding_smt@ but@ only@ if@ polymorphism@ appear."

let encoding_tptp_if_poly env =
  Trans.on_meta Detect_polymorphism.meta_monomorphic_types_only
    (function
    | [] -> encoding_tptp env
    | _ -> Trans.identity)

let () =
  Trans.register_env_transform "encoding_tptp_if_poly"
    encoding_tptp_if_poly
    ~desc:"Same@ as@ encoding_tptp@ but@ only@ if@ polymorphism@ appear."
