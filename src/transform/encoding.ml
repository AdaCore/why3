(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Stdlib
open Ty
open Theory
open Task
open Trans

let meta_select_kept = register_meta_excl "select_kept" [MTstring]
  ~desc:"@[Specify@ how@ to@ automatically@ choose@ the@ type@ that@ are@ \
           kept@ (mark@ by@ 'encoding : kept')@ by@ the@ polymorphic@ \
           encoding:@]@\n  \
@[\
  - none:@[ don't@ mark@ automatically@]@\n\
  - goal:@[ mark@ all@ the@ closed@ type@ that@ appear@ has@ argument@ \
            in@ the@ goal@]@\n\
  - all:@[ same@ as@ goal@ but@ also@ in@ the@ premises.@]\
@]"
let meta_enco_kept   = register_meta_excl "enco_kept"   [MTstring]
  ~desc:"@[Specify@ how@ to@ keep@ type:@]@\n  \
@[\
  - @[<hov 2>twin: use@ conversion@ function@ between@ the@ kept@ types@ \
              and@ the@ universal@ type (a complete encoding)@]@\n\
  - @[<hov 2>instantiate: instantiate all the axioms with the kept types@]@\n\
  - @[<hov 2>instantiate_complete: same@ as@ instantiate@ but@ keep@ a@ \
    version@ not@ instantiated(a@ complete@ encoding).@]\
@]"
let meta_enco_poly   = register_meta_excl "enco_poly"   [MTstring]
  ~desc:"@[Specify@ how@ to@ keep@ encode@ polymorphism:@]@\n  \
@[\
  - @[<hov 2>decoexp: TODO @]@\n\
  - @[<hov 2>decorate: add@ around@ all@ the@ terms@ a@ function@ which@ \
             give@ the@ type@ of@ the@ terms@]@\n\
  - @[<hov 2>guard: add@ guards@ (hypothesis)@ in@ all@ the@ axioms@ about@ \
             the@ type@ of@ the@ variables@]@\n\
  - @[<hov 2>explicit: add@ type@ argument@ to@ all@ the@ polymorphic@ \
             functions@]\
@]"

let def_enco_select_smt  = "none"
let def_enco_kept_smt    = "twin"
let def_enco_poly_smt    = "decorate"

let def_enco_select_tptp = "none"
let def_enco_kept_tptp   = "twin"
let def_enco_poly_tptp   = "decorate"

let ft_select_kept = ((Hstr.create 17) : (Env.env,Sty.t) Trans.flag_trans)
let ft_enco_kept   = ((Hstr.create 17) : (Env.env,task)  Trans.flag_trans)
let ft_enco_poly   = ((Hstr.create 17) : (Env.env,task)  Trans.flag_trans)

let select_kept def env =
  let select = Trans.on_flag meta_select_kept ft_select_kept def env in
  let trans task =
    let add ty acc = create_meta Libencoding.meta_kept [MAty ty] :: acc in
    let decls = Sty.fold add (Trans.apply select task) [] in
    Trans.apply (Trans.add_tdecls decls) task
  in
  Trans.store trans

let encoding_smt env = Trans.seq [
  Libencoding.monomorphise_goal;
  select_kept def_enco_select_smt env;
  Trans.print_meta Libencoding.debug Libencoding.meta_kept;
  Trans.on_flag meta_enco_kept ft_enco_kept def_enco_kept_smt env;
  Trans.on_flag meta_enco_poly ft_enco_poly def_enco_poly_smt env]

let encoding_tptp env = Trans.seq [
  Libencoding.monomorphise_goal;
  select_kept def_enco_select_tptp env;
  Trans.print_meta Libencoding.debug Libencoding.meta_kept;
  Trans.on_flag meta_enco_kept ft_enco_kept def_enco_kept_tptp env;
  Trans.on_flag meta_enco_poly ft_enco_poly def_enco_poly_tptp env;
  Protect_finite.protect_finite]

let () = register_env_transform "encoding_smt" encoding_smt
  ~desc_metas:[meta_select_kept, Pp.empty_formatted;
               meta_enco_kept, Pp.empty_formatted;
               meta_enco_poly, Pp.empty_formatted]
  ~desc:"encode@ polymorphism@ with@ default@ configuration@ choosed@ for@ \
         smt@ solver"
let () = register_env_transform "encoding_tptp" encoding_tptp
  ~desc_metas:[meta_select_kept, Pp.empty_formatted;
               meta_enco_kept, Pp.empty_formatted;
               meta_enco_poly, Pp.empty_formatted]
  ~desc:"encode@ polymorphism@ with@ default@ configuration@ choosed@ for@ \
         tptp@ solver"
