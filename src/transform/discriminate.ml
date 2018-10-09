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
open Ident
open Ty
open Term
open Decl
open Theory
open Task

let meta_inst = register_meta "encoding:inst" [MTty]
  ~desc:"Specify@ which@ types@ should@ instantiate@ symbols@ marked@ by@ \
         'encoding:lskept'."

let meta_lskept = register_meta "encoding:lskept" [MTlsymbol]
  ~desc:"Specify@ which@ function/predicate@ symbols@ should@ be@ kept.@ \
         When@ the@ symbol@ is@ polymorphic,@ generate@ every@ possible@ \
         type@ instances@ with@ types@ marked@ by@ 'encoding:inst'."

let meta_lsinst = register_meta "encoding:lsinst" [MTlsymbol;MTlsymbol]
  ~desc:"Specify@ which@ type@ instances@ of@ symbols@ should@ be@ kept.@ \
         The first@ symbol@ specifies@ the@ polymorphic@ symbol,@ \
         the@ second@ provides@ a@ monomorphic@ type@ signature@ to@ keep."

let meta_select_inst = register_meta_excl "select_inst" [MTstring]
  ~desc:"Specify@ the@ types@ to@ mark@ with@ 'encoding:inst':@;  \
    @[\
      - none: @[don't@ mark@ any@ type@ automatically@]@\n\
      - goal: @[mark@ every@ closed@ type@ in@ the@ goal@]@\n\
      - all:  @[mark@ every@ closed@ type@ in@ the@ task.@]\
    @]"

let meta_select_lskept = register_meta_excl "select_lskept" [MTstring]
  ~desc:"Specify@ the@ symbols@ to@ mark@ with@ 'encoding:lskept':@;  \
    @[\
      - none: @[don't@ mark@ any@ symbol@ automatically@]@\n\
      - goal: @[mark@ every@ polymorphic@ symbol@ in@ the@ goal@]@\n\
      - all:  @[mark@ every@ polymorphic@ symbol@ in@ the@ task.@]\
    @]"

let meta_select_lsinst = register_meta_excl "select_lsinst" [MTstring]
  ~desc:"Specify@ the@ symbols@ to@ mark@ with@ 'encoding:lsinst':@;  \
    @[\
      - none: @[don't@ mark@ any@ symbol@ automatically@]@\n\
      - goal: @[mark@ every@ monomorphic@ instance@ in@ the@ goal@]@\n\
      - all:  @[mark@ every@ monomorphic@ instance@ in@ the@ task.@]\
    @]"

let meta_select_inst_default =
  register_meta_excl "select_inst_default" [MTstring]
  ~desc:"Default@ setting@ for@ select_inst"

let meta_select_lskept_default =
  register_meta_excl "select_lskept_default" [MTstring]
  ~desc:"Default@ setting@ for@ select_lskept"

let meta_select_lsinst_default =
  register_meta_excl "select_lsinst_default" [MTstring]
  ~desc:"Default@ setting@ for@ select_lsinst"

module OHTy = OrderedHashed(struct
  type t = ty
  let tag = ty_hash
end)

module OHTyl = OrderedHashedList(struct
  type t = ty
  let tag = ty_hash
end)

module Mtyl = Extmap.Make(OHTyl)

module Lsmap = struct

(* TODO : transmettre les tags des logiques polymorphe vers les logiques
   instantié. Un tag sur un logique polymorphe doit être un tag sur toute
   la famille de fonctions *)

  let ls_inst =
    (* FIXME? Skolem type constants are short-living but
       will stay in lsmap as long as the lsymbol is alive *)
    let lsmap = Wls.memoize 63 (fun _ -> ref Mtyl.empty) in
    fun ls tyl tyv ->
      let m = lsmap ls in
      let l = oty_cons tyl tyv in
      match Mtyl.find_opt l !m with
      | Some ls -> ls
      | None ->
          let nls = create_lsymbol (id_clone ls.ls_name) tyl tyv in
          m := Mtyl.add l nls !m;
          nls

  type t = lsymbol Mtyl.t Mls.t

  let empty = Mls.empty

  let add ls tyl tyv lsmap =
    if ls_equal ls ps_equ then lsmap else
    if not (List.for_all Ty.ty_closed (oty_cons tyl tyv)) then lsmap else
    let newls = function
      | None -> Some (ls_inst ls tyl tyv)
      | nls  -> nls in
    let insts = Mls.find_def Mtyl.empty ls lsmap in
    Mls.add ls (Mtyl.change newls (oty_cons tyl tyv) insts) lsmap

(* dead code
  let print_env fmt menv =
    Format.fprintf fmt "defined_lsymbol (%a)@."
      (Pp.print_iter2 Mls.iter Pp.semi Pp.comma Pretty.print_ls
         (Pp.print_iter2 Mtyl.iter Pp.semi Pp.arrow
            (Pp.print_list Pp.space Pretty.print_ty)
            Pretty.print_ls)) menv
*)

  (** From/To metas *)
  let metas lsmap =
    let fold_inst ls _ lsinst decls =
      create_meta meta_lsinst [MAls ls; MAls lsinst] :: decls in
    let fold_ls ls insts decls = Mtyl.fold (fold_inst ls) insts decls in
    Mls.fold fold_ls lsmap []

  let of_metas metas =
    let fold env args =
      match args with
        | [MAls ls; MAls lsinst] ->
          let tydisl = oty_cons lsinst.ls_args lsinst.ls_value in
          if not (List.for_all Ty.ty_closed tydisl) then env else
          let insts = Mls.find_def Mtyl.empty ls env in
          Mls.add ls (Mtyl.add tydisl lsinst insts) env
        | _ -> assert false
    in
    List.fold_left fold Mls.empty metas

end

let find_logic env ls tyl tyv =
  if ls_equal ls ps_equ then ls else
  try Mtyl.find (oty_cons tyl tyv) (Mls.find ls env)
  with Not_found -> ls

module Ssubst = Set.Make(struct
  type t = ty Mtv.t
  let compare = Mtv.compare OHTy.compare end)

(* find all the possible instantiation which can create a kept instantiation *)
let ty_quant env t =
  let add_vs acc0 ls tyl tyv =
    if ls_equal ls ps_equ then acc0 else
      try
        let insts = Mls.find ls env in
        let tyl = oty_cons tyl tyv in
        let fold_inst inst _ acc =
          let fold_subst subst acc =
            try
              let subst = List.fold_left2 ty_match subst tyl inst in
              Ssubst.add subst acc
            with TypeMismatch _ -> acc
          in
          (* fold on acc0 *)
          Ssubst.fold fold_subst acc0 acc
        in
        Mtyl.fold fold_inst insts acc0
      with Not_found (* no such p *) -> acc0
  in
  t_app_fold add_vs (Ssubst.singleton (Mtv.empty)) t

let ts_of_ls env ls decls =
  if ls_equal ls ps_equ then decls else
  let add_ts sts ts = Sts.add ts sts in
  let add_ty sts ty = ty_s_fold add_ts sts ty in
  let add_tyl tyl _ sts = List.fold_left add_ty sts tyl in
  let insts = Mls.find_def Mtyl.empty ls env in
  let sts = Mtyl.fold add_tyl insts Sts.empty in
  let add_ts ts dl = create_ty_decl ts :: dl in
  Sts.fold add_ts sts decls

(* The Core of the transformation *)
let map metas_rewrite_pr env d =
  let decls,metas =
    match d.d_node with
    | Dtype _ -> [d],[]
    | Ddata _ -> Printer.unsupportedDecl d
      "Algebraic and recursively-defined types are \
            not supported, run eliminate_algebraic"
    | Dparam ls ->
      let lls = Mtyl.values (Mls.find_def Mtyl.empty ls env) in
      let lds = List.map create_param_decl lls in
      ts_of_ls env ls (d::lds),[]
    | Dlogic [ls,ld] when not (Sid.mem ls.ls_name d.d_syms) ->
      let f = ls_defn_axiom ld in
      let substs = ty_quant env f in
      let conv_f tvar (defns,axioms) =
        let f = t_ty_subst tvar Mvs.empty f in
        let f = t_app_map (find_logic env) f in
        match ls_defn_of_axiom f with
          | Some ld ->
              create_logic_decl [ld] :: defns, axioms
          | None ->
              let nm = ls.ls_name.id_string ^ "_inst" in
              let pr = create_prsymbol (id_derive nm ls.ls_name) in
              defns, create_prop_decl Paxiom pr f :: axioms
      in
      let defns,axioms = Ssubst.fold conv_f substs ([],[]) in
      ts_of_ls env ls (List.rev_append defns axioms),[]
    | Dlogic _ -> Printer.unsupportedDecl d
      "Recursively-defined symbols are not supported, run eliminate_recursion"
    | Dind _ -> Printer.unsupportedDecl d
      "Inductive predicates are not supported, run eliminate_inductive"
    | Dprop (k,pr,f) ->
      let substs = ty_quant env f in
      let substs_len = Ssubst.cardinal substs in
      let conv_f tvar (task,metas) =
        let f = t_ty_subst tvar Mvs.empty f in
        let f = t_app_map (find_logic env) f in
        if substs_len = 1 then
          create_prop_decl k pr f :: task, metas
        else
          let pr' = create_prsymbol (id_clone pr.pr_name) in
          create_prop_decl k pr' f :: task,
          (if Spr.mem pr metas_rewrite_pr then
              create_meta Compute.meta_rewrite [MApr pr'] :: metas
           else metas)
      in
      Ssubst.fold conv_f substs ([],[])
  in
  List.rev_append (List.rev_map create_decl decls) metas


let ft_select_inst =
  ((Hstr.create 17) : (Env.env,Sty.t) Trans.flag_trans)

let ft_select_lskept =
  ((Hstr.create 17) : (Env.env,Sls.t) Trans.flag_trans)

let ft_select_lsinst =
  ((Hstr.create 17) : (Env.env,Lsmap.t) Trans.flag_trans)

let metas_from_env env =
  let fold_inst tyl _ s = List.fold_right Sty.add tyl s in
  let fold_ls _ insts s = Mtyl.fold fold_inst insts s in
  let sty = Mls.fold fold_ls env Sty.empty in
  let add ty decls = create_meta Libencoding.meta_kept [MAty ty] :: decls in
  Sty.fold add sty (Lsmap.metas env)

let inst_completion kn kept =
  let rec inst_constructors ty acc = match ty.ty_node with
    | Tyapp (ts,tyl) when not (Sty.mem ty acc) ->
        let acc = Sty.add ty acc in
        let tys = Sty.of_list tyl in
        let csl = Decl.find_constructors kn ts in
        let tys = if csl = [] then tys else
          let d = Mid.find ts.ts_name kn in
          let base = ty_app ts (List.map ty_var ts.ts_args) in
          let sbs = ty_match Mtv.empty base ty in
          let recu ts = Sid.mem ts.ts_name d.d_news in
          let add_fd tys ty = if ty_s_any recu ty
            then tys else Sty.add (ty_inst sbs ty) tys in
          let add_cs tys (cs,_) =
            List.fold_left add_fd tys cs.ls_args in
          List.fold_left add_cs tys csl in
        Sty.fold inst_constructors tys acc
    | _ -> acc in
  Sty.fold inst_constructors kept Sty.empty

let lsinst_completion kept lskept env =
  let fold_ls ls env =
    let rec aux env tydisl subst = function
      | [] ->
          let tydisl = List.rev tydisl in
          let tyl,tyv = match tydisl, ls.ls_value with
            | tyv::tyl, Some _ -> tyl, Some tyv
            | tyl, None -> tyl, None
            | _ -> assert false in
          Lsmap.add ls tyl tyv env
      | ty::tyl ->
          let fold_ty tykept env =
            try
              let subst = ty_match subst ty tykept in
              aux env (tykept::tydisl) subst tyl
            with TypeMismatch _ -> env
          in
          Sty.fold fold_ty kept env
    in
    aux env [] Mtv.empty (oty_cons ls.ls_args ls.ls_value)
  in
  Sls.fold fold_ls lskept env

let add_user_lsinst env = function
  | [MAls ls; MAls nls] -> Lsmap.add ls nls.ls_args nls.ls_value env
  | _ -> assert false

let clear_metas = Trans.fold (fun hd task ->
  match hd.task_decl.td_node with
    | Meta (m,_) when meta_equal m meta_lsinst -> task
    | _ -> add_tdecl task hd.task_decl) None

let select_lsinst env =
  let select m1 m2 ft =
    Trans.on_flag_t m1 ft (Trans.on_flag m2 ft "none") env in
  let inst   =
    select meta_select_inst   meta_select_inst_default   ft_select_inst   in
  let lskept =
    select meta_select_lskept meta_select_lskept_default ft_select_lskept in
  let lsinst =
    select meta_select_lsinst meta_select_lsinst_default ft_select_lsinst in
  let trans task =
    let inst   = Trans.apply inst   task in
    let lskept = Trans.apply lskept task in
    let lsinst = Trans.apply lsinst task in
    let inst   = Sty.union inst   (Task.on_tagged_ty meta_inst   task) in
    let lskept = Sls.union lskept (Task.on_tagged_ls meta_lskept task) in
    let lsinst = Task.on_meta meta_lsinst add_user_lsinst lsinst task in
    let inst   = inst_completion (Task.task_known task) inst in
    let lsinst = lsinst_completion inst lskept lsinst in
    let task   = Trans.apply clear_metas task in
    Trans.apply (Trans.add_tdecls (metas_from_env lsinst)) task
  in
  Trans.store trans

let lsymbol_distinction =
  Trans.on_meta meta_lsinst (fun metas ->
    if metas = [] then Trans.identity
    else
      let env = Lsmap.of_metas metas in
      (* Format.eprintf "instantiate %a@." print_env env; *)
      Trans.on_tagged_pr Compute.meta_rewrite (fun rewrite_pr ->
        Trans.tdecl (map rewrite_pr env) None))

let discriminate env = Trans.seq [
  Libencoding.monomorphise_goal;
  select_lsinst env;
  Trans.print_meta Libencoding.debug meta_lsinst;
  lsymbol_distinction;
]

let () = Trans.register_env_transform "discriminate" discriminate
  ~desc:"Generate@ monomorphic@ type@ instances@ of@ function@ and@ \
         predicate@ symbols@ and@ monomorphize@ task@ premises."

let discriminate_if_poly env =
  Trans.on_meta Detect_polymorphism.meta_monomorphic_types_only
    (function
    | [] -> discriminate env
    | _ -> Trans.identity)

let () =
  Trans.register_env_transform "discriminate_if_poly"
    discriminate_if_poly
    ~desc:"Same@ as@ discriminate@ but@ only@ if@ polymorphism@ appear."

let li_add_ls acc = function
  | [MAls ls; MAls nls] -> Mls.add nls ls acc
  | _ -> assert false

let get_lsinst task =
  Task.on_meta meta_lsinst li_add_ls Mls.empty task

let on_lsinst fn =
  Trans.on_meta meta_lsinst (fun dls ->
    fn (List.fold_left li_add_ls Mls.empty dls))

let sm_add_ls sm0 sm = function
  | [MAls ls; MAls nls] ->
      begin match Mid.find_opt ls.ls_name sm0 with
        | Some s -> Mid.add nls.ls_name s sm
        | None -> sm
      end
  | _ -> assert false

let get_syntax_map task =
  let sm0 = Printer.get_syntax_map task in
  Task.on_meta meta_lsinst (sm_add_ls sm0) sm0 task

let on_syntax_map fn =
  Printer.on_syntax_map (fun sm0 ->
  Trans.on_meta meta_lsinst (fun dls ->
    fn (List.fold_left (sm_add_ls sm0) sm0 dls)))
