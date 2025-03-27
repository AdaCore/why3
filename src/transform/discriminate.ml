(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
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
         type@ instances@ whose@ parameter/return@ type@ (or@ a@ supertype)@ \
         is@ marked@ by@ 'encoding:inst'.@ \
         Ignores@ constructors@ and@ projections."

let meta_lsinst = register_meta "encoding:lsinst" [MTlsymbol;MTlsymbol]
  ~desc:"Specify@ which@ type@ instances@ of@ symbols@ should@ be@ kept.@ \
         The first@ symbol@ specifies@ the@ polymorphic@ symbol,@ \
         the@ second@ provides@ a@ monomorphic@ type@ signature@ to@ keep.@ \
         Ignores@ instances@ of@ constructors@ and@ projections."

let meta_alginst = register_meta "encoding:alginst" [MTty]
  ~desc:"Specify@ which@ instances@ of@ algebraic@ types@ should@ be@ kept."


let meta_lsinst_proj = register_meta "encoding:lsinst_proj" [MTlsymbol;MTty]
  ~desc:"Instances@ of@ projections.@ Internal@ use@ only."

let meta_lsinst_constr = register_meta "encoding:lsinst_contr" [MTlsymbol;MTty]
  ~desc:"Instances@ of@ constructors.@ Internal@ use@ only."

let meta_select_inst = register_meta_excl "select_inst" [MTstring]
  ~desc:"Specify@ the@ types@ to@ mark@ with@ 'encoding:inst':@;  \
    @[\
      - none:  @[don't@ mark@ any@ type@ automatically@]@\n\
      - goal:  @[mark@ every@ closed@ type@ in@ the@ goal@]@\n\
      - local: @[mark@ every@ closed@ type@ in@ the@ local@ context@]@\n\
      - all:   @[mark@ every@ closed@ type@ in@ the@ task.@]\
    @]"

let meta_select_lskept = register_meta_excl "select_lskept" [MTstring]
  ~desc:"Specify@ the@ symbols@ to@ mark@ with@ 'encoding:lskept':@;  \
    @[\
      - none:  @[don't@ mark@ any@ symbol@ automatically@]@\n\
      - goal:  @[mark@ every@ polymorphic@ symbol@ in@ the@ goal@]@\n\
      - local: @[mark@ every@ polymorphic@ symbol@ in@ the@ local@ context@]@\n\
      - all:   @[mark@ every@ polymorphic@ symbol@ in@ the@ task.@]\
    @]"

let meta_select_lsinst = register_meta_excl "select_lsinst" [MTstring]
  ~desc:"Specify@ the@ symbols@ to@ mark@ with@ 'encoding:lsinst':@;  \
    @[\
      - none:  @[don't@ mark@ any@ symbol@ automatically@]@\n\
      - goal:  @[mark@ every@ monomorphic@ instance@ in@ the@ goal@]@\n\
      - local: @[mark@ every@ monomorphic@ instance@ in@ the@ local@ context@]@\n\
      - all:   @[mark@ every@ monomorphic@ instance@ in@ the@ task.@]\
    @]"

let meta_select_alginst = register_meta_excl "select_alginst" [MTstring]
  ~desc:"Specify@ the@ types@ to@ mark@ with@ 'encoding:alginst':@;  \
    @[\
      - none:  @[don't@ mark@ any@ algebraic@ type@ instance@ automatically@]@\n\
      - goal:  @[mark@ every@ monomorphic@ instance@ of@ algebraic@ type@ in@ the@ goal@]@\n\
      - local: @[mark@ every@ monomorphic@ instance@ of@ algebraic@ type@ in@ the@ local@ context@]@\n\
      - all:   @[mark@ every@ monomorphic@ instance@ of@ algebraic@ type@ in@ the@ task.@]\
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

let meta_select_alginst_default =
  register_meta_excl "select_alginst_default" [MTstring]
  ~desc:"Default@ setting@ for@ select_alginst"

module OHTyl = OrderedHashedList(struct
  type t = ty
  let tag = ty_hash
end)

module Styl = Extset.Make(OHTyl)
module Mtyl = Styl.M

module Insts : sig
  type t
  val find_ls_insts : lsymbol -> t -> lsymbol Mtyl.t
  val find_alg_insts : tysymbol -> t -> Styl.t
  val subst_ls : t -> lsymbol -> ty list -> ty option -> lsymbol
  val make : lsinsts:meta_arg list list -> alginsts:meta_arg list list ->
             lsinsts_proj:meta_arg list list -> lsinsts_constr:meta_arg list list ->
             t
end = struct
  type t = {
      ls: lsymbol Mtyl.t Mls.t;
      alg: Styl.t Mts.t;
    }

  let find_ls_insts x env = Mls.find_def Mtyl.empty x env.ls
  let find_alg_insts x env = Mts.find_def Styl.empty x env.alg

  let subst_ls env ls tyl tyv =
    if ls_equal ls ps_equ then ls else
    Mtyl.find_def ls (oty_cons tyl tyv) (find_ls_insts ls env)

  let add_ls_inst ls tyl tyv lsinst map =
    let tydisl = oty_cons tyl tyv in
    let insts = Mls.find_def Mtyl.empty ls map in
    Mls.add ls (Mtyl.add tydisl lsinst insts) map

  let make ~lsinsts ~alginsts ~lsinsts_proj ~lsinsts_constr =
    let fold_alg acc = function
        | [MAty {ty_node = Tyapp (_, [])}] -> acc
        | [MAty {ty_node = Tyapp (tys, tyl)}] ->
          let insts = Mts.find_def Styl.empty tys acc in
          Mts.add tys (Styl.add tyl insts) acc
        | _ -> assert false
    in
    let alg = List.fold_left fold_alg Mts.empty alginsts in
    let fold_ls acc = function
        | [MAls ls; MAls lsinst] ->
          add_ls_inst ls lsinst.ls_args lsinst.ls_value lsinst acc
        | _ -> assert false
    in
    let ls = List.fold_left fold_ls Mls.empty lsinsts in
    (* We add constructors and projections. They are substituted to themselves,
       but it is important that [ty_quant] is aware that they need to be
       monomorphized. *)
    let fold_proj acc = function
        | [MAls proj; MAty ty] ->
            let subst = List.fold_left2 ty_match Mtv.empty proj.ls_args [ty] in
            let tyv = Option.map (ty_inst subst) proj.ls_value in
            add_ls_inst proj [ty] tyv proj acc
        | _ -> assert false
    in
    let ls = List.fold_left fold_proj ls lsinsts_proj in
    let fold_constr acc = function
        | [MAls c; MAty ty] ->
           let subst = oty_match Mtv.empty c.ls_value (Some ty) in
           let tyl = List.map (ty_inst subst) c.ls_args in
           add_ls_inst c tyl (Some ty) c acc
        | _ -> assert false
    in
    let ls = List.fold_left fold_constr ls lsinsts_constr in
    { ls; alg }
end

module Ssubst = Set.Make(struct
  type t = ty Mtv.t
  let compare = Mtv.compare ty_compare end)

(* find all the possible instantiation which can create a kept instantiation *)
let ty_quant env t =
  let fold_app acc0 ls tyl tyv =
    if ls_equal ls ps_equ then acc0 else
      let insts = Insts.find_ls_insts ls env in
      if Mtyl.is_empty insts then (* no such p *) acc0 else
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
  in
  let acc = t_app_fold fold_app (Ssubst.singleton (Mtv.empty)) t in
  let fold_case acc0 tys tyl _ =
    let insts = Insts.find_alg_insts tys env in
    if Styl.is_empty insts then acc0 else
    let fold_inst inst acc =
      let fold_subst subst acc =
        try
          let subst = List.fold_left2 ty_match subst tyl inst in
          Ssubst.add subst acc
        with TypeMismatch _ -> acc
      in
      (* fold on acc0 *)
      Ssubst.fold fold_subst acc0 acc
    in
    Styl.fold fold_inst insts acc0
  in
  t_case_fold fold_case acc t

(* The Core of the transformation *)
let translate metas_rewrite_pr env d =
  let decls,metas =
    match d.d_node with
    | Dtype _ | Ddata _ -> [d],[]
    | Dparam ls ->
      let lls = Mtyl.values (Insts.find_ls_insts ls env) in
      let lds = List.map create_param_decl lls in
      d::lds,[]
    | Dlogic [ls,ld] when not (Sid.mem ls.ls_name (get_used_syms_decl d)) ->
      let f = ls_defn_axiom ld in
      let substs = ty_quant env f in
      let conv_f subst (defns,axioms) =
        let f = t_ty_subst subst Mvs.empty f in
        let f = t_app_map (Insts.subst_ls env) f in
        match ls_defn_of_axiom f with
          | Some ld ->
              create_logic_decl [ld] :: defns, axioms
          | None ->
              let nm = ls.ls_name.id_string ^ "_inst" in
              let pr = create_prsymbol (id_derive nm ls.ls_name) in
              defns, create_prop_decl Paxiom pr f :: axioms
      in
      let defns,axioms = Ssubst.fold conv_f substs ([],[]) in
      List.rev_append defns axioms,[]
    | Dlogic _ -> Printer.unsupportedDecl d
      "Recursively-defined symbols are not supported, run eliminate_recursion"
    | Dind _ -> Printer.unsupportedDecl d
      "Inductive predicates are not supported, run eliminate_inductive"
    | Dprop (k,pr,f) ->
      let substs = ty_quant env f in
      let substs_len = Ssubst.cardinal substs in
      let conv_f subst (task, metas)=
        let f = t_ty_subst subst Mvs.empty f in
        let f = t_app_map (Insts.subst_ls env) f in
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

module Lsmap : sig
  type t
  val empty : t
  val add : lsymbol -> ty list -> ty option -> t -> t
  val fold : (lsymbol -> ty list -> lsymbol -> 'acc -> 'acc) -> t -> 'acc -> 'acc
end = struct

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
    if ls_equal ls ps_equ then lsmap
    else if ls.ls_proj || ls.ls_constr > 0 then lsmap
    else if not (List.for_all Ty.ty_closed (oty_cons tyl tyv)) then lsmap else
    let newls = function
      | None -> Some (ls_inst ls tyl tyv)
      | nls  -> nls in
    let insts = Mls.find_def Mtyl.empty ls lsmap in
    Mls.add ls (Mtyl.change newls (oty_cons tyl tyv) insts) lsmap

  let fold f env acc =
    Mls.fold (fun ls insts acc -> Mtyl.fold (f ls) insts acc) env acc
end

let ft_select_inst =
  ((Hstr.create 17) : (Env.env,Sty.t) Trans.flag_trans)

let ft_select_lskept =
  ((Hstr.create 17) : (Env.env,Sls.t) Trans.flag_trans)

let ft_select_lsinst =
  ((Hstr.create 17) : (Env.env,Lsmap.t) Trans.flag_trans)

let ft_select_alginst =
  ((Hstr.create 17) : (Env.env,Styl.t Mts.t) Trans.flag_trans)

let metas_from_env kn lsmap tsmap =
  let fold_inst ls _ lsinst decls =
    create_meta meta_lsinst [MAls ls; MAls lsinst] :: decls in
  let metas = Lsmap.fold fold_inst lsmap [] in
  let fold_alg ts styl decls =
    let fold_alg_inst tyl decls =
      match tyl with [] -> decls | _ ->
      let ty = ty_app ts tyl in
      let decls = create_meta meta_alginst [MAty ty] :: decls in
      let cl = Decl.find_constructors kn ts in
      let fold_constr decls (c, _) =
        create_meta meta_lsinst_constr [MAls c; MAty ty] :: decls
      in
      let decls = List.fold_left fold_constr decls cl in
      let projs = List.filter_map Fun.id (snd (List.hd cl)) in
      let fold_proj decls proj =
        create_meta meta_lsinst_proj [MAls proj; MAty ty] :: decls
      in
      List.fold_left fold_proj decls projs
    in
    Styl.fold fold_alg_inst styl decls
  in
  let metas = Mts.fold fold_alg tsmap metas in
  let fold_ls_sty _ tyl _ s = List.fold_right Sty.add tyl s in
  let sty = Lsmap.fold fold_ls_sty lsmap Sty.empty in
  let add ty decls = create_meta Libencoding.meta_kept [MAty ty] :: decls in
  let metas = Sty.fold add sty metas in
  let fold_alg_sty ts styl s =
    Styl.fold (fun tyl s -> Sty.add (ty_app ts tyl) s) styl s
  in
  let sty = Mts.fold fold_alg_sty tsmap Sty.empty in
  let add ty decls = create_meta Eliminate_algebraic.meta_alg_kept [MAty ty] :: decls in
  Sty.fold add sty metas

(* Add to [kept]:
     - Any subtype of a type in [kept]
     - The type of any non-recursive field of an algebraic type in [kept]
     - And recursively *)
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

(* Add to [lsmap] symbols from [lskept], instantiated so that their
   parameter/return types are taken from [kept]. *)
let lsinst_completion kept lskept lsmap =
  let fold_ls ls lsmap =
    let rec aux lsmap tydisl subst = function
      | [] ->
          let tydisl = List.rev tydisl in
          let tyl,tyv = match tydisl, ls.ls_value with
            | tyv::tyl, Some _ -> tyl, Some tyv
            | tyl, None -> tyl, None
            | _ -> assert false in
          Lsmap.add ls tyl tyv lsmap
      | ty::tyl ->
          let fold_ty tykept lsmap =
            try
              let subst = ty_match subst ty tykept in
              aux lsmap (tykept::tydisl) subst tyl
            with TypeMismatch _ -> lsmap
          in
          Sty.fold fold_ty kept lsmap
    in
    aux lsmap [] Mtv.empty (oty_cons ls.ls_args ls.ls_value)
  in
  Sls.fold fold_ls lskept lsmap

let add_user_lsinst env = function
  | [MAls ls; MAls nls] -> Lsmap.add ls nls.ls_args nls.ls_value env
  | _ -> assert false

let clear_metas = Trans.fold (fun hd task ->
  match hd.task_decl.td_node with
    | Meta (m,_) when meta_equal m meta_lsinst ||
                      meta_equal m meta_alginst -> task
    | _ -> add_tdecl task hd.task_decl) None

let select_insts env =
  let select m1 m2 ft =
    Trans.on_flag_t m1 ft (Trans.on_flag m2 ft "none") env in
  let inst   =
    select meta_select_inst    meta_select_inst_default    ft_select_inst   in
  let lskept =
    select meta_select_lskept  meta_select_lskept_default  ft_select_lskept in
  let lsinst =
    select meta_select_lsinst  meta_select_lsinst_default  ft_select_lsinst in
  let alginst =
    select meta_select_alginst meta_select_alginst_default ft_select_alginst in
  let trans task =
    let kn = Task.task_known task in
    let inst   = Trans.apply inst   task in
    let lskept = Trans.apply lskept task in
    let lsinst = Trans.apply lsinst task in
    let alginst = Trans.apply alginst task in
    let inst   = Sty.union inst   (Task.on_tagged_ty meta_inst   task) in
    let lskept = Sls.union lskept (Task.on_tagged_ls meta_lskept task) in
    let lsinst = Task.on_meta meta_lsinst add_user_lsinst lsinst task in
    let inst   = inst_completion kn inst in
    let lsinst = lsinst_completion inst lskept lsinst in
    let task   = Trans.apply clear_metas task in
    Trans.apply (Trans.add_tdecls (metas_from_env kn lsinst alginst)) task
  in
  Trans.store trans

let lsymbol_distinction =
  Trans.on_meta meta_lsinst (fun lsinsts ->
  Trans.on_meta meta_alginst (fun alginsts ->
  if lsinsts = [] && alginsts == [] then Trans.identity else
  Trans.on_meta meta_lsinst_proj (fun lsinsts_proj ->
  Trans.on_meta meta_lsinst_constr (fun lsinsts_constr ->
      let env = Insts.make ~lsinsts ~alginsts ~lsinsts_proj ~lsinsts_constr  in
      Trans.on_tagged_pr Compute.meta_rewrite (fun rewrite_pr ->
        Trans.tdecl (translate rewrite_pr env) None)))))

let move_typedecl_top =
  let fold t (type_decls,other_decls) =
    match t.task_decl.td_node with
    | Decl {d_node = Ddata _ | Dtype _} -> t.task_decl::type_decls, other_decls
    | _ -> type_decls,t.task_decl::other_decls
  in
  Trans.bind (Trans.fold fold ([],[])) (fun (type_decls,other_decls) ->
    let decls = List.rev_append type_decls (List.rev other_decls) in
    Trans.return (List.fold_left add_tdecl None decls))

let discriminate env = Trans.seq [
  Eliminate_algebraic.compile_match;
  Libencoding.monomorphise_goal;
  select_insts env;
  Trans.print_meta Libencoding.debug meta_lsinst;
  Trans.print_meta Libencoding.debug meta_alginst;
  move_typedecl_top;
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
