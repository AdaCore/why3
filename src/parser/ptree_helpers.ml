(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ptree

let ident ?(attrs=[]) ?(loc=Loc.dummy_position) s =
  { id_str = s; id_ats = attrs; id_loc = loc }

let qualid l =
  let rec aux l =
    match l with
      | [] -> assert false
      | [x] -> Qident(ident x)
      | x::r -> Qdot(aux r,ident x)
  in
  aux (List.rev l)

let const ?(kind = Number.ILitDec) i =
  Constant.(ConstInt Number.{ il_kind = kind; il_int = BigInt.of_int i })

let unit_binder ?(loc=Loc.dummy_position) () = [loc, None, false, Some (PTtuple [])]

let one_binder ?(loc=Loc.dummy_position) ?(ghost=false) ?pty id =
  [loc, Some (ident ~loc id), ghost, pty]

let term ?(loc=Loc.dummy_position) t = { term_desc = t; term_loc = loc }

let tvar ?loc id = term ?loc (Tident id)

let tapp ?loc f l = term ?loc (Tidapp(f,l))

let pat ?(loc=Loc.dummy_position) p = { pat_desc = p; pat_loc = loc }

let pat_var ?loc id = pat ?loc (Pvar id)

let tconst ?loc i = term ?loc (Tconst (const i))




let break_id    = "'Break"
let continue_id = "'Continue"
let return_id   = "'Return"


let expr ?(loc=Loc.dummy_position) e = { expr_desc = e; expr_loc = loc }

let econst ?loc i = expr ?loc (Econst (const i))

let eapp ?loc f l = expr ?loc (Eidapp(f,l))

let eapply ?loc e1 e2 = expr ?loc (Eapply(e1,e2))

let evar ?loc x = expr ?loc (Eident x)

let empty_spec = {
  sp_pre = [];
  sp_post = [];
  sp_xpost = [];
  sp_reads = [];
  sp_writes = [];
  sp_alias = [];
  sp_variant = [];
  sp_checkrw = false;
  sp_diverge = false;
  sp_partial = false;
}

let use ?(loc=Loc.dummy_position) ~import l =
  let qid_id_opt = (qualid l, None) in
  Duseimport(loc,import,[qid_id_opt])

let global_var_decl ty id =
  let v =
    Eany([], Expr.RKnone, Some ty, pat Pwild, Ity.MaskVisible, empty_spec)
  in
  let body = expr (Eapply(expr Eref, expr v)) in
  let attrs = [ATstr Pmodule.ref_attr] in
  let id_x = ident ~attrs id in
  id_x, Dlet (id_x, false, Expr.RKnone, body)

let prop k ?loc id t =
  Dprop(k,ident ?loc id,t)

module F = struct

  type state = { modules : (ident * decl list) list ;
                 module_id : ident option;
                 decls : decl list;
                 fun_head : (bool * bool * pty option * ident * binder list) option;
                 spec_pre : term list;
                 spec_writes : term list;
                 spec_post : term list;
               }

  exception Invalid_use_of_helpers of string

  let invalid_use s = raise (Invalid_use_of_helpers s)

  let create () = { modules = [];
                    module_id = None;
                    decls = [];
                    fun_head = None;
                    spec_pre = [];
                    spec_writes = [];
                    spec_post = [];
                  }

  let begin_module s ?loc name =
    match s.fun_head,s.module_id,s.decls with
    | Some _,_,_ -> invalid_use "begin_module: function declaration already in progress"
    | None,Some _,_ -> invalid_use "begin_module: module declaration already in progress"
    | None,None,(_::_) -> invalid_use "begin_module: top level declarations already in progress"
    | None,None,[] ->
       let id = ident ?loc name in
       { s with module_id = Some id }

  let use s ?loc ~import l =
    match s.fun_head with
    | Some _ -> invalid_use "use: function declaration already in progress"
    | None ->
       let d = use ?loc ~import l in
       { s with decls = d :: s.decls }

  let add_prop s k ?loc id t =
    match s.fun_head with
    | Some _ -> invalid_use "add_prop: function declaration already in progress"
    | None ->
       let d = prop k ?loc id t in
       { s with decls = d :: s.decls }

  let add_global_var_decl s ty id =
    match s.fun_head with
    | Some _ -> invalid_use "begin_let: function declaration already in progress"
    | None ->
        let id,d = global_var_decl ty id in
        id, { s with decls = d :: s.decls }

  let begin_let s ?(ghost=false) ?(diverges=false) ?ret_type id params =
    match s.fun_head with
    | Some _ -> invalid_use "begin_let: function declaration already in progress"
    | None ->
       { s with fun_head = Some (ghost,diverges,ret_type,(ident id), params) }

  let add_pre s t =
    match s.fun_head with
    | None -> invalid_use "add_pre: no function declaration in progress"
    | Some _ ->
       { s with spec_pre = t :: s.spec_pre }

  let add_writes s w =
    match s.fun_head with
    | None -> invalid_use "add_pre: no function declaration in progress"
    | Some _ ->
       { s with spec_writes = w @ s.spec_writes }

  let add_post s t =
    match s.fun_head with
    | None -> invalid_use "add_post: no function declaration in progress"
    | Some _ ->
       { s with spec_post = t :: s.spec_post }

  let add_body s e =
    match s.fun_head with
    | None -> invalid_use "add_body: no function declaration in progress"
    | Some (ghost,diverges,ret_type,id,params) ->
       let pres = List.rev s.spec_pre in
       let posts =
         List.rev_map (fun t -> (Loc.dummy_position,[pat Pwild,t])) s.spec_post
       in
       let spec = {
           sp_pre = pres;
           sp_post = posts;
           sp_xpost = [];
           sp_reads = [];
           sp_writes = [];
           sp_alias = [];
           sp_variant = [];
           sp_checkrw = false;
           sp_diverge = diverges;
           sp_partial = false;
         }
       in
       let f = Efun(params,ret_type,pat Pwild,Ity.MaskVisible,spec,e) in
       let d = Dlet(id, ghost, Expr.RKnone, expr f) in
       { s with
         fun_head = None;
         decls = d :: s.decls;
         spec_pre = [];
         spec_post = [];
       }


  let end_module s =
    match s.fun_head,s.module_id with
    | (Some _),_ -> invalid_use "end_module: function declaration in progress"
    | None,None -> invalid_use "end_module: no module declaration in progress"
    | None,(Some id) ->
       { s with
         modules = (id, List.rev s.decls) :: s.modules;
         module_id = None;
         decls = [] }

  let get_mlw_file s =
    match s.fun_head,s.module_id,s.modules,s.decls with
    | (Some _),_,_,_ -> invalid_use "get_mlw_file: function declaration in progress"
    | None,(Some _),_,_ -> invalid_use "get_mlw_module: module declaration in progress"
    | None,None,l,[] -> Modules (List.rev l)
    | None,None,[],l -> Decls (List.rev l)
    | None,None,(_::_),(_::_) -> assert false

end

module I = struct

  let st = ref (F.create ())

  let begin_module ?loc s =
    st := F.begin_module !st ?loc s

  let use ?loc ~import l =
    st := F.use !st ?loc ~import l

  let add_prop k ?loc id t =
    st := F.add_prop !st k ?loc id t

  let add_global_var_decl ty id =
    let id,s = F.add_global_var_decl !st ty id in
    st := s; id

  let begin_let ?(ghost=false) ?(diverges=false) ?ret_type id params =
    st := F.begin_let !st ~ghost ~diverges ?ret_type id params

  let add_pre t =
    st := F.add_pre !st t

  let add_writes w =
    st := F.add_writes !st w

  let add_post t =
    st := F.add_post !st t

  let add_body e =
    st := F.add_body !st e

  let end_module () =
    st := F.end_module !st

  let get_mlw_file () =
    let x = F.get_mlw_file !st in
    st := F.create ();
    x

end
