(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
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

open Format
open Util
open Ident
open Ty
open Term

(** Type declaration *)

type ty_def =
  | Tabstract
  | Talgebraic of lsymbol list

type ty_decl = tysymbol * ty_def

(** Logic declaration *)

type ls_defn = lsymbol * fmla

type logic_decl = lsymbol * ls_defn option

exception UnboundVar of vsymbol

let check_fvs f =
  let fvs = f_freevars Svs.empty f in
  Svs.iter (fun vs -> raise (UnboundVar vs)) fvs;
  f

let make_fs_defn fs vl t =
  let hd = t_app fs (List.map t_var vl) t.t_ty in
  let fd = f_forall_close vl [] (f_equ hd t) in
  fs, Some (fs, check_fvs fd)

let make_ps_defn ps vl f =
  let hd = f_app ps (List.map t_var vl) in
  let pd = f_forall_close vl [] (f_iff hd f) in
  ps, Some (ps, check_fvs pd)

let make_ls_defn ls vl = e_apply (make_fs_defn ls vl) (make_ps_defn ls vl)

let open_ls_defn (_,f) =
  let vl, ef = f_open_forall f in
  match ef.f_node with
    | Fapp (_, [_; t2]) -> vl, Term t2
    | Fbinop (_, _, f2) -> vl, Fmla f2
    | _ -> assert false

let open_fs_defn ld = let vl,e = open_ls_defn ld in
  match e with Term t -> vl,t | _ -> assert false

let open_ps_defn ld = let vl,e = open_ls_defn ld in
  match e with Fmla f -> vl,f | _ -> assert false

let ls_defn_axiom (_,f) = f

(** Termination checking for mutually recursive logic declarations *)

type descent =
  | Less of int
  | Equal of int
  | Unknown

let rec match_var link acc p = match p.pat_node with
  | Pwild -> acc
  | Pvar u -> List.rev_map (Mvs.add u link) acc
  | Pas (p,u) -> List.rev_map (Mvs.add u link) (match_var link acc p)
  | Por (p1,p2) ->
      let acc1 = match_var link acc p1 in
      let acc2 = match_var link acc p2 in
      List.rev_append acc1 acc2
  | Papp _ ->
      let link = match link with
        | Unknown -> Unknown
        | Equal i -> Less i
        | Less i  -> Less i
      in
      let join u = Mvs.add u link in
      List.rev_map (Svs.fold join p.pat_vars) acc

let rec match_term vm t acc p = match t.t_node, p.pat_node with
  | _, Pwild -> acc
  | Tvar v, _ when not (Mvs.mem v vm) -> acc
  | Tvar v, _ -> match_var (Mvs.find v vm) acc p
  | Tapp _, Pvar _ -> acc
  | Tapp _, Pas (p,_) -> match_term vm t acc p
  | Tapp _, Por (p1,p2) ->
      let acc1 = match_term vm t acc p1 in
      let acc2 = match_term vm t acc p2 in
      List.rev_append acc1 acc2
  | Tapp (c1,tl), Papp (c2,pl) when ls_equal c1 c2 ->
      let down l t p = match_term vm t l p in
      List.fold_left2 down acc tl pl
  | _,_ -> acc

let build_call_graph cgr syms ls =
  let call vm s tl =
    let desc t = match t.t_node with
      | Tvar v -> Mvs.find_default v Unknown vm
      | _ -> Unknown
    in
    Hls.add cgr s (ls, Array.of_list (List.map desc tl))
  in
  let rec term vm () t = match t.t_node with
    | Tapp (s,tl) when Mls.mem s syms ->
        t_fold (term vm) (fmla vm) () t; call vm s tl
    | Tlet ({t_node = Tvar v}, b) when Mvs.mem v vm ->
        let u,e = t_open_bound b in
        term (Mvs.add u (Mvs.find v vm) vm) () e
    | Tcase (e,bl) ->
        term vm () e; List.iter (fun b ->
          let p,t = t_open_branch b in
          let vml = match_term vm e [vm] p in
          List.iter (fun vm -> term vm () t) vml) bl
    | _ -> t_fold (term vm) (fmla vm) () t
  and fmla vm () f = match f.f_node with
    | Fapp (s,tl) when Mls.mem s syms ->
        f_fold (term vm) (fmla vm) () f; call vm s tl
    | Flet ({t_node = Tvar v}, b) when Mvs.mem v vm ->
        let u,e = f_open_bound b in
        fmla (Mvs.add u (Mvs.find v vm) vm) () e
    | Fcase (e,bl) ->
        term vm () e; List.iter (fun b ->
          let p,f = f_open_branch b in
          let vml = match_term vm e [vm] p in
          List.iter (fun vm -> fmla vm () f) vml) bl
    | Fquant (_,b) ->
        let _,_,f = f_open_quant b in fmla vm () f
    | _ -> f_fold (term vm) (fmla vm) () f
  in
  fun (vl,e) ->
    let i = ref (-1) in
    let add vm v = incr i; Mvs.add v (Equal !i) vm in
    let vm = List.fold_left add Mvs.empty vl in
    e_apply (term vm ()) (fmla vm ()) e

let build_call_list cgr ls =
  let htb = Hls.create 5 in
  let local v = Array.mapi (fun i -> function
    | (Less j) as d when i = j -> d
    | (Equal j) as d when i = j -> d
    | _ -> Unknown) v
  in
  let subsumes v1 v2 =
    let sbs d1 d2 = match d1,d2 with
      | _, Unknown -> ()
      | Equal u1, Equal u2 when u1 = u2 -> ()
      | Less  u1, Equal u2 when u1 = u2 -> ()
      | Less  u1, Less  u2 when u1 = u2 -> ()
      | _,_ -> raise Not_found
    in
    let test i d1 = sbs d1 (Array.get v2 i) in
    try Array.iteri test v1; true with Not_found -> false
  in
  let subsumed s c =
    List.exists (subsumes c) (Hls.find_all htb s)
  in
  let multiply v1 v2 =
    let to_less = function
      | Unknown -> Unknown
      | Equal i -> Less i
      | Less i  -> Less i
    in
    Array.map (function
      | Unknown -> Unknown
      | Equal i -> Array.get v2 i
      | Less i -> to_less (Array.get v2 i)) v1
  in
  let resolve s c =
    Hls.add htb s c;
    let mult (s,v) = (s, multiply c v) in
    List.rev_map mult (Hls.find_all cgr s)
  in
  let rec add_call lc = function
    | [] -> lc
    | (s,c)::r when ls_equal ls s -> add_call (local c :: lc) r
    | (s,c)::r when subsumed s c -> add_call lc r
    | (s,c)::r -> add_call lc (List.rev_append (resolve s c) r)
  in
  add_call [] (Hls.find_all cgr ls)

exception NoTerminationProof of lsymbol

let check_call_list ls cl =
  let add d1 d2 = match d1, d2 with
    | Unknown, _ -> d1
    | _, Unknown -> d2
    | Less _, _  -> d1
    | _, Less _  -> d2
    | _, _ -> d1
  in
  let add v1 v2 =
    Array.mapi (fun i d1 -> add d1 (Array.get v2 i)) v1
  in
  let rec check acc mx = match mx with
    | [] -> List.rev acc
    | a :: r ->
        (* calculate the bitwise minimum of all call vectors *)
        let p = List.fold_left add a r in
        (* find the decreasing argument positions *)
        let find l = function Less i -> i :: l | _ -> l in
        let res = Array.fold_left find [] p in
        (* eliminate the decreasing calls *)
        if res = [] then raise (NoTerminationProof ls);
        let test a =
          List.for_all (fun i -> Array.get a i <> Less i) res
        in
        check (List.rev_append res acc) (List.filter test mx)
  in
  check [] cl

let check_termination ldl =
  let cgr = Hls.create 5 in
  let add acc (ls,ld) = match ld with
    | Some ld -> Mls.add ls (open_ls_defn ld) acc
    | None -> acc
  in
  let syms = List.fold_left add Mls.empty ldl in
  Mls.iter (build_call_graph cgr syms) syms;
  let check ls _ =
    let cl = build_call_list cgr ls in
    check_call_list ls cl
  in
  Mls.mapi check syms

(** Inductive predicate declaration *)

type prsymbol = {
  pr_name : ident;
}

module Prop = WeakStructMake (struct
  type t = prsymbol
  let tag pr = pr.pr_name.id_tag
end)

module Spr = Prop.S
module Mpr = Prop.M
module Hpr = Prop.H
module Wpr = Prop.W

let pr_equal : prsymbol -> prsymbol -> bool = (==)

let pr_hash pr = id_hash pr.pr_name

let create_prsymbol n = { pr_name = id_register n }

type ind_decl = lsymbol * (prsymbol * fmla) list

(** Proposition declaration *)

type prop_kind =
  | Plemma    (* prove, use as a premise *)
  | Paxiom    (* do not prove, use as a premise *)
  | Pgoal     (* prove, do not use as a premise *)
  | Pskip     (* do not prove, do not use as a premise *)

type prop_decl = prop_kind * prsymbol * fmla

(** Declaration type *)

type decl = {
  d_node : decl_node;
  d_syms : Sid.t;         (* idents used in declaration *)
  d_news : Sid.t;         (* idents introduced in declaration *)
  d_tag  : Hashweak.tag;  (* unique magical tag *)
}

and decl_node =
  | Dtype  of ty_decl list      (* recursive types *)
  | Dlogic of logic_decl list   (* recursive functions/predicates *)
  | Dind   of ind_decl list     (* inductive predicates *)
  | Dprop  of prop_decl         (* axiom / lemma / goal *)

(** Declarations *)

module Hsdecl = Hashcons.Make (struct

  type t = decl

  let eq_td (ts1,td1) (ts2,td2) = ts_equal ts1 ts2 && match td1,td2 with
    | Tabstract, Tabstract -> true
    | Talgebraic l1, Talgebraic l2 -> list_all2 ls_equal l1 l2
    | _ -> false

  let eq_ld (ls1,ld1) (ls2,ld2) = ls_equal ls1 ls2 && match ld1,ld2 with
    | Some (_,f1), Some (_,f2) -> f_equal f1 f2
    | None, None -> true
    | _ -> false

  let eq_iax (pr1,fr1) (pr2,fr2) =
    pr_equal pr1 pr2 && f_equal fr1 fr2

  let eq_ind (ps1,al1) (ps2,al2) =
    ls_equal ps1 ps2 && list_all2 eq_iax al1 al2

  let equal d1 d2 = match d1.d_node, d2.d_node with
    | Dtype  l1, Dtype  l2 -> list_all2 eq_td l1 l2
    | Dlogic l1, Dlogic l2 -> list_all2 eq_ld l1 l2
    | Dind   l1, Dind   l2 -> list_all2 eq_ind l1 l2
    | Dprop (k1,pr1,f1), Dprop (k2,pr2,f2) ->
        k1 = k2 && pr_equal pr1 pr2 && f_equal f1 f2
    | _,_ -> false

  let hs_td (ts,td) = match td with
    | Tabstract -> ts_hash ts
    | Talgebraic l -> 1 + Hashcons.combine_list ls_hash (ts_hash ts) l

  let hs_ld (ls,ld) = Hashcons.combine (ls_hash ls)
    (Hashcons.combine_option (fun (_,f) -> f_hash f) ld)

  let hs_prop (pr,f) = Hashcons.combine (pr_hash pr) (f_hash f)

  let hs_ind (ps,al) = Hashcons.combine_list hs_prop (ls_hash ps) al

  let hs_kind = function
    | Plemma -> 11 | Paxiom -> 13 | Pgoal  -> 17 | Pskip  -> 19

  let hash d = match d.d_node with
    | Dtype  l -> Hashcons.combine_list hs_td 3 l
    | Dlogic l -> Hashcons.combine_list hs_ld 5 l
    | Dind   l -> Hashcons.combine_list hs_ind 7 l
    | Dprop (k,pr,f) -> Hashcons.combine (hs_kind k) (hs_prop (pr,f))

  let tag n d = { d with d_tag = Hashweak.create_tag n }

end)

module Decl = WeakStructMake (struct
  type t = decl
  let tag d = d.d_tag
end)

module Sdecl = Decl.S
module Mdecl = Decl.M
module Wdecl = Decl.W

let d_equal : decl -> decl -> bool = (==)

let d_hash d = Hashweak.tag_hash d.d_tag

(** Declaration constructors *)

let mk_decl node syms news = Hsdecl.hashcons {
  d_node = node;
  d_syms = syms;
  d_news = news;
  d_tag  = Hashweak.dummy_tag;
}

exception IllegalTypeAlias of tysymbol
exception ClashIdent of ident
exception BadLogicDecl of lsymbol * lsymbol

exception EmptyDecl
exception EmptyAlgDecl of tysymbol
exception EmptyIndDecl of lsymbol

exception NonPositiveTypeDecl of tysymbol * lsymbol * tysymbol

let news_id s id = Sid.add_new id (ClashIdent id) s

let syms_ts s ts = Sid.add ts.ts_name s
let syms_ls s ls = Sid.add ls.ls_name s

let syms_ty s ty = ty_s_fold syms_ts s ty
let syms_term s t = t_s_fold syms_ts syms_ls s t
let syms_fmla s f = f_s_fold syms_ts syms_ls s f

let create_ty_decl tdl =
  if tdl = [] then raise EmptyDecl;
  let add s (ts,_) = Sts.add ts s in
  let tss = List.fold_left add Sts.empty tdl in
  let check_constr tys ty (syms,news) fs =
    let vty = of_option fs.ls_value in
    if not (ty_equal ty vty) then raise (TypeMismatch (ty,vty));
    let add s ty = match ty.ty_node with
      | Tyvar v -> Stv.add v s
      | _ -> assert false
    in
    let vs = ty_fold add Stv.empty vty in
    let rec check seen s ty = match ty.ty_node with
      | Tyvar v when Stv.mem v vs -> s
      | Tyvar v -> raise (UnboundTypeVar v)
      | Tyapp (ts,_) ->
          let now = Sts.mem ts tss in
          if seen && now then
            raise (NonPositiveTypeDecl (tys,fs,ts))
          else
            let s = ty_fold (check (seen || now)) s ty in
            Sid.add ts.ts_name s
    in
    let syms = List.fold_left (check false) syms fs.ls_args in
    syms, news_id news fs.ls_name
  in
  let check_decl (syms,news) (ts,td) = match td with
    | Tabstract ->
        let syms = option_apply syms (syms_ty syms) ts.ts_def in
        syms, news_id news ts.ts_name
    | Talgebraic cl ->
        if cl = [] then raise (EmptyAlgDecl ts);
        if ts.ts_def <> None then raise (IllegalTypeAlias ts);
        let news = news_id news ts.ts_name in
        let ty = ty_app ts (List.map ty_var ts.ts_args) in
        List.fold_left (check_constr ts ty) (syms,news) cl
  in
  let (syms,news) = List.fold_left check_decl (Sid.empty,Sid.empty) tdl in
  mk_decl (Dtype tdl) syms news

let create_logic_decl ldl =
  if ldl = [] then raise EmptyDecl;
  let check_decl (syms,news) (ls,ld) = match ld with
    | Some (s,_) when not (ls_equal s ls) ->
        raise (BadLogicDecl (ls, s))
    | Some (_,f) ->
        syms_fmla syms f, news_id news ls.ls_name
    | None ->
        let syms = option_apply syms (syms_ty syms) ls.ls_value in
        let syms = List.fold_left syms_ty syms ls.ls_args in
        syms, news_id news ls.ls_name
  in
  let (syms,news) = List.fold_left check_decl (Sid.empty,Sid.empty) ldl in
  ignore (check_termination ldl);
  mk_decl (Dlogic ldl) syms news

exception InvalidIndDecl of lsymbol * prsymbol
exception TooSpecificIndDecl of lsymbol * prsymbol * term
exception NonPositiveIndDecl of lsymbol * prsymbol * lsymbol

exception Found of lsymbol
let ls_mem s sps = if Sls.mem s sps then raise (Found s) else false
let t_pos_ps sps = t_s_all (fun _ -> true) (fun s -> not (ls_mem s sps))

let rec f_pos_ps sps pol f = match f.f_node, pol with
  | Fapp (s, _), Some false when ls_mem s sps -> false
  | Fapp (s, _), None when ls_mem s sps -> false
  | Fbinop (Fiff, f, g), _ ->
      f_pos_ps sps None f && f_pos_ps sps None g
  | Fbinop (Fimplies, f, g), _ ->
      f_pos_ps sps (option_map not pol) f && f_pos_ps sps pol g
  | Fnot f, _ ->
      f_pos_ps sps (option_map not pol) f
  | Fif (f,g,h), _ ->
      f_pos_ps sps None f && f_pos_ps sps pol g && f_pos_ps sps pol h
  | _ -> f_all (t_pos_ps sps) (f_pos_ps sps pol) f

let create_ind_decl idl =
  if idl = [] then raise EmptyDecl;
  let add acc (ps,_) = Sls.add ps acc in
  let sps = List.fold_left add Sls.empty idl in
  let check_ax ps (syms,news) (pr,f) =
    let rec clause acc f = match f.f_node with
      | Fquant (Fforall, f) ->
          let _,_,f = f_open_quant f in clause acc f
      | Fbinop (Fimplies, g, f) -> clause (g::acc) f
      | _ -> (acc, f)
    in
    let cls, f = clause [] (check_fvs f) in
    match f.f_node with
      | Fapp (s, tl) when ls_equal s ps ->
          let mtch t ty =
            if not (ty_equal t.t_ty ty) then
              raise (TooSpecificIndDecl (ps, pr, t))
          in
          List.iter2 mtch tl ps.ls_args;
          (try ignore (List.for_all (f_pos_ps sps (Some true)) cls)
          with Found ls -> raise (NonPositiveIndDecl (ps, pr, ls)));
          syms_fmla syms f, news_id news pr.pr_name
      | _ -> raise (InvalidIndDecl (ps, pr))
  in
  let check_decl (syms,news) (ps,al) =
    if al = [] then raise (EmptyIndDecl ps);
    let news = news_id news ps.ls_name in
    List.fold_left (check_ax ps) (syms,news) al
  in
  let (syms,news) = List.fold_left check_decl (Sid.empty,Sid.empty) idl in
  mk_decl (Dind idl) syms news

let create_prop_decl k p f =
  let syms = syms_fmla Sid.empty f in
  let news = news_id Sid.empty p.pr_name in
  mk_decl (Dprop (k,p,check_fvs f)) syms news

(** Utilities *)

let decl_map fnT fnF d = match d.d_node with
  | Dtype _ ->
      d
  | Dlogic l ->
      let fn = function
        | ls, Some ld ->
            let vl,e = open_ls_defn ld in
            make_ls_defn ls vl (e_map fnT fnF e)
        | ld -> ld
      in
      create_logic_decl (List.map fn l)
  | Dind l ->
      let fn (pr,f) = pr, fnF f in
      let fn (ps,l) = ps, List.map fn l in
      create_ind_decl (List.map fn l)
  | Dprop (k,pr,f) ->
      create_prop_decl k pr (fnF f)

let decl_fold fnT fnF acc d = match d.d_node with
  | Dtype _ -> acc
  | Dlogic l ->
      let fn acc = function
        | _, Some ld ->
            let _,e = open_ls_defn ld in
            e_fold fnT fnF acc e
        | _ -> acc
      in
      List.fold_left fn acc l
  | Dind l ->
      let fn acc (_,f) = fnF acc f in
      let fn acc (_,l) = List.fold_left fn acc l in
      List.fold_left fn acc l
  | Dprop (_,_,f) ->
      fnF acc f

let rpair_map_fold f acc (x1,x2) =
  let acc, x2 = f acc x2 in
  acc, (x1, x2)

let list_rpair_map_fold f =
  Util.map_fold_left (rpair_map_fold f)

let decl_map_fold fnT fnF acc d =
  match d.d_node with
  | Dtype _ -> acc, d
  | Dprop (k,pr,f) ->
      let acc, f = f_map_fold fnT fnF acc f in
      acc, create_prop_decl k pr f
  | Dind l ->
      let acc, l =
        list_rpair_map_fold (list_rpair_map_fold (f_map_fold fnT fnF)) acc l in
      acc, create_ind_decl l
  | Dlogic l ->
      let acc, l =
      list_rpair_map_fold (option_map_fold
        (rpair_map_fold (f_map_fold fnT fnF))) acc l in
      acc, create_logic_decl l


(** Known identifiers *)

exception KnownIdent of ident
exception UnknownIdent of ident
exception RedeclaredIdent of ident

type known_map = decl Mid.t

let known_id kn id =
  if not (Mid.mem id kn) then raise (UnknownIdent id)

let merge_known kn1 kn2 =
  let check_known id decl1 decl2 =
    if d_equal decl1 decl2 then Some decl1
    else raise (RedeclaredIdent id)
  in
  Mid.union check_known kn1 kn2

let known_add_decl kn0 decl =
  let kn = Mid.map (fun _ -> decl) decl.d_news in
  let check id decl0 _ =
    if d_equal decl0 decl
    then raise (KnownIdent id)
    else raise (RedeclaredIdent id)
  in
  let kn = Mid.union check kn0 kn in
  let unk = Mid.diff (fun _ _ _ -> None) decl.d_syms kn in
  if Sid.is_empty unk then kn
  else raise (UnknownIdent (Sid.choose unk))

let find_constructors kn ts =
  match (Mid.find ts.ts_name kn).d_node with
  | Dtype dl ->
      begin match List.assq ts dl with
        | Talgebraic cl -> cl
        | Tabstract -> []
      end
  | _ -> assert false

let find_inductive_cases kn ps =
  match (Mid.find ps.ls_name kn).d_node with
  | Dind dl -> List.assq ps dl
  | Dlogic _ -> []
  | Dtype _ -> []
  | _ -> assert false

let find_logic_definition kn ls =
  match (Mid.find ls.ls_name kn).d_node with
  | Dlogic dl -> List.assq ls dl
  | Dind _ -> None
  | Dtype _ -> None
  | _ -> assert false

let find_prop kn pr =
  match (Mid.find pr.pr_name kn).d_node with
  | Dind dl ->
      let test (_,l) = List.mem_assq pr l in
      List.assq pr (snd (List.find test dl))
  | Dprop (_,_,f) -> f
  | _ -> assert false

let find_prop_decl kn pr =
  match (Mid.find pr.pr_name kn).d_node with
  | Dind dl ->
      let test (_,l) = List.mem_assq pr l in
      Paxiom, List.assq pr (snd (List.find test dl))
  | Dprop (k,_,f) -> k,f
  | _ -> assert false

exception NonExhaustiveExpr of (pattern list * expr)

let rec check_matchT kn () t = match t.t_node with
  | Tcase (t1,bl) ->
      let bl = List.map (fun b -> let p,t = t_open_branch b in [p],t) bl in
      ignore (try Pattern.CompileTerm.compile (find_constructors kn) [t1] bl
      with Pattern.NonExhaustive p -> raise (NonExhaustiveExpr (p,Term t)));
      t_fold (check_matchT kn) (check_matchF kn) () t
  | _ -> t_fold (check_matchT kn) (check_matchF kn) () t

and check_matchF kn () f = match f.f_node with
  | Fcase (t1,bl) ->
      let bl = List.map (fun b -> let p,f = f_open_branch b in [p],f) bl in
      ignore (try Pattern.CompileFmla.compile (find_constructors kn) [t1] bl
      with Pattern.NonExhaustive p -> raise (NonExhaustiveExpr (p,Fmla f)));
      f_fold (check_matchT kn) (check_matchF kn) () f
  | _ -> f_fold (check_matchT kn) (check_matchF kn) () f

let check_match kn d = decl_fold (check_matchT kn) (check_matchF kn) () d

exception NonFoundedTypeDecl of tysymbol

let rec check_foundness kn d =
  let rec check_constr s ty ls =
    let vty = of_option ls.ls_value in
    let m = ty_match Mtv.empty vty ty in
    let check ty = check_type s (ty_inst m ty) in
    List.for_all check ls.ls_args
  and check_type s ty = match ty.ty_node with
    | Tyvar _ -> true
    | Tyapp (ts,_) ->
        if Sts.mem ts s then false else
        let cl = find_constructors kn ts in
        if cl == [] then true else
        let s = Sts.add ts s in
        List.exists (check_constr s ty) cl
  in
  match d.d_node with
  | Dtype tdl ->
      let check () (ts,_) =
        let tl = List.map ty_var ts.ts_args in
        if check_type Sts.empty (ty_app ts tl)
        then () else raise (NonFoundedTypeDecl ts)
      in
      List.fold_left check () tdl
  | _ -> ()

let known_add_decl kn d =
  let kn = known_add_decl kn d in
  check_foundness kn d;
  check_match kn d;
  kn

