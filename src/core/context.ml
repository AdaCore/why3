open Ident
open Theory

type puc_def =
  | Ktype of type_decl
  | Klogic of logic_decl 
  | Kprop of prop

type puc = { puc_next : (puc * Theory.decl) option;
             puc_tag : int;
             puc_known : decl Mid.t;
             puc_def : puc_def Mid.t;
           }


module S =
  struct
    type t = puc
    let hash puc = match puc.puc_next with
      | None -> 0
      | Some (n,d) -> 1 + (Hashcons.combine n.puc_tag d.d_tag)

    let equal a b = 
      match a.puc_next,b.puc_next with
        | None, None -> true
        | Some (na,da), Some (nb,db) -> na.puc_next == nb.puc_next && da.d_tag == db.d_tag
        | _ -> false

    let tag i puc = {puc with puc_tag = i}
  end

module Hsh = Hashcons.Make(S)

let nil = Hsh.hashcons {puc_next = None; puc_known = Mid.empty; puc_tag = -1}
(*
(* Manage new declaration *)

exception RedeclaredIdent of ident
exception UnknownIdent of ident

let add_known decl (id,def) puc =
  try
    if (Mid.find id uc.puc_known) != decl then raise (RedeclaredIdent id)
  with Not_found -> ();
    { puc with 
        puc_known = Mid.add id decl puc.puc_known;
        puc_def = Mid.add id def puc.puc_def }

let add_type uc decl (ts,def) =
  let uc = add_known decl ts.ts_name uc in
  match def with
  | Tabstract -> uc
  | Talgebraic lfs ->
      let add_constr uc fs = add_known decl (fs.fs_name, uc in
      List.fold_left add_constr uc lfs

let check_type kn (ts,def) = match def with
  | Tabstract ->
      begin match ts.ts_def with
        | Some ty -> known_ty kn ty
        | None -> ()
      end
  | Talgebraic lfs ->
      let check fs = List.iter (known_ty kn) (fst fs.fs_scheme) in
      List.iter check lfs

let add_logic uc = function
  | Lfunction (fs, df) ->
      let uc = add_symbol add_fs fs.fs_name fs uc in
      if df == None then add_param fs.fs_name uc else uc
  | Lpredicate (ps, dp) ->
      let uc = add_symbol add_ps ps.ps_name ps uc in
      if dp == None then add_param ps.ps_name uc else uc
  | Linductive (ps, la) ->
      let uc = add_symbol add_ps ps.ps_name ps uc in
      let add uc (id,f) = add_symbol add_pr id f uc in
      List.fold_left add uc la

let check_logic kn = function
  | Lfunction (fs, df) ->
      known_ty kn (snd fs.fs_scheme);
      List.iter (known_ty kn) (fst fs.fs_scheme);
      begin match df with
        | Some (_,_,_,f) -> known_fmla kn f
        | None -> ()
      end
  | Lpredicate (ps, dp) ->
      List.iter (known_ty kn) ps.ps_scheme;
      begin match dp with
        | Some (_,_,_,f) -> known_fmla kn f
        | None -> ()
      end
  | Linductive (ps, la) ->
      List.iter (known_ty kn) ps.ps_scheme;
      let check (_,f) = known_fmla kn f in
      List.iter check la


let add_decl uc d =
  let uc = match d.d_node with
    | Dtype dl ->
        let uc = List.fold_left (add_type d) uc dl in
         List.iter (check_type uc.uc_known) dl;
        uc
    | Dlogic dl ->
        let uc = List.fold_left (add_logic uc dl in
        List.iter (check_logic uc.uc_known) dl;
        uc
    | Dprop (k, id, f) ->
        known_fmla uc.uc_known f;
        add_symbol add_pr id f uc
    | Dclone _ | Duse _ -> assert false
  in
  { uc with uc_decls = d :: uc.uc_decls }


let cons n d = 
  
  Hsh.hashcons {puc_next = None;known = Mid.empty; puc_tag = -1}

*)
