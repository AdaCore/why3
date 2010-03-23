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

open Util
open Ident
open Ty
open Term

module type Action = sig
  type action
  val mk_let : vsymbol -> term -> action -> action
  val mk_case : term -> (pattern * action) list -> action
end

exception NonExhaustive of pattern list

module Compile (X : Action) = struct
  open X

  let rec compile css pat_cont tl rl = match tl,rl with
    | _, [] -> (* no actions *)
        let pl = List.map (fun t -> pat_wild t.t_ty) tl in
        raise (NonExhaustive (pat_cont pl))
    | [], (_,a) :: _ -> (* no terms, at least one action *)
        a
    | t :: tl, _ -> (* process the leftmost column *)
        (* map constructors to argument types *)
        let rec populate types p = match p.pat_node with
          | Pwild | Pvar _ -> types
          | Pas (p,_) -> populate types p
          | Papp (fs,pl) -> Mls.add fs pl types
        in
        let populate types (pl,_) = populate types (List.hd pl) in
        let types = List.fold_left populate Mls.empty rl in
        (* map constructors to subordinate matrices *)
        let add_case fs pl a cases =
          let rl = try Mls.find fs cases with Not_found -> [] in
          Mls.add fs ((pl,a)::rl) cases
        in
        let add_wild pl a fs ql cases =
          let add pl q = pat_wild q.pat_ty :: pl in
          add_case fs (List.fold_left add pl ql) a cases
        in
        let rec dispatch (pl,a) (cases,wilds) =
          let p = List.hd pl in let pl = List.tl pl in
          match p.pat_node with
            | Papp (fs,pl') ->
                add_case fs (List.rev_append pl' pl) a cases, wilds
            | Pas (p,x) ->
                dispatch (p::pl, mk_let x t a) (cases,wilds)
            | Pvar x ->
                let a = mk_let x t a in
                Mls.fold (add_wild pl a) types cases, (pl,a)::wilds
            | Pwild ->
                Mls.fold (add_wild pl a) types cases, (pl,a)::wilds
        in
        let cases,wilds = List.fold_right dispatch rl (Mls.empty,[]) in
        (* assemble the primitive case statement *)
        let ty = t.t_ty in
        let pw = pat_wild ty in
        let exhaustive, nopat = match ty.ty_node with
          | Tyapp (ts,_) ->
              begin match css ts with
              | [] -> false, pw
              | cl ->
                  let test cs = not (Mls.mem cs types) in
                  begin match List.filter test cl with
                  | cs :: _ ->
                      (* FIXME? specialize types to t.t_ty *)
                      let pl = List.map pat_wild cs.ls_args in
                      false, pat_app cs pl (of_option cs.ls_value)
                  | _ -> true, pw
                  end
              end
          | Tyvar _ -> false, pw
        in
        let base = if exhaustive then [] else
          let pat_cont pl = pat_cont (nopat::pl) in
          [pw, compile css pat_cont tl wilds]
        in
        let add fs ql acc =
          let id = id_fresh "x" in
          let vl = List.map (fun q -> create_vsymbol id q.pat_ty) ql in
          let tl = List.fold_left (fun tl v -> t_var v :: tl) tl vl in
          let pat = pat_app fs (List.map pat_var vl) ty in
          let rec cont acc vl pl = match vl,pl with
            | (_::vl), (p::pl) -> cont (p::acc) vl pl
            | [], pl -> pat_cont (pat_app fs acc ty :: pl)
            | _, _ -> assert false
          in
          let pat_cont pl = cont [] vl pl in
          (pat, compile css pat_cont tl (Mls.find fs cases)) :: acc
        in
        match Mls.fold add types base with
        | [{ pat_node = Pwild }, a] -> a
        | bl -> mk_case t bl

  let compile css tl rl = compile css (fun p -> p) tl rl

end

