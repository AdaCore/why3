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

exception ConstructorExpected of lsymbol
exception NonExhaustive of pattern list

module Compile (X : Action) = struct
  open X

  let rec compile constructors tl rl = match tl,rl with
    | _, [] -> (* no actions *)
        let pl = List.map (fun t -> pat_wild t.t_ty) tl in
        raise (NonExhaustive pl)
    | [], (_,a) :: _ -> (* no terms, at least one action *)
        a
    | t :: tl, _ -> (* process the leftmost column *)
        (* extract the set of constructors *)
        let ty = t.t_ty in
        let css = match ty.ty_node with
          | Tyapp (ts,_) ->
              let s_add s cs = Sls.add cs s in
              List.fold_left s_add Sls.empty (constructors ts)
          | Tyvar _ -> Sls.empty
        in
        (* map constructors to argument types *)
        let rec populate types p = match p.pat_node with
          | Pwild | Pvar _ -> types
          | Pas (p,_) -> populate types p
          | Por (p,q) -> populate (populate types p) q
          | Papp (fs,pl) ->
              if Sls.mem fs css then Mls.add fs pl types
              else raise (ConstructorExpected fs)
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
            | Por (p,q) ->
                dispatch (p::pl, a) (dispatch (q::pl, a) (cases,wilds))
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
        let pat_cont cs vl pl =
          let rec cont acc vl pl = match vl,pl with
            | (_::vl), (p::pl) -> cont (p::acc) vl pl
            | [], pl -> pat_app cs acc ty :: pl
            | _, _ -> assert false
          in
          cont [] vl pl
        in
    match t.t_node with
    | Tapp (cs,al) when Sls.mem cs css ->
        if Mls.mem cs cases then
          let tl = List.rev_append al tl in
          try compile constructors tl (Mls.find cs cases)
          with NonExhaustive pl -> raise (NonExhaustive (pat_cont cs al pl))
        else begin
          try compile constructors tl wilds
          with NonExhaustive pl ->
            let al = List.map pat_wild cs.ls_args in
            let pat = pat_app cs al (of_option cs.ls_value) in
            raise (NonExhaustive (pat::pl))
        end
    | _ -> begin
        let pw = pat_wild ty in
        let nopat =
          if Sls.is_empty css then Some pw else
          let test cs = not (Mls.mem cs types) in
          let unused = Sls.filter test css in
          if Sls.is_empty unused then None else
          let cs = Sls.choose unused in
          let pl = List.map pat_wild cs.ls_args in
          Some (pat_app cs pl (of_option cs.ls_value))
        in
        let base = match nopat with
          | None -> []
          | Some pat ->
              (try [pw, compile constructors tl wilds]
              with NonExhaustive pl -> raise (NonExhaustive (pat::pl)))
        in
        let add fs ql acc =
          let id = id_fresh "x" in
          let vl = List.map (fun q -> create_vsymbol id q.pat_ty) ql in
          let tl = List.fold_left (fun tl v -> t_var v :: tl) tl vl in
          let pat = pat_app fs (List.map pat_var vl) ty in
          try (pat, compile constructors tl (Mls.find fs cases)) :: acc
          with NonExhaustive pl -> raise (NonExhaustive (pat_cont fs vl pl))
        in
        match Mls.fold add types base with
        | [{ pat_node = Pwild }, a] -> a
        | bl -> mk_case t bl
    end

end

module CompileTerm = Compile (struct
  type action = term
  let mk_let v s t = t_let v s t
  let mk_case t bl = t_case t bl (snd (List.hd bl)).t_ty
end)

module CompileFmla = Compile (struct
  type action = fmla
  let mk_let v t f = f_let v t f
  let mk_case t bl = f_case t bl
end)

