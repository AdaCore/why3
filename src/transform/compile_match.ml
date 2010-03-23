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
open Pattern
open Decl
open Task

module CompileTerm = Compile (struct
  type action = term
  let mk_let v s t = t_let v s t
  let mk_case t bl =
    let ty = (snd (List.hd bl)).t_ty in
    t_case [t] (List.map (fun (p,a) -> [p],a) bl) ty
end)

module CompileFmla = Compile (struct
  type action = fmla
  let mk_let v t f = f_let v t f
  let mk_case t bl =
    f_case [t] (List.map (fun (p,a) -> [p],a) bl)
end)

let constructors kn ts =
  match (Mid.find ts.ts_name kn).d_node with
  | Dtype dl ->
      begin match List.assoc ts dl with
        | Talgebraic cl -> cl
        | Tabstract -> []
      end
  | _ -> assert false

let rec rewriteT kn t = match t.t_node with
  | Tcase (tl,bl) ->
      let mk_b (pl,_,t) = (pl,t) in
      let bl = List.map (fun b -> mk_b (t_open_branch b)) bl in
      begin try CompileTerm.compile (constructors kn) tl bl with
      | NonExhaustive pl ->
          Format.printf "@[Non-exhaustive matching in:@\n  @[<hov>%a@]@]\n\n"
            Pretty.print_term t;
          Format.printf "@[This pattern is not covered:  %a@]\n"
            (Pp.print_list Pp.comma Pretty.print_pat) pl;
          assert false
      end
  | _ ->
      t_map (rewriteT kn) (rewriteF kn) t

and rewriteF kn f = match f.f_node with
  | Fcase (tl,bl) ->
      let mk_b (pl,_,f) = (pl,f) in
      let bl = List.map (fun b -> mk_b (f_open_branch b)) bl in
      begin try CompileFmla.compile (constructors kn) tl bl with
      | NonExhaustive pl ->
          Format.printf "@[Non-exhaustive matching in:@\n  @[<hov>%a@]@]\n\n"
            Pretty.print_fmla f;
          Format.printf "@[This pattern is not covered:  %a@]\n"
            (Pp.print_list Pp.comma Pretty.print_pat) pl;
          assert false
      end
  | _ ->
      f_map (rewriteT kn) (rewriteF kn) f

let comp t task =
  let fnT = rewriteT t.task_known in
  let fnF = rewriteF t.task_known in
  add_decl task (decl_map fnT fnF t.task_decl)

let comp = Register.store (fun () -> Trans.map comp None)

let () = Driver.register_transform "compile_match" comp

