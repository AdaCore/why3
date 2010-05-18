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

open Format
open Why
open Ident
open Term
open Decl
open Theory
open Pgm_ttree
open Pgm_itree
open Pgm_typing

module E = Pgm_effect

type env = {
  uc      : theory_uc;
  globals : type_v Mls.t;
  locals  : type_v Mvs.t;
}

let empty_env uc = { uc = uc; globals = Mls.empty; locals = Mvs.empty }
let add_local x v env = { env with locals = Mvs.add x v env.locals }
let add_global x v env = { env with globals = Mls.add x v env.globals }

let ts_label env = ns_find_ts (get_namespace env.uc) ["label"]

let ls_bang env = ns_find_ls (get_namespace env.uc) ["prefix !"]

(* phase 3: translation to intermediate trees and effect inference **********)

let reference_of_term t = match t.t_node with
  | Tvar vs -> E.Rlocal vs
  | Tapp (ls, []) -> E.Rglobal ls
  | _ -> assert false

let rec term_effect env ef t = match t.t_node with
  | Tapp (ls, [t]) when ls_equal ls (ls_bang env) ->
      let r = reference_of_term t in
      E.add_read r ef
  | _ ->
      t_fold (term_effect env) (fmla_effect env) ef t

and fmla_effect _env _ef _f =
  assert false (*TODO*)

let add_binder env (x, v) = add_local x v env
let add_binders = List.fold_left add_binder

let rec expr env e =
  let ty = e.Pgm_ttree.expr_type in
  let loc = e.Pgm_ttree.expr_loc in
  let d, v, ef = expr_desc env loc ty e.Pgm_ttree.expr_desc in
  { expr_desc = d; expr_type_v = v; expr_effect = ef; expr_loc = loc }

and expr_desc env _loc ty = function
  | Pgm_ttree.Elogic t ->
      let ef = term_effect env E.empty t in
      Elogic t, Tpure ty, ef
  | Pgm_ttree.Elocal vs ->
      assert (Mvs.mem vs env.locals);
      Elocal vs, Mvs.find vs env.locals, E.empty
  | Pgm_ttree.Eglobal ls ->
      assert (Mls.mem ls env.globals);
      Eglobal ls, Mls.find ls env.globals, E.empty
  | Pgm_ttree.Eapply _ ->
      assert false (*TODO*)
  | Pgm_ttree.Eapply_ref _ ->
      assert false (*TODO*)
  | Pgm_ttree.Efun (bl, t) ->
      let env = add_binders env bl in
      let t, c = triple env t in
      Efun (bl, t), Tarrow (bl, c), E.empty
  | Pgm_ttree.Elet (v, e1, e2) ->
      let e1 = expr env e1 in
      let env = { env with locals = Mvs.add v e1.expr_type_v env.locals } in
      let e2 = expr env e2 in
      let ef = E.union e1.expr_effect e2.expr_effect in
      Elet (v, e1, e2), e2.expr_type_v, ef
  | _ -> 
      assert false (*TODO*)

and triple env (p, e, q) =
  let e = expr env e in
  let c = 
    { c_result_type = e.expr_type_v;
      c_effect      = e.expr_effect;
      c_pre         = p;
      c_post        = q }
  in
  (p, e, q), c

and recfun _env _def =
  assert false (*TODO*)

(* phase 4: weakest preconditions *******************************************)

module State : sig
  type t
  val create     : E.t -> t
  val push_label : env -> label -> t -> t
  val havoc      : env -> ?pre:label -> E.t   -> t -> t
  val term       : env ->               t -> term -> term
  val fmla       : env -> ?old:label -> t -> fmla -> fmla
  val quantify   : env -> t -> E.t -> fmla -> fmla
end = struct

  type t = {
    current : vsymbol E.Mref.t;
    old     : vsymbol E.Mref.t Mvs.t;
  }

  let havoc1 r m =
    let v = match r with
      | E.Rlocal vs -> 
	  create_vsymbol (id_fresh vs.vs_name.id_string) vs.vs_ty
      | E.Rglobal { ls_name = id; ls_value = Some ty } -> 
	  create_vsymbol (id_fresh id.id_string) ty
      | E.Rglobal { ls_value = None } ->
	  assert false
    in
    E.Mref.add r v m

  let create ef = 
    let s = E.Sref.union ef.E.reads ef.E.writes in
    { current = E.Sref.fold havoc1 s E.Mref.empty;
      old = Mvs.empty; }

  let fresh_label env =
    let ty = Ty.ty_app (ts_label env) [] in
    create_vsymbol (id_fresh "label") ty

  let havoc env ?pre ef s = 
    let l = match pre with
      | None -> fresh_label env
      | Some l -> l
    in
    { current = E.Sref.fold havoc1 ef.E.writes s.current;
      old = Mvs.add l s.current s.old; }

  let push_label env l s = havoc env ~pre:l E.empty s

  let ref_at cur s r = 
    let m = match cur with
      | None -> s.current
      | Some l -> assert (Mvs.mem l s.old); Mvs.find l s.old
    in
    assert (E.Mref.mem r m);
    E.Mref.find r m

  (* old = label for old state,     if any
     cur = label for current state, if any *)
  let rec term_at env old cur s t = match t.t_node with
    | Tapp (ls, [t]) when ls_equal ls (ls_bang env) ->
	let r = reference_of_term t in
	t_var (ref_at cur s r)
    (* TODO: old, at *)
    | _ ->
	t_map (term_at env old cur s) (fmla_at env old cur s) t

  and fmla_at env old cur s f = 
    f_map (term_at env old cur s) (fmla_at env old cur s) f

  let term env      s t = term_at env None None s t
  let fmla env ?old s f = fmla_at env old None s f

  let quantify _env _s _ef _f = assert false (*TODO*)

  let print _fmt _s = assert false (*TODO*)

end

let rec wprec env s e = match e.expr_desc with
  | Elogic t ->
      assert false (*TODO*)
  | _ -> 
      f_true (* TODO *)

let wp env _ls e = wprec env (State.create e.expr_effect) e

let wp_recfun _env _l _def = f_true (* TODO *)

let add_wp_decl l f env =
  let pr = create_prsymbol (id_fresh ("WP_" ^ l.ls_name.id_string)) in
  let d = create_prop_decl Pgoal pr f in
  { env with uc = add_decl env.uc d }

let decl env = function
  | Pgm_ttree.Dlet (ls, e) ->
      let e = expr env e in
      (* DEBUG *)
      printf "@[--effect %a-----@\n  %a@]@\n---------@." 
	Pretty.print_ls ls print_type_v e.expr_type_v;
      let f = wp env ls e in
      let env = add_wp_decl ls f env in
      let env = add_global ls e.expr_type_v env in
      env
  | Pgm_ttree.Dletrec dl ->
      let add_one env (ls, def) = 
	let def = recfun env def in
	let f = wp_recfun env ls def in 
	let env = add_wp_decl ls f env in
	let v = assert false (*TODO*) in
	let env = add_global ls v env in
	env
      in
      List.fold_left add_one env dl
  | Pgm_ttree.Dparam (ls, v) ->
      let env = add_global ls v env in
      env

let file uc dl =
  let env = List.fold_left decl (empty_env uc) dl in
  Theory.close_theory env.uc
