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

open Ident
open Ty
open Term
open Decl
open Theory
open Task
open Args_wrapper

let attr_ind = create_attribute "induction"
let attr_inv = create_attribute "inversion"

type context = {
 c_node  : context_node;
 c_attrs : Sattr.t;
 c_loc   : Loc.position option }

and context_node =
 | Hole
 | Clet of vsymbol * term * context
   (* triggers are forgotten on purpose *)
 | Cforall of vsymbol list * context
 | Cimplies of term * context


exception Ind_not_found

let make_context node term =
 { c_node = node; c_attrs = term.t_attrs; c_loc = term.t_loc }


let make_context_ctx node context =
 { c_node = node; c_attrs = context.c_attrs; c_loc = context.c_loc }

(* Locate induction term in [t]: either leftmost inductive on
   the implication chain, or the one tagged with [attr].
   If found, return [ctx, (ls,argl,cl), rhs] where:
     [ctx] is the context in which term is found
       (leftmost part of the context at top, e.g term with hole)
     [ls] is the inductive symbol
     [argl] are the argument with which the inductive symbol is
       instantiated
     [cl] are the inductive symbol clauses
     [rhs] is the part of the term 'right' to the induction term
     ([t] is decomposed as ctx[ls(argl) -> rhs])
   If not found, raise Ind_not_found *)
let locate kn attr t =
  let rec locate_inductive find_any t = match t.t_node with
    | Tlet (t1, tb) ->
      let vs,t2 = t_open_bound tb in
      let ctx, ind, goal = locate_inductive find_any t2 in
      make_context (Clet (vs, t1, ctx)) t, ind, goal
    | Tquant(Tforall, tq) ->
      let vsl, _, t1 = t_open_quant tq in
      let ctx, ind, goal = locate_inductive find_any t1 in
      make_context (Cforall (vsl, ctx)) t, ind, goal
    | Tbinop (Timplies, lhs, rhs) ->
      let locate_rhs find_any =
        let ctx, ind, goal = locate_inductive find_any rhs in
        make_context (Cimplies (lhs, ctx)) t, ind, goal in
      let has_attr () = Sattr.mem attr lhs.t_attrs
      in if find_any || (has_attr ())
        then
          match lhs.t_node with
            | Tapp (ls, argl) ->
              begin
                match (Mid.find ls.ls_name kn).d_node with
                | Dind (Ind, dl) ->
                  let cl = List.assq ls dl in
                  if find_any && not (has_attr ()) then
                    (* take first tagged inductive in rhs if any.
                       Otherwise, take lhs *)
                    try
                      locate_rhs false
                    with Ind_not_found ->
                      make_context Hole t, (ls, argl, cl), rhs
                  else
                    (* here attr has been found *)
                    make_context Hole t, (ls, argl, cl), rhs
                | Dind _ | Dlogic _ | Dparam _ | Ddata _ -> locate_rhs find_any
                | Dtype _ | Dprop _ -> assert false
              end
            | _  -> locate_rhs find_any
        else locate_rhs find_any
    | _  -> raise Ind_not_found
  in locate_inductive true t

(* Find arguments of the inductive that are unchanged
   within recursion. *)
type 'a matching =
  | Any
  | Equal of 'a
  | Nothing

let matching eq a b = match a with
  | Any -> Equal b
  | Equal a when eq a b -> Equal a
  | _ -> Nothing

(* Identify parameters of an inductive declaration. *)
let parameters ls cl =
  let rec explore l t =
    let l = match t.t_node with
    | Tapp (ls2, args) when ls_equal ls ls2 ->
      List.map2 (matching t_equal) l args
    | _ -> l
    in
    t_fold explore l t
  in
  let clause l (_,c) =
    List.map (function Nothing -> Nothing | _ -> Any) (explore l c)
  in
  let l = List.map (fun _ -> Any) ls.ls_args in
  let l = List.fold_left clause l cl in
  List.map (function Nothing -> false | _ -> true) l

(* Partition [ctx] into two contexts,
   the first one containing the part independent on [vsi]
   and the second one containing the part that depends on [vsi].
   input [ctx] is taken as a term with hole,
   and outputs are in reverse order (e.g zippers) *)
let partition ctx vsi =
  let rec aux ctx vsi_acc cindep cdep = match ctx.c_node with
    | Hole -> cindep, cdep
    | Cimplies (t, ctx2) ->
      let add c = make_context_ctx (Cimplies (t, c)) ctx in
      let cindep, cdep =
        let fvs = t_vars t in
        if Mvs.is_empty (Mvs.set_inter fvs vsi_acc)
        then add cindep, cdep
        else cindep, add cdep in
      aux ctx2 vsi_acc cindep cdep
    | Cforall (vsl, ctx2) ->
      let add c = function
        | []  -> c
        | vl  -> make_context_ctx (Cforall (vl, c)) ctx in
      let vsl = List.filter (fun v -> not (Mvs.mem v vsi)) vsl in
      let vdep, vindep = List.partition (fun v -> Mvs.mem v vsi_acc) vsl in
      aux ctx2 vsi_acc (add cindep vindep) (add cdep vdep)
    | Clet (vs, t, ctx2) ->
      if Mvs.mem vs vsi
      then
        let t = t_equ (t_var vs) t in
        let cdep = make_context_ctx (Cimplies (t, cdep)) ctx in
        aux ctx2 vsi_acc cindep cdep
      else
        let add c = make_context_ctx (Clet (vs, t, c)) ctx in
        let fvs = t_vars t in
        if Mvs.is_empty (Mvs.set_inter fvs vsi_acc)
        then aux ctx2 vsi_acc (add cindep) cdep
        else aux ctx2 (Mvs.add vs 1 vsi_acc) cindep (add cdep)
  in
  let hole = make_context_ctx Hole ctx in
  aux ctx vsi hole hole

(* Add equalities between clause variables and parameters. *)
let introduce_equalities vsi paraml argl goal =
  let goal =
    List.fold_left2 (fun g p a -> t_implies (t_equ a p) g) goal paraml argl in
  t_forall_close (Mvs.keys vsi) [] goal

(* Zip term within context. *)
let rec zip ctx goal = match ctx.c_node with
  | Hole -> goal
  | Cimplies (t, ctx2)  -> zip ctx2
      (t_attr_set ?loc:ctx.c_loc ctx.c_attrs (t_implies t goal))
  | Cforall (vsl, ctx2) -> zip ctx2
      (t_attr_set ?loc:ctx.c_loc ctx.c_attrs (t_forall_close vsl [] goal))
  | Clet (vs, t, ctx2)  -> zip ctx2
      (t_attr_set ?loc:ctx.c_loc ctx.c_attrs (t_let_close vs t goal))

(* Replace clause by the associated inductive case. *)
let substitute_clause induct vsi ls argl goal c =
  let sigma = ls_arg_inst ls argl in
  let c = t_ty_subst sigma Mvs.empty c in
  let rec subst keepi t = match t.t_node with
    | Tapp (ls', paraml) when ls_equal ls ls' ->
      let t2 () = introduce_equalities vsi paraml argl goal in
        if keepi then
          if induct && List.for_all2
            (fun a b -> Opt.equal ty_equal a.t_ty b.t_ty) argl paraml
          then t_and t (t2 ())
          (* FIXME: in case of polymorphic recursion we do not generate IHs *)
          else t
        else t2 ()
    | _  -> t_map (subst keepi) t in
  let rec aux t = match t.t_node with
    | Tlet (t1, tb) ->
      let vs, t2, cb = t_open_bound_cb tb in
      t_attr_copy t (t_let t1 (cb vs (aux t2)))
    | Tquant(Tforall, tq) ->
      let vsl, tr, t1, cb = t_open_quant_cb tq in
      t_attr_copy t (t_forall (cb vsl tr (aux t1)))
    | Tbinop (Timplies, lhs, rhs) ->
      t_attr_copy t (t_implies (subst true lhs) (aux rhs))
    | _ -> subst false t
  in aux c

let induction_l attr induct kn t =
  let (ctx, (ls, argl, cl), goal) = locate kn attr t in
  let fold vsi p t = if p then vsi else t_freevars vsi t in
  let vsi = List.fold_left2 fold Mvs.empty (parameters ls cl) argl in
  let cindep, cdep = partition ctx vsi in
  let goal = zip cdep goal in
  List.map (fun (_,c) ->
    zip cindep (substitute_clause induct vsi ls argl goal c)) cl

let induction_l attr induct task = match task with
  | Some { task_decl ={ td_node = Decl { d_node = Dprop (Pgoal, pr, f) } };
	   task_prev = prev;
	   task_known = kn } ->
    begin try List.map (add_prop_decl prev Pgoal pr) (induction_l attr induct kn f)
    with Ind_not_found -> [task] end
  | _ -> assert false

let induction_on_hyp attr b h =
  Trans.compose (Ind_itp.revert_tr_symbol [Tsprsymbol h])
    (Trans.store (induction_l attr b))

let () = wrap_and_register
    ~desc:"induction_arg_pr <pr> performs induction_pr on pr."
    "induction_arg_pr"
    (Tprsymbol Ttrans_l) (induction_on_hyp attr_ind true)

let () = wrap_and_register
    ~desc:"induction_arg_pr <pr> performs inversion_pr on pr."
    "inversion_arg_pr"
    (Tprsymbol Ttrans_l) (induction_on_hyp attr_inv false)

let () =
  Trans.register_transform_l "induction_pr" (Trans.store (induction_l attr_ind true))
    ~desc:"Generate@ induction@ hypotheses@ for@ goals@ over@ inductive@ predicates."

let () =
  Trans.register_transform_l "inversion_pr" (Trans.store (induction_l attr_inv false))
    ~desc:"Invert@ inductive@ predicate."


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3.byte"
End:
*)
