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

open Why3
open Cfg_ast
open Ptree

(* Todo use labeled graph *)
module G = Graph.Imperative.Digraph.Concrete (struct
  type t = label

  let equal a b = a.id_str = b.id_str
  let compare a b = String.compare a.id_str b.id_str
  let hash a = Hashtbl.hash a.id_str
end)

module Dom = Graph.Dominator.Make (G)
module Topo = Graph.WeakTopological.Make (G)

let rec targets (t : cfg_term) : label list =
  match t.cfg_term_desc with
  | CFGgoto l -> [ l ]
  | CFGswitch (_, brs) -> List.fold_left (fun acc (_, a) -> targets a @ acc) [] brs
  | CFGreturn _ -> []
  | CFGabsurd -> []

type labeled_block = label * block
type usage = Multi | One

type exp_tree =
  | Scope of label * usage * exp_tree * exp_tree
  | Loop of (loop_clause * ident option * Ptree.term * int option ref) list * exp_tree
  | Block of labeled_block

let rec _print_exp_structure' exp =
  match exp with
  | Scope (lbl, _, tgt, exp) ->
      Format.printf "Scope( %s = " lbl.id_str;
      _print_exp_structure' tgt;
      Format.printf " in ";
      _print_exp_structure' exp;
      Format.printf ")"
  | Loop (_, exp) ->
      Format.printf "Loop[  ";
      _print_exp_structure' exp;
      Format.printf "]"
  | Block (l, _) -> Format.printf "Block(%s)" l.id_str

let graph_from_blocks (bl : (label * block) list) : G.t =
  let g = G.create () in
  List.iter
    (fun (source, (_, t)) ->
      let target_label = targets t in
      G.add_vertex g source;
      List.iter (fun target -> G.add_edge g source target) target_label)
    bl;
  g

exception NotReducible of (string * string)
exception NotConnected of G.V.t list

let () =
  Exn_printer.register (fun fmt exn ->
      match exn with
      | NotReducible (n1, n2) ->
          Format.fprintf fmt "CFG is not a reducible graph. The nodes %s %s belong to a cycle with multiple entries" n1
            n2
      | NotConnected s ->
          Format.fprintf fmt
            "CFG is not a connected graph. The following nodes are not reachable from the start block: ";
          List.iter (fun el -> Format.printf "%s" el.id_str) s
      | _ -> raise exn)

module Sint = Extset.Make (struct
  type t = label

  let compare a b = String.compare a.id_str b.id_str
end)

let _graph_is_reducible (g : G.t) (dom : G.V.t -> G.V.t -> bool) (entry : label) =
  let visited = ref Sint.empty in
  let to_visit = Stack.create () in
  Stack.push entry to_visit;

  while not (Stack.is_empty to_visit) do
    let node = Stack.pop to_visit in
    visited := Sint.add node !visited;

    G.iter_succ
      (fun succ ->
        if not (Sint.mem succ !visited) then Stack.push succ to_visit
        else if (* back-edge *)
                not (dom succ node) then raise (NotReducible (succ.id_str, node.id_str)))
      g node
  done;
  (* graph is connected *)
  let unreached = G.fold_vertex (fun v u -> if not (Sint.mem v !visited) then Sint.add v u else u) g Sint.empty in
  if not (Sint.is_empty unreached) then raise (NotConnected (Sint.elements unreached));
  ()

let rec entry e = match e with Block b -> b | Loop (_, h) -> entry h | Scope (_, _, _, h) -> entry h
(* unused | _ -> assert false *)

let mk_scope label usage tgt body = Scope (label, usage, tgt, body)

let rec treeify_from_components pred dom (prev : exp_tree option) blocks (wto : label Graph.WeakTopological.t) :
    exp_tree =
  Option.get
    (Graph.WeakTopological.fold_left
       (fun prev c ->
         let e = treeify_component pred dom blocks c in
         let lbl = fst (entry e) in
         let forward_preds = List.filter (fun pred -> not (dom lbl pred)) (pred lbl) in
         let usage = if List.length forward_preds > 1 then Multi else One in
         match prev with Some prev -> Some (mk_scope lbl usage e prev) | None -> Some e)
       prev wto)

and treeify_component pred dom blocks (wto : label Graph.WeakTopological.element) : exp_tree =
  let open Graph.WeakTopological in
  match wto with
  | Vertex b -> Block (List.find (fun (l, _) -> l.id_str = b.id_str) blocks)
  | Component (v, b) ->
      let rec split_invariants = function
        | { cfg_instr_desc = CFGinvariant is } :: xs ->
            let invs, stmts = split_invariants xs in
            (is @ invs, stmts)
        | [] -> ([], [])
        | a -> ([], a)
      in
      let l, (s, t) = List.find (fun (l, _) -> l.id_str = v.id_str) blocks in
      let invariants, stmts = split_invariants s in

      Loop (invariants, treeify_from_components pred dom (Some (Block (l, (stmts, t)))) blocks b)

and treeify pred dom cs = treeify_from_components pred dom None cs

let stackify (bl : labeled_block list) (entry : label) : exp_tree =
  let g = graph_from_blocks bl in
  let idom = Dom.compute_idom g entry in
  let dom = Dom.idom_to_dom idom in

  (* graph_is_reducible g dom entry; *)
  let comps = Topo.recursive_scc g entry in
  let t = treeify (G.pred g) dom bl comps in
  t
