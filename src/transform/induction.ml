(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
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

open Ident
open Ty
open Term
open Decl
open Theory
open Task




(** TODO use this label in the following function *)
let label_induction = create_label "induction"

let desc_labels = [label_induction,
                   ("Make the induction on the labeled variables." :
                       Pp.formatted)]


(*********************************************************)
(*******      Data type induction principle      *********)
(*********************************************************)

(*INDUCTION SCHEME*)

(*Induction scheme for some algebraic recursive datatype. For example: 
type tree 'a = Leaf | Node (tree 'a) 'a (tree 'a) 
tyscheme(tree 'a) = [Leaf "->" emptyset; Node l x r "->" (l,r)]*)
type tyscheme = (pattern * Svs.t) list


(*QUANTIFIERS GENERALIZATION INSIDE INDUCTION HYPOTHESES*)

(*an information for induction hypothesis construction on some 
induction variable, taking into account its type's induction scheme
and initial quantifier order. 
For example, if initial formula is Va.Vx3.Vb.Vx1.Vc.Vx2.Vd F(x1,x2,x3), and
the lex. order of induction is (x1,x2,x3), then
vlex(x1) = {x1; b; (x3,c,x2,d); x1.type.tyscheme},
vlex(x2) = {x2; c; (x3,d); x2.type.tyscheme},
vlex(x1) = {x3; a; (b,c,d); x3.type.tyscheme}*)
type vlex =
    {vs: vsymbol;       (*variable*)
     lq: vsymbol list;  (*left immediate neutral quantifiers *)
     rq: vsymbol list;  (*generalized neutral and induction quantifiers *)
     ts: tyscheme       (*type scheme following its definition*)
    }


(*HEURISTIC CANDIDATES FOR INDUCTION TACTIC *)

(*Definitions for Svsl : "Set of variable symbol list". 
  Each list corresponds to the largest prefix of some recursive function
  decreasing argument list, where arguments are instanciated 
  with call actual parameters and recognized as possibles induction candidates
  if they are variables themselves. 
  
  Note, that first are compared lists length, otherwise comparison is made on 
  lexicographic order of vsymbols. Empty list corresponds to non-recurisve 
  functions calls  
  
  This definitions and methods using them are without use if some induction tags
  are provided in the goal by user.*)  
module VsList =
struct
  type t = vsymbol list
  let hash = Hashcons.combine_list vs_hash 3
  let equal = Util.list_all2 vs_equal
  let cmp_vs vs1 vs2 = Pervasives.compare (vs_hash vs2) (vs_hash vs1)
  let compare t1 t2 = 
    let rec aux t1 t2 = match t1,t2 with
      | [],[] -> 0
      | v1 :: q1, v2 :: q2 ->
	if vs_equal v1 v2 
	then aux q1 q2 
	else cmp_vs v1 v2
      | _ -> assert false; 
    in
    if List.length t1 < List.length t2 then -1
    else if List.length t1 > List.length t2 then 1
    else aux t1 t2
end
module Mvsl = Stdlib.Map.Make(VsList)
module Svsl = Mvsl.Set    

(* DEBUGGING AND PRINTING *)

let debug = Debug.register_info_flag "induction"
  ~desc:"About@ the@ transformation@ of@ the@ goal@ using@ induction."

let debug_verbose = Debug.register_info_flag "induction-verbose"
  ~desc:"Same@ as@ induction, but@ print@ also@ the@ variables, the@ \
         heuristics@ and@ the lexicographic@ order@ used."

let print_ty_skm skm =
  List.iter
    (fun (p,svs) ->
      Format.printf "@[| %a : @]" Pretty.print_pat p;
      Svs.iter (Format.printf "%a " Pretty.print_vs) svs;
      Format.printf "@.")
    skm;
  Pretty.forget_all ()

let print_vset vset =
  let aux vl =
    Format.printf "[ ";
    List.iter (Format.printf "%a " Pretty.print_vs) vl;
    Format.printf "] " 
  in
  Format.printf "************** t_candidates_lex *****************\n";
  Format.printf "Candidates found : %d @." (Svsl.cardinal vset);
  Format.printf "Candidates : [ ";
  Svsl.iter (fun vl -> aux vl) vset;
  Format.printf "]\n@.";
  Pretty.forget_all ()
    
let print_heuristic_lex vl =
  let _,ivm = List.fold_left (fun (i,m) v -> 
    (i+1, Mvs.add v i m)) (0,Mvs.empty) vl in
  Format.printf "**************** heuristic_lex ******************\n";
  Format.printf "Induction variables (in lexicographic order): [ ";
  List.iter (Format.printf "%a " Pretty.print_vs) vl;
  Format.printf "]@.";
  Format.printf "Lex. order map : [ ";
  Mvs.iter (fun v i -> Format.printf "%a -> %d; " Pretty.print_vs v i) ivm;
  Format.printf "]\n@.";
  Pretty.forget_all ()

let print_lex lexl =
  let rec aux = function
    | [] -> ()
    | v :: tl ->
      Format.printf "\n%a : [ " Pretty.print_vs v.vs;
      List.iter (Format.printf "%a " Pretty.print_vs) v.lq;
      Format.printf "] [ ";
      List.iter (Format.printf "%a " Pretty.print_vs) v.rq;
      Format.printf "]@.";
      Format.printf "--- Type scheme --- \n";
      print_ty_skm v.ts;
      Format.printf "------------------- \n";
      aux tl
  in
  Format.printf "******************* qsplit_lex ******************\n";
  Format.printf "Induction variables (in the initial order): ";
  List.iter (fun v -> Format.printf "%a " Pretty.print_vs v.vs ) lexl;
  Format.printf "@.(Variable) (Introduced) (Generalized)\n";
  aux lexl;
  Pretty.forget_all ()

(*****************************************************************************)
(******************** INDUCTION BASED ON TYPE DEFINITIONS ********************)
(************************* WITH LEXICOGRAPHIC ORDER **************************)
(*****************************************************************************)


let split_quantifiers x qvl =
  let rec aux left = function
    | hd :: tl when vs_equal x hd -> List.rev left, tl
    | hd :: tl -> aux (hd :: left) tl
    | [] -> assert false
  in aux [] qvl

(*INITIAL FORMULA SPLIT*)
let decompose_forall t =
  let rec aux qvl_acc t = match t.t_node with
    | Tquant (Tforall, qt) ->
      let qvl, _, t = t_open_quant qt in aux (qvl_acc @ qvl) t
    | _ -> qvl_acc, t
  in
  let qvl, t = aux [] t in (List.fold_right Svs.add qvl Svs.empty), qvl, t





let qvl_labeled qvl = 
  List.filter (fun v -> 
    let slab = Slab.filter (fun v -> 
      v.lab_string = "induction") v.vs_name.id_label 
    in not (Slab.is_empty slab)) qvl

(*HEURISTICS SEARCH FOR CANDIDATES IN THE BODY OF THE FORMULA*)
(* This function collects lists of variables corresponding to
   some recursive functions call parameters into the body of formula, 
   if no user made induction tag is provided. 
   
   If some user tags are provided, this function will return the corresponding 
   list of variables will be returned according to the order of tags 
   (from left to right).  
   
   Otherwise, each list respects the lexicographic order of the corresponding 
   recusrive function in which decrease its formal arguments.
   
   Note that one list contain the biggest lexicographic order prefix where all
   actual parameters are variables. For example, if function f(x,a,y,b,z) 
   decreases on [a;b], but is called with some not-variable term T for argument
   b, then the resulting list will be [a]. 
*)
let t_candidates_lex km qvs labeledvl t =
  (* let int_candidates _tl acc = acc 
   List.fold_left (fun acc t -> match t.t_node with
     | Tvar x when Svs.mem x qvs && ty_equal x.vs_ty ty_int -> 
     Svls.add [x] acc
     | _ -> acc) acc tl *) 
  let rec_candidates il tl acc =
    let rec aux il vl = match il with
      | i :: iq ->
	begin match (List.nth tl i).t_node with
	  | Tvar x when Svs.mem x qvs ->
	    begin match x.vs_ty.ty_node with
	      | Tyvar _ -> vl
	      | Tyapp _ -> aux iq (x :: vl)
	    end
	  | _ -> vl
	end
      | [] -> vl
    in 
    
    Svsl.add (List.rev (aux il [])) acc
  in
  let defn_candidates (ls,tl) acc = match (find_logic_definition km ls) with
    | Some defn -> 
      let acc = acc (*int_candidates tl acc*) in
      rec_candidates (ls_defn_decrease defn) tl acc
    | None -> acc
  in
  let rec t_candidates acc t =
    let acc = match t.t_node with
      | Tapp (ls, tl) -> defn_candidates (ls, tl) acc
      | _ ->  acc
    in t_fold t_candidates acc t
  in
  if labeledvl <> [] 
  then Svsl.add labeledvl Svsl.empty 
  else t_candidates Svsl.empty t
    
    
exception No_candidates_found

(*Chooses leftmost (in the formula's quantifiers list ) candidate list 
from the subset of lists of the biggest size ; raises an exception, 
if the candidate set is empty or contains only an empty list, *)
let heuristic_lex vset =
  try 
    let vl = Svsl.max_elt vset in
    if vl = []
    then raise No_candidates_found
    else vl
  with Not_found -> raise No_candidates_found
    

(*Generates induction scheme for one variable of some algebraic datatype 
  according to datatype's definition *)
let vs_tyscheme km x =
  let ts,ty = match x.vs_ty.ty_node with
    | Tyapp _ when ty_equal x.vs_ty ty_int -> assert false
    | Tyvar _ ->   assert false
    | Tyapp (ts, _) -> ts, ty_app ts (List.map ty_var ts.ts_args)
  in
  let sigma = ty_match Mtv.empty ty x.vs_ty in
  let ty_str ty =
    let s = match ty.ty_node with
      | Tyapp (ts, _) -> ts.ts_name.id_string
      | Tyvar tv -> tv.tv_name.id_string
    in if s = "" then "x" else String.make 1 s.[0]
  in
  let ty_vs ty =
    let ty = ty_inst sigma ty in
    Term.create_vsymbol (Ident.id_fresh (ty_str ty)) ty
  in
  let tyscheme_constructor (ls, _) =
    let vlst = List.map ty_vs ls.ls_args in
    let plst = List.map pat_var vlst in
    let vset = List.fold_left
      (fun s v -> if ty_equal x.vs_ty v.vs_ty then Svs.add v s else s)
      Svs.empty vlst
    in pat_app ls plst x.vs_ty, vset
  in
  let cl = find_constructors km ts in
  ((List.map tyscheme_constructor cl) : tyscheme)

(* Preprocesses selected induction candidate list for 
   induction scheme instanciation.*)
let qsplit km vl qvl  = 
  let rec aux (ivs,ivm) qvl lql lvl acc = match qvl with
    | [] -> List.rev acc, lql
    | q :: tl ->
      if Svs.mem q ivs 
      then
	let qi = Mvs.find q ivm in
	let rleft = List.filter (fun v -> (Mvs.find v ivm) > qi) lvl in
	let rright = List.filter
	  (fun v -> if (Mvs.mem v ivm) then (Mvs.find v ivm) > qi else true) tl
	in
	let v = {
	  vs = q;
	  lq = List.rev lql;
	  rq = (List.rev rleft) @ rright;
	  ts =  vs_tyscheme km q} in
	aux ((Svs.remove q ivs),ivm) tl [] (q :: lvl) (v :: acc)
      else
	if Svs.is_empty ivs 
	then List.rev acc, qvl 
	else aux (ivs,ivm) tl (q :: lql) lvl acc
  in 
  let _, ivs, ivm = List.fold_left (fun (i,s,m) v -> 
    (i+1, Svs.add v s, Mvs.add v i m)) (0,Svs.empty,Mvs.empty) vl in
  aux (ivs,ivm) qvl [] [] []

let make_induction_lex lexl rql t = 
  let make_h v vset timp = 
    Svs.fold (fun x timp -> 
      let t = t_subst_single v.vs (t_var x) t in
      let t = t_forall_close v.rq [] t in
      Term.t_implies t timp) vset timp  
  in
  let rec aux lexl timp = match lexl with
    | [] -> timp
    | v :: vl -> 
      let tbl = List.map (fun (pat, vset) -> 
	let timp = (make_h v vset timp) in 
	t_close_branch pat (aux vl timp)) v.ts in
      let t = t_case (t_var v.vs) tbl in
      let t = t_forall_close (v.lq @ [v.vs]) [] t in t
  in aux lexl (t_forall_close rql [] t)

let induction_ty_lex km t0 =
  let qvs, qvl, t = decompose_forall t0 in
  let lblvl = qvl_labeled qvl in
  let vset = t_candidates_lex km qvs lblvl t in
  try
    let vl = heuristic_lex vset in
    let lexl, rightmost_qvl = qsplit km vl qvl in
    let tcase = make_induction_lex lexl rightmost_qvl t in
    
    if Debug.test_flag debug_verbose then
      begin
	print_vset vset;
	print_heuristic_lex vl;
	print_lex lexl; 
	Format.printf "Old Task: %a \n@." Pretty.print_term t0;
	Format.printf "New Task: %a \n@." Pretty.print_term tcase 
      end;
    if Debug.test_flag debug then
      begin
	Format.printf "Old Task: %a \n@." Pretty.print_term t0;
	Format.printf "New Task: %a \n@." Pretty.print_term tcase 
      end;
    [tcase]
  with No_candidates_found -> Format.printf "No candidates found\n"; [t0]

let induction_ty_lex = function
  | Some { task_decl = { td_node = Decl { d_node = Dprop (Pgoal, pr, f) } };
	   task_prev = prev;
	   task_known = km } ->
    List.map (add_prop_decl prev Pgoal pr) (induction_ty_lex km f)
  | _ -> assert false


let () =
  Trans.register_transform_l "induction_ty_lex" (Trans.store induction_ty_lex)
    ~desc_labels ~desc:"TODO: induction on type with lexicographic order"

(***************************************************************************)
(********************** INDUCTION TACTIC FOR INTEGERS **********************)
(***************************************************************************)
let filter_int v = ty_equal v.vs_ty ty_int


(*HEURISTICS SEARCH FOR CANDIDATES IN THE BODY OF THE FORMULA*)
let t_candidates filter km qvs t =
  let int_candidate = (fun acc t ->
    match t.t_node with
      | Tvar x when Svs.mem x qvs && ty_equal x.vs_ty ty_int ->
	Svs.add x acc
      | _ -> acc)
  in
  let arg_candidate = (fun acc t ->
    match t.t_node with
      | Tvar x when Svs.mem x qvs ->
	begin match x.vs_ty.ty_node with
	  | Tyvar _ -> acc
	  | Tyapp _ -> Svs.add x acc
	end
      | _ -> acc)
  in
  let defn_candidate = (fun vs_acc ls tl ->
    match (find_logic_definition km ls) with
      | Some defn ->
	let vs_acc = List.fold_left int_candidate vs_acc tl in
	begin match ls_defn_decrease defn with
	  | [i] -> arg_candidate vs_acc (List.nth tl i)
	  | h :: _ ->
	    arg_candidate vs_acc (List.nth tl h)
	  | _ ->  vs_acc
	end
      | None -> vs_acc)
  in
  let rec t_candidate vs_acc t =
    let vs_acc = match t.t_node with
      | Tapp (ls, tl) -> defn_candidate vs_acc ls tl
      | _ ->  vs_acc
    in t_fold t_candidate vs_acc t
  in Svs.filter filter (t_candidate Svs.empty t)

(*CANDIDATE SELECTION*)
let heuristic_svs vset = Svs.choose vset

let int_strong_induction (le_int,lt_int) x t =

  let k = Term.create_vsymbol (Ident.id_clone x.vs_name) ty_int in
  (* 0 <= k < x *)
  let ineq = t_and (ps_app le_int [t_int_const "0"; t_var k])
    (ps_app lt_int [t_var k; t_var x]) in
  (* forall k. 0 <= k < x -> P[x <- k] *)
  let ih =
    t_forall_close [k] [] (t_implies ineq (t_subst_single x (t_var k) t)) in
  t_forall_close [x] [] (t_implies ih t)

let induction_int km (le_int,lt_int) t0 =
  let qvs, qvl, t = decompose_forall t0 in
  let vset = t_candidates filter_int km qvs t in
  if Svs.is_empty vset
  then [t0]
  else begin
    let x = heuristic_svs vset in
    let qvl1, qvl2 = split_quantifiers x qvl in
    let t = t_forall_close qvl2 [] t in
    let t = int_strong_induction (le_int,lt_int) x t in
    let t = t_forall_close qvl1 [] t in
    if Debug.test_flag debug then
    (Format.printf "Old Task: %a \n@." Pretty.print_term t0;
     Format.printf "New Task: %a \n@." Pretty.print_term t);
    [t]
  end

let induction_int th_int = function
  | Some
      { task_decl = { td_node = Decl { d_node = Dprop (Pgoal, pr, f) } };
	task_prev = prev; task_known = km } as t ->
    begin
      try
	let le_int = ns_find_ls th_int.th_export ["infix <="] in
	let lt_int = ns_find_ls th_int.th_export ["infix <"] in
	if not (Mid.mem le_int.ls_name km) then raise Exit;
	List.map (add_prop_decl prev Pgoal pr)
	  (induction_int km (le_int, lt_int) f)
      with Exit -> [t] end
  | _ -> assert false


let () =
  Trans.register_env_transform_l "induction_int"
    (fun env ->
      let th_int = Env.find_theory env ["int"] "Int" in
      Trans.store (induction_int th_int))
    ~desc_labels ~desc:"TODO: induction on integers"

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3.byte"
End:
*)
