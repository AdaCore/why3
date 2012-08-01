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


(*********************************************************)
(*******      Data type induction principle      *********)
(*********************************************************)

(**********************************************************************)
(*Algebraic datatype induction scheme *)
type tyscheme = (pattern * Svs.t) list


(*A induction scheme variable*)
type vlex =
    {vs: vsymbol;       (*variable*)
     lq: vsymbol list;  (*left immediate neutral quantifiers *)
     rq: vsymbol list;  (*generalized neutral and induction quantifiers *)
     ts: tyscheme       (*type scheme following its definition*)
    }

(*Definitions for Svsl : "Set of variable symbol list". 
  Each list corresponds to the largest prefix of some recursive function
  decreasing argument list, where arguments are instanciated 
  with call actual parameters and recognized as possibles induction candidates
  if they are variables themselves. 
  
  Note, that first are compared lists length, otherwise comparison is made on 
  lexicographic order of vsymbols. Empty list corresponds to non-recurisve 
  functions calls  
  
  This definitions and methods using them are without use if some induction tags
  are provided in the goal by user.
*)  
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

(**************************** PRINTING ***************************************)
let debug = Debug.register_flag "induction"
  ~desc:"About@ the@ transformation@ of@ the@ goal@ using@ induction."

let debug_verbose = Debug.register_flag "induction-verbose"
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


(**********************************************************************)
let tyscheme_inst f (km : Decl.known_map) x tx  =
  let inst_branch = (fun (p, vset) ->
    t_close_branch p ( Svs.fold (fun v tacc ->
      (Term.t_implies (t_subst_single x (t_var v) tx) tacc )) vset tx))
  in
  t_case (t_var x) (List.map inst_branch ((f km x tx) : tyscheme))


let split_quantifiers x qvl =
  let rec aux left = function
    | hd :: tl when vs_equal x hd -> List.rev left, tl
    | hd :: tl -> aux (hd :: left) tl
    | [] -> assert false
  in aux [] qvl


let decompose_forall t =
  let rec aux qvl_acc t = match t.t_node with
    | Tquant (Tforall, qt) ->
      let qvl, _, t = t_open_quant qt in aux (qvl_acc @ qvl) t
    | _ -> qvl_acc, t
  in
  let qvl, t = aux [] t in (List.fold_right Svs.add qvl Svs.empty), qvl, t


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

let heuristic_svs vset = Svs.choose vset

let filter_tydef v = not (ty_equal v.vs_ty ty_int)

(* Decl.known_map -> Term.vsymbol -> Term.term -> tyscheme *)
let tyscheme_vsty km x (_t : Term.term) =
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
      (fun s v ->
	if ty_equal x.vs_ty v.vs_ty then Svs.add v s else s)
      Svs.empty vlst
    in pat_app ls plst x.vs_ty, vset
  in
  let cl = find_constructors km ts in
  ((List.map tyscheme_constructor cl) : tyscheme)


let induction_ty km t0 =
  let qvs, qvl, t = decompose_forall t0 in
  let vset = t_candidates filter_tydef km qvs t in
  if Svs.is_empty vset then [t0]
  else
    let x  =  heuristic_svs vset in
    let qvl1, qvl2 = split_quantifiers x qvl in
    let t = t_forall_close qvl2 [] t in
    let tcase = tyscheme_inst tyscheme_vsty km x t in
    let tcase = t_forall_close [x] [] tcase in
    let tcase = t_forall_close qvl1 [] tcase in
    if Debug.test_flag debug then
      begin

	Format.printf "Old Task: %a \n@." Pretty.print_term t0;
	Format.printf "New Task: %a \n@." Pretty.print_term tcase
      end;
    [tcase]

(*****************************************************************************)
(******************** INDUCTION BASED ON TYPE DEFINITIONS ********************)
(************************* WITH LEXICOGRAPHIC ORDER **************************)
(*****************************************************************************)

(** TODO use this label in the following function *)
let label_induction = create_label "induction"

let qvl_labeled qvl = 
  List.filter (fun v -> 
    let slab = Slab.filter (fun v -> 
      v.lab_string = "induction") v.vs_name.id_label 
    in not (Slab.is_empty slab)) qvl


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
    (*Format.printf "[";
    List.iter (fun i ->
      Format.printf "[%d : %a]" i Pretty.print_term (List.nth tl i)) il;
    Format.printf "]@.";*)
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

(*Chooses leftmost (in the formula's quantifiers list ) candidate list from the subset of lists 
  of the biggest size ; raises an exception, if the candidate set is empty 
  or contains only an empty list, *)
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
   induction scheme instanciation.  
*)
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

(*****************************************************************************)
(******************** INDUCTION BASED ON FUNCTION DEFINITION *****************)
(************************* WITH LEXICOGRAPHIC ORDER **************************)
(*****************************************************************************)

type htree = | Snode of (vsymbol * pattern * htree) list
	     | Sleaf of Svs.t (*here (int, vsymbol) set*)

let empty = Sleaf Svs.empty


let defn_candidates_lex km qvs t = 
  let rec are_vars il tl = match il with
    | i :: iq ->
      begin match (List.nth tl i).t_node with
	| Tvar x when Svs.mem x qvs ->
	  begin match x.vs_ty.ty_node with
	    | Tyvar _ -> are_vars iq tl
	    | Tyapp _ -> false 
	  end
	| _ -> false
      end
    | [] -> true
  in
  let defn_candidates (ls,tl) acc = match (find_logic_definition km ls) with
    | Some defn -> 
      let il = ls_defn_decrease defn in
      if (are_vars il tl) then Mls.add ls (il, defn) acc else acc
    | None -> acc
  in
  let rec t_candidates acc t =
    let acc = match t.t_node with
      | Tapp (ls, tl) -> defn_candidates (ls, tl) acc
      | _ ->  acc
    in t_fold t_candidates acc t
  in
  t_candidates Mls.empty t


let defn_htree fname x i t =
  let rec t_htree acc t =
    match t.t_node with
      | Tcase ({t_node = (Tvar y)}, bl) when ty_equal x.vs_ty y.vs_ty ->
	case_htree acc y bl
      | Tapp (ls, tl) when ls_equal ls fname ->
	begin
	  match (List.nth tl i).t_node with
	    | Tvar y -> push acc (Sleaf (Svs.add y Svs.empty))
	    | _ -> assert false
	end

      | Tapp (_, tl) -> app_htree acc tl
      | _ -> acc

  and app_htree acc tl =
    List.fold_left (fun acc t -> t_htree acc t ) acc tl

  and case_htree acc y bl =
    let ptl = List.map (fun b ->
      let (p,t) = t_open_branch b in (p, t)) bl in
    let sml = List.map (fun (p,t) -> (y, p, t_htree empty t)) ptl in
    push acc (Snode sml)

  and push acc sm = match acc with
    | Snode l -> Snode (List.map (fun (x,p,s) -> (x,p, push s sm)) l)
    | Sleaf svs0 -> match sm with
	| Snode sml ->
	  Snode ((List.map (fun (x,p,s) ->
	    (x,p, push (Sleaf svs0) s)))  sml)
	| Sleaf svs1 -> Sleaf (Svs.union svs0 svs1)
  in
  t_htree (Sleaf Svs.empty) t

(*
let htree_tyscheme _ht = ([] : tyscheme)

(* Decl.known_map -> Term.vsymbol -> Term.term -> tyscheme *)
let tyscheme_fdef_one km x t =
  let (ls, (i, _defn)) = Mls.choose (t_defn_candidates km x t) in
  let ht = defn_htree km ls x i t in
  htree_tyscheme ht

let induction_fun km t0 =
  let qvs, qvl, t = decompose_forall t0 in
  let vset = t_candidates (fun _ -> true) km qvs t in
  if Svs.is_empty vset
  then [t0]
  else
    let x  =  heuristic_svs vset in
    let qvl1, qvl2 = split_quantifiers x qvl in
    let t = t_forall_close qvl2 [] t in
    let t = tyscheme_inst tyscheme_fdef_one km x t in
    let t = t_forall_close [x] [] t in
    let t = t_forall_close qvl1 [] t in
    if Debug.test_flag debug then
      (Format.printf "Old Task: %a \n@." Pretty.print_term t0;
       Format.printf "New Task: %a \n@." Pretty.print_term t);
    [t]

    *)


(**********************************************************************)
let filter_int v = ty_equal v.vs_ty ty_int

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



(********************************************************************)

let induction_ty = function
  | Some { task_decl = { td_node = Decl { d_node = Dprop (Pgoal, pr, f) } };
	   task_prev = prev;
	   task_known = km } ->
    List.map (add_prop_decl prev Pgoal pr) (induction_ty km f)
  | _ -> assert false


let induction_ty_lex = function
  | Some { task_decl = { td_node = Decl { d_node = Dprop (Pgoal, pr, f) } };
	   task_prev = prev;
	   task_known = km } ->
    List.map (add_prop_decl prev Pgoal pr) (induction_ty_lex km f)
  | _ -> assert false


(*
let induction_fun = function
  | Some { task_decl = { td_node = Decl { d_node = Dprop (Pgoal, pr, f) } };
	   task_prev = prev;
	   task_known = km } ->
    List.map (add_prop_decl prev Pgoal pr) (induction_fun km f)
  | _ -> assert false
*)


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



let desc_labels = [label_induction,
                   ("Make the induction on the labeled variables." :
                       Pp.formatted)]


let () =
  Trans.register_transform_l "induction_ty" (Trans.store induction_ty)
    ~desc_labels ~desc:"TODO: induction on type"

let () =
  Trans.register_transform_l "induction_ty_lex" (Trans.store induction_ty_lex)
    ~desc_labels ~desc:"TODO: induction on type with lexicographic order"

(*
let () =
  Trans.register_transform_l "induction_ty_fdef" (Trans.store induction_fun)
    ~desc_labels ~desc:"TODO: induction on type using function definition"
*)

let () =
  Trans.register_env_transform_l "induction_int"
    (fun env ->
      let th_int = Env.find_theory env ["int"] "Int" in
      Trans.store (induction_int th_int))
    ~desc_labels ~desc:"TODO: induction on integers"

(**********************************************************************)
(*TODO

1° km x t -> htree (optimized)
2° htree -> tyscheme

3° defn list -> htree
4° predicate induction
4° benchmark
4° labels à la
  {induction j}
  {induction false}
  {induction_int}
  {induction @1} {induction @2}
  {induction @1 generalize}
5° common tactic
6° mutual recursion
7° lexicographic orders
8° termination criterium
9° warnings
10° indentation

let time = Unix.localtime (Unix.time ()) in
	Format.printf "Last version : %d:%d %d.%d\n"
	  time.Unix.tm_hour time.Unix.tm_min
	  time.Unix.tm_mon time.Unix.tm_mday;


*)




(******************* ATTIC  **********************)
(*
let t_iter_scheme km t =

  let ty_cl ts =
    List.map (fun (ls, _) -> ls ) (find_constructors km ts) in

  let rec t_patc (acc,n) t =
    match t.t_node with
      | Tapp (ls, tl)      -> t_tapp (acc,n) (ls,tl)
      | Tif (c, t1, t2)    -> t_tif (acc,n)  (c, t1,t2)
      | Tlet (t, tb)       -> t_tlet (acc,n) (t,tb)
      | Tcase (t, tbl)     -> t_tcase (acc,n) (t, tbl)
      | Tvar _ | Tconst _  -> acc, n
      | Ttrue | Tfalse | Tnot _ | Tbinop (_, _, _) | Tquant (_,_) -> acc, n
      | Teps _ -> acc,n

  and t_tcase (acc,n) (t0, bl) = match t0.t_node with
    | (Tvar x)  ->
      begin
        match x.vs_ty.ty_node with
          | Tyapp (_, _) ->
            let tpl = List.map
	      (fun b -> let (p,t) = t_open_branch b in (p, t)) bl in
            let sub_ctl =
              List.fold_left (fun acc (_, t) ->
                let ctl,_ = (t_patc ([],(n+1)) t) in ctl @ acc) [] tpl in
            let tpl =
              List.map (fun b -> let (p,t) = t_open_branch b in [p], t) bl
            in
            let patc = Pattern.CompileTerm.compile ty_cl [t0] tpl in
            let acc = ((patc, n) :: sub_ctl) @ acc in
            acc,n
          | _ -> assert false
      end
    | _ ->
      let tl = List.map (fun b -> let (_,t) = t_open_branch b in t) bl in
      List.fold_left (fun (acc,n) t -> t_patc (acc,n) t) (acc,n) tl

  and t_tapp (acc,n) (_ls,tl) =
    List.fold_left (fun (acc,n) t -> t_patc (acc,n) t) (acc,n) tl

  and t_tif (acc,n) (_c,t1,t2) =
    let acc, n = (t_patc (acc,n) t1) in t_patc (acc,n) t2

  and t_tlet (acc,n) (_t,_tb) = acc,n  in


  let acc, _ = t_patc ([],0) t in
  List.iter (fun (pc, n ) ->
    Format.printf "%d: %a \n @." n Pretty.print_term pc  )
    (List.rev acc)



let t_iter_compile_first km t =
  let ty_cl ts =
    List.map (fun (ls, _) -> ls ) (find_constructors km ts) in

  let rec t_patc t =
    match t.t_node with
      | Tapp (_ls, _tl)      -> t (* fs_app ls (List.map t_patc tl) *)
      | Tif (c, t1, t2)    ->  Term.t_if c (t_patc t1) (t_patc t2)
      | Tlet (t, _tb)       -> t (*
	let vs,tb,f = t_open_bound_cb tb in
	t_let t (f vs (t_patc tb)) *)
      | Tcase (t, bl)   ->
	let tpl =
          List.map (fun b -> let (p,t) = t_open_branch b in [p], t) bl
        in
	let ct = Pattern.CompileTerm.compile ty_cl [t] tpl in
	begin
	  match ct.t_node with
	    | Tcase (t, bl) ->
	      let bl =
		List.map (fun b ->
		  let (p,t) = t_open_branch b in
		  t_close_branch p (t_patc t)) bl
	      in
	      Term.t_case t bl
	    | _ -> ct
	end

      | _ -> t
  in
  Format.printf "%a \n @." Pretty.print_term (t_patc t)


t_tcase (acc,n) (t, tbl)
      | _ -> t

  and t_tcase (acc,n) (t0, bl) = match t0.t_node with
    | (Tvar x)  ->
      begin
        match x.vs_ty.ty_node with
          | Tyapp (_, _) ->
	    let tpl =
              List.map (fun b -> let (p,t) = t_open_branch b in [p], t) bl
            in
	    let patc = Pattern.CompileTerm.compile ty_cl [t0] tpl in


	    let tpl = List.map
	      (fun b -> let (p,t) = t_open_branch b in (p, t)) bl in
            let sub_ctl =
              List.fold_left (fun acc (_, t) ->
                let ctl,_ = (t_patc ([],(n+1)) t) in ctl @ acc) [] tpl in
            let tpl =
              List.map (fun b -> let (p,t) = t_open_branch b in [p], t) bl
            in
            let patc = Pattern.CompileTerm.compile ty_cl [t0] tpl in
            let acc = ((patc, n) :: sub_ctl) @ acc in
            acc,n
          | _ -> assert false
      end
    | _ ->
      let tl = List.map (fun b -> let (_,t) = t_open_branch b in t) bl in
      List.fold_left (fun (acc,n) t -> t_patc (acc,n) t) (acc,n) tl

  and t_tapp (acc,n) (_ls,tl) =
    List.fold_left (fun (acc,n) t -> t_patc (acc,n) t) (acc,n) tl

  and t_tif (acc,n) (_c,t1,t2) =
    let acc, n = (t_patc (acc,n) t1) in t_patc (acc,n) t2

  and t_tlet (acc,n) (_t,_tb) = acc,n  in


  let acc, _ = t_patc ([],0) t in
  List.iter (fun (pc, n ) ->
    Format.printf "%d: %a \n @." n Pretty.print_term pc  )
    (List.rev acc)

	 *)







(*
let functional_induction km t0 =
  let qvs, _qvl, t = decompose_forall t0 in
  let vmap = t_collect_data km qvs t in
  let x, lmap =  Mvs.choose vmap in
  let (ls, (i, defn)) = Mls.choose lmap in
  let (_,t) = open_ls_defn defn in
  Format.printf "%a@." print_scheme (make_scheme km ls x i t);
  [t0]

  let _ = Mls.iter (fun _ls (_i,defn) ->
    let (_,t) = open_ls_defn defn in t_iter_compile_first km t) lmap in

  if (Mvs.is_empty vmap)
  then
    [t0]
  else
    [t0]
*)


(*

let functional_induction  = function
  | Some { task_decl = { td_node = Decl { d_node = Dprop (Pgoal, pr, f) } };
           task_prev = prev;
           task_known = km } ->
    List.map (add_prop_decl prev Pgoal pr) (functional_induction km f)
  | _ -> assert false


let () = Trans.register_transform_l
  "induction_on_function_definition"
  (Trans.store functional_induction)
  *)


(*
Local Variables:
compile-command: "unset LANG; make -C ../.."
End:
*)

(*


let rec print_scheme fmt = function
  | Snode l ->
      Format.fprintf fmt "Snode@[<hov 2>[";
      List.iter (fun (x,p,s) ->
	Format.printf "@[(%a,@ %a,@ %a)@];@ "
	  Pretty.print_vs x Pretty.print_pat p print_scheme s)
	l;
      Format.fprintf fmt "@]]"
    | Sleaf s ->
      if Svs.cardinal s = 0 then
	Format.fprintf fmt "Sleaf .. "
      else
	( Format.fprintf fmt "Sleaf ";
	  Svs.iter (fun x -> Format.printf "%a " Pretty.print_vs x) s )



let t_collect_data km qvs t =

  let defn_collect_data acc ls tl =

    let arg_collect_data i defn = function
      | Tvar x when Svs.mem x qvs ->
        let lmap =
          try
            Mvs.find x acc
          with Not_found ->
            Mls.empty
        in Mvs.add x (Mls.add ls (i,defn) lmap) acc
      | _ -> acc
    in

    match (find_logic_definition km ls) with
      | Some defn ->
        begin match ls_defn_decrease defn with
          | [i] -> arg_collect_data i defn (List.nth tl i).t_node
          | _  -> acc
        end
      | None -> acc
  in

  let rec t_collect acc t =
    let acc = match t.t_node with
      | Tapp (ls, tl) -> defn_collect_data acc ls tl
      | _ -> acc
    in t_fold t_collect acc t

  in t_collect (Mvs.empty) t
*)



(*

type ind_info =
    {tact : string ;
     cands : Term.Svs.t;
     ind_v : Term.vsymbol;
     ind_ty : ty;
     itsk : Term.term;
     pred : Term.term;
     sg : Term.term;
     }

let show_info i =
   Format.printf "\nInduction tactic: %s  @." i.tact;
   Format.printf "Initial task: %a @.Candidates: " Pretty.print_term i.itsk;
   Svs.iter (fun x -> Format.printf "%a @." Pretty.print_vs x) i.cands;
   Format.printf "Induction on variable:   %a @." Pretty.print_vsty i.ind_v;
   Format.printf "Induction on type:   %a @." Pretty.print_ty i.ind_ty;
   Format.printf "Induction predicate:   %a @." Pretty.print_term i.pred;
   Format.printf "Induction sub-task: %a \n@." Pretty.print_term i.sg

let print_ty_skm skm =
  List.iter
    (fun (p,svs) ->
      Format.printf "@[ %a : @]" Pretty.print_pat p;
      Svs.iter (Format.printf "%a " Pretty.print_vs) svs;
      Format.printf "@.")
    skm




let indv_ty x = match x.vs_ty.ty_node with
  | Tyapp (ts, _) -> ts, ty_app ts (List.map ty_var ts.ts_args)
  | Tyvar _ -> assert false

let heuristic vss =
  let x = Svs.choose vss in
  let ts, ty = indv_ty x in
  x, ts, ty

let name_from_type ty =
  let s = match ty.ty_node with
    | Tyapp (ts, _) -> ts.ts_name.id_string
    | Tyvar tv -> tv.tv_name.id_string
  in
  if s = "" then "x" else String.make 1 s.[0]




let make_induction vs km qvl t =
  let x, ts, ty  = heuristic vs in

  let sigma = ty_match Mtv.empty ty x.vs_ty in
  let qvl1, qvl2 = split_quantifiers x qvl in
  let p = t_forall_close qvl2 [] t in
  let make_case (ls, _) =
    let create_var ty =
      let ty = ty_inst sigma ty in
      let id = Ident.id_fresh (name_from_type ty) in
      Term.create_vsymbol id ty
    in
    let ind_vl = List.map create_var ls.ls_args in
    let ind_tl = List.map t_var ind_vl in
    let goal = t_subst_single x (t_app ls ind_tl (Some x.vs_ty)) p in
    let goal = List.fold_left
      (fun goal vs ->
	if ty_equal vs.vs_ty x.vs_ty
	then Term.t_implies (t_subst_single x (t_var vs) p) goal
	else goal) goal ind_vl
    in
    let goal = t_forall_close (qvl1 @ ind_vl) [] goal in
     if Debug.test_flag debug then
       begin
	 let data = {
	   tact = ""; cands = vs; ind_v = x;
	   ind_ty = ty;
	   itsk = t_forall_close qvl [] t ;
	   pred = p; sg = goal}
	 in  show_info data
       end; goal
  in
  let cl = find_constructors km ts in
  List.map make_case cl


let induction km t0 =
  let qvs, _qvl, t = decompose_forall t0 in
  let vs = t_candidates km qvs t in
  if Svs.is_empty vs then [t0] else
    let x, _ts, _ty  = heuristic vs in
    let () = print_ty_skm (tyscheme_genvt km x t) in
    [t0]
    (* make_induction vs km qvl t  *)

let induction = function
  | Some { task_decl = { td_node = Decl { d_node = Dprop (Pgoal, pr, f) } };
	   task_prev = prev;
	   task_known = km } ->
      List.map (add_prop_decl prev Pgoal pr) (induction km f)
  | _ -> assert false

let () = Trans.register_transform_l "induction" (Trans.store induction)
*)

  (*Format.printf "[";
    List.iter (fun i ->
      Format.printf "[%d : %a]" i Pretty.print_term (List.nth tl i)) il;
    Format.printf "]@.";*)

(*********************************************************)
(******* Induction tactic on function definition *********)
(*********************************************************)



(*
module Vsl = struct
  type t = Svs.elt list
  let compare t1 t2 =
    let rec aux t1 t2 = match t1,t2 with
      | [],[] -> 0
      | h1 :: q1, h2 :: q2 ->
	if vs_equal h1 h2 
	then aux q1 q2 
	else Pervasives.compare (vs_hash h1) (vs_hash h2)
      | _ -> assert false;
    in
    if List.length t1 < List.length t2 then -1
    else if List.length t1 > List.length t2 then 1
    else aux t1 t2
end

module Svsl = Set.Make(Vsl) *)





(*
module VsList =
struct
 
  type t = Svs.elt list
  let hash = Hashcons.combine_list vs_hash 3
  let equal = list_all2 vs_equal
  let cmp_vs vs1 vs2 = Pervasives.compare (vs_hash vs1) (vs_hash vs2)
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

module Mvls = Util.StructMake(VsList)
*)




(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3.byte"
End:
*)
