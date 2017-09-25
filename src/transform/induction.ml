(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
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




let lab_ind = create_label "induction"

(*
let desc_labels = [label_induction,
                   ("Make the induction on the labeled variables." :
                       Pp.formatted)]
*)

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
module VsList = Stdlib.OrderedHashedList(struct
  type t = vsymbol
  let tag = vs_hash
end)
module Mvsl = Extmap.Make(VsList)
module Svsl = Extset.MakeOfMap(Mvsl)

(* DEBUGGING AND PRINTING *)

let debug = Debug.register_info_flag "induction"
  ~desc:"Print@ debugging@ messages@ of@ the@ 'induction'@ transformation."

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

(* dead code
let split_quantifiers x qvl =
  let rec aux left = function
    | hd :: tl when vs_equal x hd -> List.rev left, tl
    | hd :: tl -> aux (hd :: left) tl
    | [] -> assert false
  in aux [] qvl
*)

(*INITIAL FORMULA SPLIT*)
let decompose_forall t =
  let rec aux qvl_acc t = match t.t_node with
    | Tquant (Tforall, qt) ->
      let qvl, _, t = t_open_quant qt in aux (qvl_acc @ qvl) t
    | _ -> qvl_acc, t
  in
  let qvl, t = aux [] t in (List.fold_right Svs.add qvl Svs.empty), qvl, t





let qvl_labeled qvl =
  List.filter (fun v -> Slab.mem lab_ind v.vs_name.id_label) qvl

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
  let vl = heuristic_lex vset in
  let lexl, rightmost_qvl = qsplit km vl qvl in
  let tcase = make_induction_lex lexl rightmost_qvl t in
  if Debug.test_flag debug then
    begin
      print_vset vset;
      print_heuristic_lex vl;
      print_lex lexl;
      Format.printf "Old Task: %a \n@." Pretty.print_term t0;
      Format.printf "New Task: %a \n@." Pretty.print_term tcase
    end;
  [tcase]

let induction_ty_lex task =
  match task with
  | Some { task_decl = { td_node = Decl { d_node = Dprop (Pgoal, pr, f) } };
	   task_prev = prev;
	   task_known = km } ->
     begin try
       let l = induction_ty_lex km f in
       List.map (add_prop_decl prev Pgoal pr) l
       with No_candidates_found ->
         Format.eprintf "induction_ty_lex: no candidate variable found in goal %a@."
                        Pretty.print_pr pr;
         [task]
     end
  | _ -> assert false


let () =
  Trans.register_transform_l "induction_ty_lex" (Trans.store induction_ty_lex)
    ~desc:"Generate@ induction@ hypotheses@ for@ goals@ over@ algebraic@ types."


(***************************************************************************)
(********************** INDUCTION TACTIC FOR INTEGERS **********************)
(***************************   WITH LEX. ORDER   ***************************)
(***************************************************************************)

(* induction_int_lex :   induction tactic for ordered int tuples.
No heuristic is provided. Use labels. Generalized variables inside
the induction hypothesis are the variables on the right of the rightmost
induction variable.*)

(* separate prenex universal quantification from the body of the formula*)
(* dead code
let decompose_int_forall t =
  let rec aux qvl_acc t = match t.t_node with
    | Tquant (Tforall, qt) ->
      let qvl, _, t = t_open_quant qt in aux (qvl_acc @ qvl) t
    | _ -> qvl_acc, t
  in aux [] t
*)

(* find labeled variables (for induction variables),
and the rest of the quantified variables after the last labeled variable
(for the variables to generalize inside induction hypothesis).
Ex: the result of Va.x1.b.x2.c.x3.d.P is [a.x1.b.x2.c.x3][x1.x2.x3][d]*)
(* dead code
let split_int_qlv_labeled qvl =
  let rec aux left_acc ind_acc gen_acc = function
    | [] -> List.rev left_acc, List.rev ind_acc, gen_acc
    | v :: tl ->
      let lbls =
	Slab.filter (fun v -> v.lab_string = "induction") v.vs_name.id_label
      in if not (Slab.is_empty lbls)
	then aux (v :: (gen_acc @ left_acc)) (v :: ind_acc) [] tl
	else aux left_acc ind_acc (v :: gen_acc) tl
  in aux [] [] [] qvl
*)

(*
input: ordered induction variables, rightmost neutral variables
output:
  new variables for rightmost neutral variables (generalization),
  new variabkes for induction hypothesis and
  the complete condition for induction variable non-negativeness and
  lexicographic order.
For instance, if input: ivl = (x1,x2); rvl = (d,e)
then output:
 (d',e') ~ 'generalization variables',
 (x1',x2',x3') ~ 'induction variables'
 (0 <= x1'/\0 <= x2'/\(x1' < x1 \/ x1' = x1 /\ x2' < x2) ~ 'hyp. condition' *)
(* dead code
let lex_order_ivl (le_int,lt_int) ivl rvl  =
  let gen_rvl, (hd,hd',tl,tl') =
    let create_v v = Term.create_vsymbol (Ident.id_clone v.vs_name) ty_int in
    match (ivl, List.map create_v ivl) with
      | v :: tl, v':: tl' -> ((List.map create_v rvl), (v, v', tl, tl'))
      | _ -> assert false in
  let nonneg_ivl' =
    let positive v = ps_app le_int [t_nat_const 0; t_var v] in
    List.fold_left (fun t v -> t_and t (positive v)) (positive hd') tl' in
  let lt_lex =
    let lt_hd = ps_app lt_int [t_var hd'; t_var hd] in
    let eq_on_left (x, x', left, left') =
      let teq = t_equ (t_var x) (t_var x') in
      List.fold_left2
	(fun t x x' -> t_and t (t_equ (t_var x) (t_var x'))) teq left left' in
    let rec lex_ord (hd, hd', left, left')  acc_or = function
      | [],[] -> acc_or
      | v :: tl, v' :: tl'  ->
	let v_eql = eq_on_left (hd, hd', left, left') in
	let v_lt = ps_app lt_int [t_var v'; t_var v] in
	lex_ord
	  (v, v', hd :: left, hd' :: left')
	  (t_or acc_or (t_and v_eql v_lt)) (tl,tl')
      | _ -> assert false
    in lex_ord (hd, hd', [],[]) lt_hd (tl, tl') in
  gen_rvl, (hd' :: tl'), t_and nonneg_ivl' lt_lex
*)

(*returns the resulting formula with induction hypothesis.
The formula however is still not closed (by the quantifiers before
the rightmost neutral quantifiers). *)
(* dead code
let int_strong_induction_lex (le_int,lt_int) ivl rvl t =
  let (gen_rvl, ind_ivl, hyp_cond) =
    lex_order_ivl (le_int,lt_int) ivl rvl in
  let hyp_goal =
    List.fold_left2
      (fun t x x' ->
	t_subst_single x (t_var x') t) t (ivl @ rvl) (ind_ivl @ gen_rvl) in
  let ind_hyp =
    t_forall_close (ind_ivl @ gen_rvl) [] (t_implies hyp_cond hyp_goal) in
  let open_t = t_implies ind_hyp (t_forall_close rvl [] t) in open_t
*)

(* dead code
let induction_int_lex _km (le_int,lt_int) t0 =
  let qvl, t = decompose_int_forall t0 in
  let lvl,ivl, genl =  split_int_qlv_labeled qvl in
  if (ivl = [])
  then [t0]
  else
    begin
      let t = int_strong_induction_lex (le_int,lt_int) ivl genl t in
      let t = t_forall_close lvl [] t in
      if Debug.test_flag debug then
	(Format.printf "Old Task: %a \n@." Pretty.print_term t0;
	 Format.printf "New Task: %a \n@." Pretty.print_term t);
      [t]
    end
*)

(* dead code
let induction_int_lex th_int = function
  | Some
      { task_decl = { td_node = Decl { d_node = Dprop (Pgoal, pr, f) } };
	task_prev = prev; task_known = km } as t ->
    begin
      try
	let le_int = ns_find_ls th_int.th_export ["infix <="] in
	let lt_int = ns_find_ls th_int.th_export ["infix <"] in
	if not (Mid.mem le_int.ls_name km) then raise Exit;
	List.map (add_prop_decl prev Pgoal pr)
	  (induction_int_lex km (le_int, lt_int) f)
      with Exit -> [t] end
  | _ -> assert false
*)

(*
let () =
  Trans.register_env_transform_l "induction_int_lex"
    (fun env ->
      let th_int = Env.find_theory env ["int"] "Int" in
      Trans.store (induction_int_lex th_int))
    ~desc:"Generate@ induction@ hypotheses@ for@ goals@ over@ integers."
*)

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3.byte"
End:
*)
