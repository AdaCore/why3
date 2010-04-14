
open Names
open Nameops
open Term
open Termops
open Tacmach
open Util
open Coqlib
open Hipattern
open Typing

open Why
open Call_provers

let debug = 
  try let _ = Sys.getenv "WHYDEBUG" in true
  with Not_found -> false

let loadpath = 
  try Str.split (Str.regexp ":") (Sys.getenv "WHYLOADPATH")
  with Not_found -> ["theories"]

let env = Env.create_env (Typing.retrieve loadpath)
    
let timeout = 
  try int_of_string (Sys.getenv "WHYTIMEOUT")
  with Not_found -> 2

let drv =
  let filename = 
    try Sys.getenv "WHYDRIVER" with Not_found -> "drivers/alt_ergo.drv"
  in
  Driver.load_driver filename env

(* Coq constants *)
let logic_dir = ["Coq";"Logic";"Decidable"]

let coq_modules =
  init_modules @ [logic_dir] @ arith_modules @ zarith_base_modules
    @ [["Coq"; "ZArith"; "BinInt"];
       ["Coq"; "Reals"; "Rdefinitions"];
       ["Coq"; "Reals"; "Raxioms";];
       ["Coq"; "Reals"; "Rbasic_fun";];
       ["Coq"; "Reals"; "R_sqrt";];
       ["Coq"; "Reals"; "Rfunctions";]]
    @ [["Coq"; "omega"; "OmegaLemmas"]]

let constant = gen_constant_in_modules "dp" coq_modules

let coq_Z = lazy (constant "Z")
let coq_Zplus = lazy (constant "Zplus")
let coq_Zmult = lazy (constant "Zmult")
let coq_Zopp = lazy (constant "Zopp")
let coq_Zminus = lazy (constant "Zminus")
let coq_Zdiv = lazy (constant "Zdiv")
let coq_Zs = lazy (constant "Zs")
let coq_Zgt = lazy (constant "Zgt")
let coq_Zle = lazy (constant "Zle")
let coq_Zge = lazy (constant "Zge")
let coq_Zlt = lazy (constant "Zlt")
let coq_Z0 = lazy (constant "Z0")
let coq_Zpos = lazy (constant "Zpos")
let coq_Zneg = lazy (constant "Zneg")
let coq_xH = lazy (constant "xH")
let coq_xI = lazy (constant "xI")
let coq_xO = lazy (constant "xO")

let coq_R = lazy (constant "R")
let coq_R0 = lazy (constant "R0")
let coq_R1 = lazy (constant "R1")
let coq_Rgt = lazy (constant "Rgt")
let coq_Rle = lazy (constant "Rle")
let coq_Rge = lazy (constant "Rge")
let coq_Rlt = lazy (constant "Rlt")
let coq_Rplus = lazy (constant "Rplus")
let coq_Rmult = lazy (constant "Rmult")
let coq_Ropp = lazy (constant "Ropp")
let coq_Rinv = lazy (constant "Rinv")
let coq_Rminus = lazy (constant "Rminus")
let coq_Rdiv = lazy (constant "Rdiv")
let coq_powerRZ = lazy (constant "powerRZ")

let coq_iff = lazy (constant "iff")

let is_constant t c = try t = Lazy.force c with _ -> false

(* not first-order expressions *)
exception NotFO

(* the task under construction *)
let task = ref None 

let why_constant path t s =
  let th = Env.find_theory env path t in
  task := Task.use_export !task th;
  Theory.ns_find_ls th.Theory.th_export s

(* coq_rename_vars env [(x1,t1);...;(xn,tn)] renames the xi outside of
   env names, and returns the new variables together with the new
   environment *)
let coq_rename_vars env vars =
  let avoid = ref (ids_of_named_context (Environ.named_context env)) in
  List.fold_right
    (fun (na,t) (newvars, newenv) ->
       let id = next_name_away na !avoid in
       avoid := id :: !avoid;
       id :: newvars, Environ.push_named (id, None, t) newenv)
    vars ([],env)

(* Arithmetic constants *)

exception NotArithConstant

(* translates a closed Coq term p:positive into a FOL term of type int *)

let big_two = Big_int.succ_big_int Big_int.unit_big_int

let rec tr_positive p = match kind_of_term p with
  | Construct _ when p = Lazy.force coq_xH ->
      Big_int.unit_big_int
  | App (f, [|a|]) when f = Lazy.force coq_xI ->
(*
      Plus (Mult (Cst 2, tr_positive a), Cst 1)
*)
      Big_int.succ_big_int (Big_int.mult_big_int big_two (tr_positive a))
  | App (f, [|a|]) when f = Lazy.force coq_xO ->
(*
      Mult (Cst 2, tr_positive a)
*)
      Big_int.mult_big_int big_two (tr_positive a)
  | Cast (p, _, _) ->
      tr_positive p
  | _ ->
      raise NotArithConstant

let const_of_big_int b = Term.t_int_const (Big_int.string_of_big_int b)
  
(* translates a closed Coq term t:Z or R into a FOL term of type int or real *)
let rec tr_arith_constant t = match kind_of_term t with
  | Construct _ when t = Lazy.force coq_Z0 ->
      Term.t_int_const "0"
  | App (f, [|a|]) when f = Lazy.force coq_Zpos ->
      const_of_big_int (tr_positive a)
  | App (f, [|a|]) when f = Lazy.force coq_Zneg ->
      const_of_big_int (Big_int.minus_big_int (tr_positive a))
  | Const _ when t = Lazy.force coq_R0 ->
      Term.t_real_const (Term.RConstDecimal ("0", "0", None))
  | Const _ when t = Lazy.force coq_R1 ->
      Term.t_real_const (Term.RConstDecimal ("1", "0", None))
(*   | App (f, [|a;b|]) when f = Lazy.force coq_Rplus -> *)
(*       let ta = tr_arith_constant a in *)
(*       let tb = tr_arith_constant b in *)
(*       begin match ta,tb with *)
(*         | RCst na, RCst nb -> RCst (Big_int.add_big_int na nb) *)
(*         | _ -> raise NotArithConstant *)
(*       end *)
(*   | App (f, [|a;b|]) when f = Lazy.force coq_Rmult -> *)
(*       let ta = tr_arith_constant a in *)
(*       let tb = tr_arith_constant b in *)
(*       begin match ta,tb with *)
(*         | RCst na, RCst nb -> RCst (Big_int.mult_big_int na nb) *)
(*         | _ -> raise NotArithConstant *)
(*       end *)
(*   | App (f, [|a;b|]) when f = Lazy.force coq_powerRZ -> *)
(*       tr_powerRZ a b *)
  | Cast (t, _, _) ->
      tr_arith_constant t
  | _ ->
      raise NotArithConstant

let rec tr_type tv env t =
  let t = Reductionops.nf_betadeltaiota env Evd.empty t in
  if t = Lazy.force coq_Z then
    Ty.ty_int
  else if t = Lazy.force coq_R then
    Ty.ty_real
  else match kind_of_term t with
    | Var x when Idmap.mem x tv ->
	Ty.ty_var (Idmap.find x tv)
    | _ ->
	assert false (*TODO*)
	(* let f, cl = decompose_app t in *)
(* 	begin try *)
(* 	  let r = global_of_constr f in *)
(* 	  match tr_global env r with *)
(* 	    | DeclType (id, k) -> *)
(* 		assert (k = List.length cl); (\* since t:Set *\) *)
(* 		Tid (id, List.map (tr_type tv env) cl) *)
(* 	    | _ -> *)
(* 		raise NotFO *)
(* 	with *)
(* 	  | Not_found -> *)
(* 	      raise NotFO *)
(* 	  | NotFO -> *)
(* 	      (\* we need to abstract some part of (f cl) *\) *)
(* 	      (\*TODO*\) *)
(* 	      raise NotFO *)
(* 	end *)

(* assumption: t:T:Set *)
and tr_term tv bv env t =
  try
    tr_arith_constant t
  with NotArithConstant -> match kind_of_term t with
    (* binary operations on integers *)
    | App (c, [|a;b|]) when is_constant c coq_Zplus ->
	let ls = why_constant ["int"] "Int" ["infix +"] in
	Term.t_app ls [tr_term tv bv env a; tr_term tv bv env b] Ty.ty_int
    | App (c, [|a;b|]) when is_constant c coq_Zminus ->
	let ls = why_constant ["int"] "Int" ["infix -"] in
	Term.t_app ls [tr_term tv bv env a; tr_term tv bv env b] Ty.ty_int
    | App (c, [|a;b|]) when is_constant c coq_Zmult ->
	let ls = why_constant ["int"] "Int" ["infix *"] in
	Term.t_app ls [tr_term tv bv env a; tr_term tv bv env b] Ty.ty_int
    | App (c, [|a;b|]) when is_constant c coq_Zdiv ->
	let ls = why_constant ["int"] "EuclideanDivision" ["div"] in
	Term.t_app ls [tr_term tv bv env a; tr_term tv bv env b] Ty.ty_int
    | App (c, [|a|]) when is_constant c coq_Zopp ->
	let ls = why_constant ["int"] "Int" ["prefix -"] in
	Term.t_app ls [tr_term tv bv env a] Ty.ty_int
    (* binary operations on reals *)
    | App (c, [|a;b|]) when is_constant c coq_Rplus ->
	let ls = why_constant ["real"] "Real" ["infix +"] in
	Term.t_app ls [tr_term tv bv env a; tr_term tv bv env b] Ty.ty_real
    | App (c, [|a;b|]) when is_constant c coq_Rminus ->
	let ls = why_constant ["real"] "Real" ["infix -"] in
	Term.t_app ls [tr_term tv bv env a; tr_term tv bv env b] Ty.ty_real
    | App (c, [|a;b|]) when is_constant c coq_Rmult ->
	let ls = why_constant ["real"] "Real" ["infix *"] in
	Term.t_app ls [tr_term tv bv env a; tr_term tv bv env b] Ty.ty_real
    | App (c, [|a;b|]) when is_constant c coq_Rdiv ->
	let ls = why_constant ["real"] "Real" ["infix /"] in
	Term.t_app ls [tr_term tv bv env a; tr_term tv bv env b] Ty.ty_real
    | App (c, [|a|]) when is_constant c coq_Ropp ->
	let ls = why_constant ["real"] "Real" ["prefix -"] in
	Term.t_app ls [tr_term tv bv env a] Ty.ty_real
    | App (c, [|a|]) when is_constant c coq_Rinv ->
	let ls = why_constant ["real"] "Real" ["inv"] in
	Term.t_app ls [tr_term tv bv env a] Ty.ty_real
    (* first-order terms *)
    | Var id when Idmap.mem id bv ->
	Term.t_var (Idmap.find id bv)
    | _ ->
	assert false (*TODO*)
(* 	let f, cl = decompose_app t in *)
(* 	begin try *)
(* 	  let r = global_of_constr f in *)
(* 	  match tr_global env r with *)
(* 	    | DeclFun (s, k, _, _) -> *)
(* 		let cl = skip_k_args k cl in *)
(* 		Fol.App (s, List.map (tr_term tv bv env) cl) *)
(* 	    | _ -> *)
(* 		raise NotFO *)
(* 	with *)
(* 	  | Not_found -> *)
(* 	      raise NotFO *)
(* 	  | NotFO -> (\* we need to abstract some part of (f cl) *\) *)
(* 	      let rec abstract app = function *)
(* 		| [] -> *)
(* 		    Fol.App (make_term_abstraction tv env app, []) *)
(* 		| x :: l as args -> *)
(* 		    begin try *)
(* 		      let s = make_term_abstraction tv env app in *)
(* 		      Fol.App (s, List.map (tr_term tv bv env) args) *)
(* 		    with NotFO -> *)
(* 		      abstract (applist (app, [x])) l *)
(* 		    end *)
(* 	      in *)
(* 	      let app,l = match cl with *)
(* 		| x :: l -> applist (f, [x]), l | [] -> raise NotFO *)
(* 	      in *)
(* 	      abstract app l *)
(* 	end *)

and quantifiers n a b tv bv env =
  let vars, env = coq_rename_vars env [n,a] in
  let id = match vars with [x] -> x | _ -> assert false in
  let b = subst1 (mkVar id) b in
  let t = tr_type tv env a in
  let vs = Term.create_vsymbol (Ident.id_fresh (string_of_id id)) t in
  let bv = Idmap.add id vs bv in
  vs, t, bv, env, b

and tr_formula tv bv env f =
  let c, args = decompose_app f in
  match kind_of_term c, args with
(*
    | Var id, [] ->
	Fatom (Pred (rename_global (VarRef id), []))
*)
    | _, [t;a;b] when c = build_coq_eq () ->
	let ty = type_of env Evd.empty t in
	if is_Set ty || is_Type ty then
	  let _ = tr_type tv env t in
	  Term.f_equ (tr_term tv bv env a) (tr_term tv bv env b)
	else
	  raise NotFO
    (* comparisons on integers *)
    | _, [a;b] when is_constant c coq_Zle ->
	let ls = why_constant ["int"] "Int" ["infix <="] in
	Term.f_app ls [tr_term tv bv env a; tr_term tv bv env b]
    | _, [a;b] when is_constant c coq_Zlt ->
	let ls = why_constant ["int"] "Int" ["infix <"] in
	Term.f_app ls [tr_term tv bv env a; tr_term tv bv env b]
    | _, [a;b] when is_constant c coq_Zge ->
	let ls = why_constant ["int"] "Int" ["infix >="] in
	Term.f_app ls [tr_term tv bv env a; tr_term tv bv env b]
    | _, [a;b] when is_constant c coq_Zgt ->
	let ls = why_constant ["int"] "Int" ["infix >"] in
	Term.f_app ls [tr_term tv bv env a; tr_term tv bv env b]
    (* comparisons on reals *)
    | _, [a;b] when is_constant c coq_Rle ->
	let ls = why_constant ["real"] "Real" ["infix <="] in
	Term.f_app ls [tr_term tv bv env a; tr_term tv bv env b]
    | _, [a;b] when is_constant c coq_Rlt ->
	let ls = why_constant ["real"] "Real" ["infix <"] in
	Term.f_app ls [tr_term tv bv env a; tr_term tv bv env b]
    | _, [a;b] when is_constant c coq_Rge ->
	let ls = why_constant ["real"] "Real" ["infix >="] in
	Term.f_app ls [tr_term tv bv env a; tr_term tv bv env b]
    | _, [a;b] when is_constant c coq_Rgt ->
	let ls = why_constant ["real"] "Real" ["infix >"] in
	Term.f_app ls [tr_term tv bv env a; tr_term tv bv env b]
    (* propositional logic *)
    | _, [] when c = build_coq_False () ->
	Term.f_false
    | _, [] when c = build_coq_True () ->
	Term.f_true
    | _, [a] when c = build_coq_not () ->
	Term.f_not (tr_formula tv bv env a)
    | _, [a;b] when c = build_coq_and () ->
	Term.f_and (tr_formula tv bv env a) (tr_formula tv bv env b)
    | _, [a;b] when c = build_coq_or () ->
	Term.f_or (tr_formula tv bv env a) (tr_formula tv bv env b)
    | _, [a;b] when c = Lazy.force coq_iff ->
	Term.f_iff (tr_formula tv bv env a) (tr_formula tv bv env b)
    | Prod (n, a, b), _ ->
	if is_imp_term f && is_Prop (type_of env Evd.empty a) then
	  Term.f_implies (tr_formula tv bv env a) (tr_formula tv bv env b)
	else
	  let vs, t, bv, env, b = quantifiers n a b tv bv env in
	  Term.f_forall [vs] [] (tr_formula tv bv env b)
    | _, [_; a] when c = build_coq_ex () ->
	begin match kind_of_term a with
	  | Lambda(n, a, b) ->
	      let vs, t, bv, env, b = quantifiers n a b tv bv env in
	      Term.f_exists [vs] [] (tr_formula tv bv env b)
	  | _ ->
	      (* unusual case of the shape (ex p) *)
	      raise NotFO (* TODO: we could eta-expanse *)
	end
(*
    | _ ->
	begin try
	  let r = global_of_constr c in
	  match tr_global env r with
	    | DeclPred (s, k, _) ->
		let args = skip_k_args k args in
		Fatom (Pred (s, List.map (tr_term tv bv env) args))
	    | _ ->
		raise NotFO
	with Not_found ->
	  raise NotFO
	end
*)
    | _ -> assert false (*TODO*)

let tr_goal gl =
  let f = tr_formula Idmap.empty Idmap.empty (pf_env gl) (pf_concl gl) in
  let pr = Decl.create_prsymbol (Ident.id_fresh "goal") in
  if debug then Format.printf "---@\n%a@\n---@." Pretty.print_fmla f;
  task := Task.add_prop_decl !task Decl.Pgoal pr f

let whytac gl =
  let concl_type = pf_type_of gl (pf_concl gl) in
  if not (is_Prop concl_type) then error "Conclusion is not a Prop";
  task := Task.use_export None Theory.builtin_theory;
  try
    tr_goal gl;
    if debug then Format.printf "@[%a@]@\n---@." (Driver.print_task drv) !task;
    let res = Driver.call_prover ~debug ~timeout drv !task in
    match res.pr_answer with
      | Valid -> Tactics.admit_as_an_axiom gl
      | Invalid -> error "Invalid"
      | Unknown s -> error ("Don't know: " ^ s)
      | Failure s -> error ("Failure: " ^ s)
      | Timeout -> error "Timeout"
      | HighFailure -> 
	  error ("Prover failure\n" ^ res.pr_stdout ^ "\n" ^ res.pr_stderr)
  with NotFO ->
    error "Not a first order goal"


let _ =
  Tacinterp.overwriting_add_tactic "Why" (fun _ -> whytac);
  Egrammar.extend_tactic_grammar "Why" [[Egrammar.TacTerm "why"]]


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. coq-plugin-opt-yes"
End:
*)
