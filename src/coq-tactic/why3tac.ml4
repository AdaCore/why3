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

open Names
open Namegen
open Term
open Termops
open Tacmach
open Util
open Coqlib
open Hipattern
open Declarations
open Pp
open Universes
open Globnames
open Vars

IFDEF COQ85 THEN
open Errors
ELSE
open CErrors
open Stdarg
END

IFDEF COQ87 THEN

module KVars = Vars
open EConstr
open EConstr.Vars
module Vars = KVars
open Ltac_plugin

END

let declare_summary name freeze unfreeze init =
  Summary.declare_summary name
    { Summary.freeze_function = (fun _ -> freeze ());
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init; }

let body_of_constant env c =
  if Reductionops.is_transparent env (ConstKey c) then
    let cb = Environ.lookup_constant c env in
    match cb.const_body with
    | Def _ -> Declareops.body_of_constant Opaqueproof.empty_opaquetab cb
    | _ -> None
  else None

let type_of = Typing.type_of

let finite_ind v = v <> Decl_kinds.CoFinite

let pr_str = Pp.str

let pr_spc = Pp.spc

let pr_fnl = Pp.fnl

let force x = x

let coq_reference t1 t2 =
  let th = lazy (coq_reference t1 t2) in
  fun x -> lazy (Lazy.force th x)

let find_reference t1 t2 =
  let th = lazy (find_reference t1 t2) in
  fun x -> lazy (Lazy.force th x)

IFDEF COQ85 THEN

let push_named = Environ.push_named
let betadeltaiota = Closure.betadeltaiota

module RedFlags = Closure.RedFlags

ELSE

let push_named (id, c, t) env =
  Environ.push_named
    (match c with
     | None -> Context.Named.Declaration.LocalAssum (id, t)
     | Some b -> Context.Named.Declaration.LocalDef (id, b, t))
    env

let pf_hyps gl =
  List.map (function
    | Context.Named.Declaration.LocalAssum (id, t) -> (id, None, t)
    | Context.Named.Declaration.LocalDef (id, b, t) -> (id, Some b, t))
    (pf_hyps gl)

let betadeltaiota = CClosure.all

module RedFlags = CClosure.RedFlags

END

DECLARE PLUGIN "why3tac"

IFDEF COQ87 THEN

let global_of_constr evd t = global_of_constr (to_constr evd t)
let type_of_global env c = of_constr (fst (Global.type_of_global_in_context env c))

ELSE

let kind _evd t = kind_of_term t
let is_global _evd c t = is_global c t
let is_Prop _evd t = is_Prop t
let is_Set _evd t = is_Set t
let is_Type _evd t = is_Type t
let to_constr _evd t = t
let of_constr t = t
let dependent _evd c t = dependent c t
let global_of_constr _evd t = global_of_constr t
let type_of_global _env c = Global.type_of_global_unsafe c
let is_imp_term _evd t = is_imp_term t
let decompose_app _evd t = decompose_app t

END

let is_global evd c t = is_global evd (Lazy.force c) t

module Why3tac = struct

open Why3
open Call_provers
open Whyconf
open Ty
open Term

let debug =
  try let _ = Sys.getenv "WHY3DEBUG" in true
  with Not_found -> false

let config =
  try
    Whyconf.read_config None
  with Whyconf.ConfigFailure(file, msg) ->
    error (file ^ ": " ^ msg)

let main = Whyconf.get_main config

let timelimit = timelimit main

let env = Env.create_env (loadpath main)

let provers = Hashtbl.create 17

let get_prover s =
  try
    Hashtbl.find provers s
  with Not_found ->
    let filter_prover = Whyconf.parse_filter_prover s in
    let cp = try Whyconf.filter_one_prover config filter_prover
      with Whyconf.ProverAmbiguity (wc,fp,provers) ->
        let provers = Mprover.filter (fun _ p -> not p.interactive) provers in
        if Mprover.is_num_elt 1 provers then
          snd (Mprover.choose provers)
        else if Mprover.is_empty provers then
          raise (Whyconf.ProverNotFound (wc,fp))
        else
          raise (Whyconf.ProverAmbiguity (wc,fp,provers))
    in
    let drv = Whyconf.load_driver main env cp.driver cp.extra_drivers in
    Hashtbl.add provers s (cp, drv);
    cp, drv

(* Coq constants *)

let coq_ref_BinInt = coq_reference "Why3" ["ZArith"; "BinInt"; "Z"]
let coq_Zplus = coq_ref_BinInt "add"
let coq_Zmult = coq_ref_BinInt "mul"
let coq_Zopp = coq_ref_BinInt "opp"
let coq_Zminus = coq_ref_BinInt "sub"
let coq_Zdiv = coq_ref_BinInt "div"
let coq_Zgt = coq_ref_BinInt "gt"
let coq_Zle = coq_ref_BinInt "le"
let coq_Zge = coq_ref_BinInt "ge"
let coq_Zlt = coq_ref_BinInt "lt"
let coq_ref_BinNums = coq_reference "Why3" ["Numbers"; "BinNums"]
let coq_Z = coq_ref_BinNums "Z"
let coq_Z0 = coq_ref_BinNums "Z0"
let coq_Zpos = coq_ref_BinNums "Zpos"
let coq_Zneg = coq_ref_BinNums "Zneg"
let coq_xH = coq_ref_BinNums "xH"
let coq_xI = coq_ref_BinNums "xI"
let coq_xO = coq_ref_BinNums "xO"

let coq_ref_Rdefinitions = coq_reference "Why3" ["Reals"; "Rdefinitions"]
let coq_R = coq_ref_Rdefinitions "R"
let coq_R0 = coq_ref_Rdefinitions "R0"
let coq_R1 = coq_ref_Rdefinitions "R1"
let coq_Rgt = coq_ref_Rdefinitions "Rgt"
let coq_Rle = coq_ref_Rdefinitions "Rle"
let coq_Rge = coq_ref_Rdefinitions "Rge"
let coq_Rlt = coq_ref_Rdefinitions "Rlt"
let coq_Rplus = coq_ref_Rdefinitions "Rplus"
let coq_Rmult = coq_ref_Rdefinitions "Rmult"
let coq_Ropp = coq_ref_Rdefinitions "Ropp"
let coq_Rinv = coq_ref_Rdefinitions "Rinv"
let coq_Rminus = coq_ref_Rdefinitions "Rminus"
let coq_Rdiv = coq_ref_Rdefinitions "Rdiv"
let coq_powerRZ = coq_reference "Why3" ["Reals"; "Rfunctions"] "powerRZ"
IFDEF COQ87 THEN
let coq_IZR = coq_ref_Rdefinitions "IZR"
ELSE
let coq_IZR = coq_reference "Why3" ["Reals"; "Raxioms"] "IZR"
END

let coq_Logic = coq_reference "Why3" ["Init"; "Logic"]
let coq_False = coq_Logic "False"
let coq_True = coq_Logic "True"
let coq_eq = coq_Logic "eq"
let coq_not = coq_Logic "not"
let coq_and = coq_Logic "and"
let coq_or = coq_Logic "or"
let coq_ex = coq_Logic "ex"
let coq_iff = coq_Logic "iff"

let coq_WhyType =
  find_reference "Why3" ["Why3"; "BuiltIn"] "WhyType"

let rec is_WhyType evd c = match kind evd c with
  | App (f, [|_|]) -> is_global evd coq_WhyType f
  | Cast (c, _, _) -> is_WhyType evd c
  | _ -> false

let has_WhyType env evd c = is_WhyType evd (snd (type_of env evd c))

(* not first-order expressions *)
exception NotFO

(* coq_rename_vars env [(x1,t1);...;(xn,tn)] renames the xi outside of
   env names, and returns the new variables together with the new
   environment *)
(*
let coq_rename_vars env vars =
  let avoid = ref (ids_of_named_context (Environ.named_context env)) in
  List.fold_right
    (fun (na,t) (newvars, newenv) ->
       let id = next_name_away na !avoid in
       avoid := id :: !avoid;
       id :: newvars, Environ.push_named (id, None, t) newenv)
    vars ([],env)
*)

let coq_rename_var env evd na t =
  let avoid = ids_of_named_context (Environ.named_context env) in
  let id = next_name_away na avoid in
  id, push_named (id, None, (to_constr evd t)) env

let preid_of_id id = Ident.id_fresh (string_of_id id)

(* rec_names_for c [|n1;...;nk|] builds the list of constant names for
   identifiers n1...nk with the same path as c, if they exist; otherwise
   raises NotFO *)
let rec_names_for c =
  let mp,dp,_ = Names.repr_con c in
  CArray.map_to_list
    (function
       | Name id ->
           let c' = Names.make_con mp dp (label_of_id id) in
           ignore
             (try Global.lookup_constant c' with Not_found -> raise NotFO);
           c'
       | Anonymous ->
           raise NotFO)

(* extract the prenex type quantifications i.e.
   type_quantifiers env (A1:Set)...(Ak:Set)t = A1...An, (env+Ai), t *)
let decomp_type_quantifiers env evd t =
  let add m id =
    let tv = Ty.create_tvsymbol (preid_of_id id) in
    Idmap.add id (Some (Ty.ty_var tv)) m, tv
  in
  let rec loop env tvm vars t = match kind evd t with
    | Prod (n, a, t) when is_Set evd a || is_Type evd a ->
        let n, env = coq_rename_var env evd n a in
        let t = subst1 (mkVar n) t in
        let tvm, tv = add tvm n in
        loop env tvm (tv :: vars) t
    | Prod (n, a, t) when is_WhyType evd a ->
        let n, env = coq_rename_var env evd n a in
        let t = subst1 (mkVar n) t in
        loop env tvm vars t
    | _ ->
        (tvm, List.rev vars), env, t
  in
  loop env Idmap.empty [] t

(* decomposes the first n type lambda abstractions correspondings to
   the list of type variables vars *)
let decomp_type_lambdas tvm env evd vars t =
  let rec loop tvm env vars t = match vars, kind evd t with
    | vars, Lambda (n, a, t) when is_WhyType evd a ->
        let id, env = coq_rename_var env evd n a in
        let t = subst1 (mkVar id) t in
        loop tvm env vars t
    | tv :: vars, Lambda (n, a, t) when is_Set evd a || is_Type evd a ->
        let id, env = coq_rename_var env evd n a in
        let t = subst1 (mkVar id) t in
        let tvm = Idmap.add id (Some (Ty.ty_var tv)) tvm in
        loop tvm env vars t
    | [], _ ->
        tvm, env, t
    | _ ->
        raise NotFO (*TODO: eta-expansion*)
  in
  loop tvm env vars t

let decompose_arrows evd =
  let rec arrows_rec l c = match kind evd c with
    | Prod (_,t,c) when not (dependent evd (mkRel 1) c) -> arrows_rec (t :: l) c
    | Cast (c,_,_) -> arrows_rec l c
    | _ -> List.rev l, c
  in
  arrows_rec []

let is_fo_kind evd ty =
  let _, ty = decompose_arrows evd ty in
  is_Set evd ty || is_Type evd ty

let decomp_lambdas _dep _tvm bv env evd vars t =
  let rec loop bv vsl env vars t = match vars, kind evd t with
    | [], _ ->
        (bv, List.rev vsl), env, t
    | ty :: vars, Lambda (n, a, t) ->
        let id, env = coq_rename_var env evd n a in
        let t = subst1 (mkVar id) t in
        let vs = create_vsymbol (preid_of_id id) ty in
        let bv = Idmap.add id (Some vs) bv in
        loop bv (vs :: vsl) env vars t
    | _ ->
        raise NotFO (*TODO: eta-expansion*)
  in
  loop bv [] env vars t

let rec skip_k_args k cl = match k, cl with
  | [], _ -> cl
  | _ :: k, _ :: cl -> skip_k_args k cl
  | _, [] -> raise NotFO

(* Coq globals *)

(* Coq reference -> symbol *)
let global_ts = ref Refmap.empty
let global_ls = ref Refmap.empty

(* polymorphic arity (i.e. number of type variables) *)
let poly_arity = ref Mls.empty
let add_poly_arity ls n = poly_arity := Mls.add ls n !poly_arity
let get_poly_arity ls = assert (Mls.mem ls !poly_arity); Mls.find ls !poly_arity

(* ident -> decl *)
let global_decl = ref Ident.Mid.empty

type dep = {
  dep_decls   : Decl.Sdecl.t;
  dep_use_int : bool;
  dep_use_eucl: bool;
  dep_use_real: bool;
}

let empty_dep =
  { dep_decls = Decl.Sdecl.empty;
    dep_use_int = false;
    dep_use_eucl = false;
    dep_use_real = false; }

let empty_dep () = ref empty_dep
let add_dep r v = r := { !r with dep_decls = Decl.Sdecl.add v !r.dep_decls }

(* dependencies: decl -> dep *)
let global_dep = ref Decl.Mdecl.empty

let add_new_decl dep dep' decl =
  add_dep dep decl;
  Ident.Sid.iter
    (fun id ->
       global_decl := Ident.Mid.add id decl !global_decl)
    decl.Decl.d_news;
  global_dep := Decl.Mdecl.add decl dep' !global_dep

let print_dep fmt =
  let print1 d { dep_decls = dl } =
    Format.fprintf fmt "@[%a -> @[%a@]@]@\n" Pretty.print_decl d
      (Pp.print_list Pp.newline Pretty.print_decl) (Decl.Sdecl.elements dl)
  in
  Decl.Mdecl.iter print1 !global_dep

(* the task under construction *)
let task = ref None

let th_int = lazy (Env.read_theory env ["int"] "Int")
let th_eucl = lazy (Env.read_theory env ["int"] "EuclideanDivision")
let th_real = lazy (Env.read_theory env ["real"] "Real")

let why_constant_int dep s =
  task := Task.use_export !task (Lazy.force th_int);
  dep := { !dep with dep_use_int = true };
  Theory.ns_find_ls (Lazy.force th_int).Theory.th_export s

let why_constant_eucl dep s =
  task := Task.use_export !task (Lazy.force th_eucl);
  dep := { !dep with dep_use_eucl = true };
  Theory.ns_find_ls (Lazy.force th_eucl).Theory.th_export s

let why_constant_real dep s =
  task := Task.use_export !task (Lazy.force th_real);
  dep := { !dep with dep_use_real = true };
  Theory.ns_find_ls (Lazy.force th_real).Theory.th_export s

let rec add_local_decls d =
  let id = Ident.Sid.choose d.Decl.d_news in
  if not (Ident.Mid.mem id (Task.task_known !task)) then begin
    assert (Decl.Mdecl.mem d !global_dep);
    let dep = Decl.Mdecl.find d !global_dep in
    Decl.Sdecl.iter add_local_decls dep.dep_decls;
    if dep.dep_use_int then task := Task.use_export !task (Lazy.force th_int);
    if dep.dep_use_eucl then task := Task.use_export !task (Lazy.force th_eucl);
    if dep.dep_use_real then task := Task.use_export !task (Lazy.force th_real);
    try
      task := Task.add_decl !task d
    with Decl.UnknownIdent id ->
      Format.eprintf "unknown ident %s@." id.Ident.id_string;
      Format.eprintf "  @[%a@]@.@." Pretty.print_decl d;
      Format.eprintf "task=@[%a@]@." Pretty.print_task !task;
      assert false
  end

(* synchronization *)
let () =
  declare_summary "Why globals"
    (fun () ->
     !global_ts, !global_ls, !poly_arity, !global_decl, !global_dep)
    (fun (ts,ls,pa,gdecl,gdep) ->
     global_ts := ts; global_ls := ls; poly_arity := pa;
     global_decl := gdecl; global_dep := gdep)
    (fun () ->
     global_ts := Refmap.empty;
     global_ls := Refmap.empty;
     poly_arity := Mls.empty;
     global_decl := Ident.Mid.empty;
     global_dep := Decl.Mdecl.empty)

let lookup_table table r = match Refmap.find r !table with
  | None -> raise NotFO
  | Some d -> d

let add_table table r v = table := Refmap.add r v !table

(* Arithmetic constants *)

exception NotArithConstant

(* translates a closed Coq term p:positive into a FOL term of type int *)

let big_two = Big_int.succ_big_int Big_int.unit_big_int

let rec tr_positive evd p = match kind evd p with
  | Construct _ when is_global evd coq_xH p ->
      Big_int.unit_big_int
  | App (f, [|a|]) when is_global evd coq_xI f ->
      (* Plus (Mult (Cst 2, tr_positive a), Cst 1) *)
      Big_int.succ_big_int (Big_int.mult_big_int big_two (tr_positive evd a))
  | App (f, [|a|]) when is_global evd coq_xO f ->
      (* Mult (Cst 2, tr_positive a) *)
      Big_int.mult_big_int big_two (tr_positive evd a)
  | Cast (p, _, _) ->
      tr_positive evd p
  | _ ->
      raise NotArithConstant

let const_of_big_int b =
  Term.t_const
    (Number.ConstInt (Number.int_const_dec (Big_int.string_of_big_int b)))
    ty_int

let const_of_big_int_real b =
  let s = Big_int.string_of_big_int b in
  Term.t_const (Number.ConstReal (Number.real_const_dec s "0" None)) ty_real

(* translates a closed Coq term t:Z or R into a FOL term of type int or real *)
let rec tr_arith_constant_IZR evd dep t = match kind evd t with
  | Construct _ when is_global evd coq_Z0 t ->
    Term.t_const (Number.ConstReal (Number.real_const_dec "0" "0" None)) ty_real
  | App (f, [|a|]) when is_global evd coq_Zpos f ->
    const_of_big_int_real (tr_positive evd a)
  | App (f, [|a|]) when is_global evd coq_Zneg f ->
    let t = const_of_big_int_real (tr_positive evd a) in
    let fs = why_constant_real dep ["prefix -"] in
    Term.fs_app fs [t] ty_real
  | Cast (t, _, _) ->
    tr_arith_constant_IZR evd dep t
  | _ ->
    raise NotArithConstant

let rec tr_arith_constant evd dep t = match kind evd t with
  | Construct _ when is_global evd coq_Z0 t -> Term.t_nat_const 0
  | App (f, [|a|]) when is_global evd coq_Zpos f ->
      const_of_big_int (tr_positive evd a)
  | App (f, [|a|]) when is_global evd coq_Zneg f ->
      let t = const_of_big_int (tr_positive evd a) in
      let fs = why_constant_int dep ["prefix -"] in
      Term.fs_app fs [t] Ty.ty_int
  | App (f, [|a|]) when is_global evd coq_IZR f ->
      tr_arith_constant_IZR evd dep a
  | Const _ when is_global evd coq_R0 t ->
      Term.t_const (Number.ConstReal (Number.real_const_dec "0" "0" None))
        ty_real
  | Const _ when is_global evd coq_R1 t ->
      Term.t_const (Number.ConstReal (Number.real_const_dec "1" "0" None))
        ty_real
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
      tr_arith_constant evd dep t
  | _ ->
      raise NotArithConstant

let rec tr_type dep tvm env evd t =
  let t = Reductionops.clos_norm_flags
      (RedFlags.red_add_transparent
	 betadeltaiota (Conv_oracle.get_transp_state (Environ.oracle env)))
      env evd t in
  if is_global evd coq_Z t then
    Ty.ty_int
  else if is_global evd coq_R t then
    Ty.ty_real
  else match kind evd t with
    | Var x when Idmap.mem x tvm ->
        begin match Idmap.find x tvm with
          | None -> raise NotFO
          | Some ty -> ty
        end
    | _ ->
        let f, cl = decompose_app evd t in
        begin try
          let r = global_of_constr evd f in
          let ts = tr_task_ts dep env evd r in
          let cl = List.filter (fun c -> not (has_WhyType env evd c)) cl in
          assert (List.length ts.Ty.ts_args = List.length cl);
          (* since t:Set *)
          Ty.ty_app ts (List.map (tr_type dep tvm env evd) cl)
        with
          | Not_found ->
              raise NotFO
          | NotFO ->
              (* TODO: we need to abstract some part of (f cl) *)
              raise NotFO
        end

(* the type symbol for r *)
and tr_task_ts dep env evd r =
  let ts = tr_global_ts dep env evd r in
  if Ident.Mid.mem ts.ts_name !global_decl then begin
    let d = Ident.Mid.find ts.ts_name !global_decl in
    add_local_decls d
  end;
  ts

(* the type declaration for r *)
and tr_global_ts dep env evd (r : global_reference) =
  try
    let ts = lookup_table global_ts r in
    begin try
      let d = Ident.Mid.find ts.ts_name !global_decl in add_dep dep d
    with Not_found -> () end;
    ts
  with Not_found ->
    add_table global_ts r None;
    let dep' = empty_dep () in
    match r with
      | VarRef id ->
          let ty = try type_of_global env r with Not_found -> raise NotFO in
          let (_,vars), _, t = decomp_type_quantifiers env evd ty in
          if not (is_Set evd t) && not (is_Type evd t) then raise NotFO;
          let id = preid_of_id id in
          let ts = Ty.create_tysymbol id vars NoDef in
          let decl = Decl.create_ty_decl ts in
          add_table global_ts r (Some ts);
          add_new_decl dep !dep' decl;
          ts
      | ConstructRef _ ->
          assert false
      | ConstRef c ->
          let ty = type_of_global env r in
          let (_,vars), _, t = decomp_type_quantifiers env evd ty in
          if not (is_Set evd t) && not (is_Type evd t) then raise NotFO;
          let id = preid_of_id (Nametab.basename_of_global r) in
          let ts = match body_of_constant env c with
            | Some b ->
                let b = force b in
                let tvm, env, t = decomp_type_lambdas Idmap.empty env evd vars (of_constr b) in
                let def = Alias (tr_type dep' tvm env evd t) in
                Ty.create_tysymbol id vars def
                  (* FIXME: is it correct to use None when NotFO? *)
            | None ->
                Ty.create_tysymbol id vars NoDef
          in
          let decl = Decl.create_ty_decl ts in
          add_table global_ts r (Some ts);
          add_new_decl dep !dep' decl;
          ts
      | IndRef i ->
          let mib, _ = Global.lookup_inductive i in
          (* first, the inductive types *)
          let make_one_ts j _ = (* j-th inductive *)
            let r = IndRef (ith_mutual_inductive i j) in
            let ty = type_of_global env r in
            let (_,vars), _, t = decomp_type_quantifiers env evd ty in
            if not (is_Set evd t) && not (is_Type evd t) then raise NotFO;
            let id = preid_of_id (Nametab.basename_of_global r) in
            let ts = Ty.create_tysymbol id vars NoDef in
            add_table global_ts r (Some ts)
          in
          Array.iteri make_one_ts mib.mind_packets;
          (* second, the declarations with constructors *)
          let make_one j oib = (* j-th inductive *)
            let j = ith_mutual_inductive i j in
            let ts = lookup_table global_ts (IndRef j) in
            let tyj = Ty.ty_app ts (List.map Ty.ty_var ts.Ty.ts_args) in
            let opaque = Ty.Stv.of_list ts.Ty.ts_args in
            let constr = Array.length oib.mind_nf_lc in
            let mk_constructor k _tyk = (* k-th constructor *)
              let r = ConstructRef (j, k+1) in
              let ty = type_of_global env r in
              let (_,vars), env, t = decomp_type_quantifiers env evd ty in
              let l, c = decompose_arrows evd t in
              let tvm = match kind evd c with
                | App (_, v) ->
                    let v = Array.to_list v in
                    let no_whytype c = not (has_WhyType env evd c) in
                    let v = List.filter no_whytype v in
                    let add v1 v2 tvm = match kind evd v1 with
                      | Var x1 ->
                          if Idmap.mem x1 tvm then raise NotFO;
                          let v2 = Some (Ty.ty_var v2) in
                          Idmap.add x1 v2 tvm
                      | _ -> raise NotFO (* GADT *)
                    in
                    List.fold_right2 add v ts.Ty.ts_args Idmap.empty
                | Ind _ -> Idmap.empty
                | Prod _ -> Idmap.empty
                (* ensured by Coq typing *)
                | CoFix _ -> assert false
                | Fix _ -> assert false
                | Case (_, _, _, _) -> assert false
                | Construct _ -> assert false
                | Const _ -> assert false
                | LetIn (_, _, _, _) -> assert false
                | Lambda (_, _, _) -> assert false
                | Cast (_, _, _) -> assert false
                | Sort _ -> assert false
                | Evar _ -> assert false
                | Meta _ -> assert false
                | Var _ -> assert false
                | Rel _ -> assert false
                | _ (* Proj *) -> assert false
              in
              let l = List.map (tr_type dep' tvm env evd) l in
              let id = preid_of_id (Nametab.basename_of_global r) in
              let ls = Term.create_fsymbol ~opaque ~constr id l tyj in
              add_table global_ls r (Some ls);
              add_poly_arity ls vars;
              ls, List.map (fun _ -> None) ls.ls_args
            in
            let cl =
              try Array.to_list (Array.mapi mk_constructor oib.mind_nf_lc)
              with NotFO -> []
            in
            (j, oib), (ts, cl)
          in
          let dl = Array.mapi make_one mib.mind_packets in
          let dl = Array.to_list dl in
          let add ((j, oib), (ts, cl as d)) (tl, dl, sl) =
            if cl = [] then begin
              let sl = ref sl in
              for k = 0 to Array.length oib.mind_nf_lc - 1 do
                let r = ConstructRef (j, k+1) in
                try
                  make_one_ls dep' env evd r;
                  let ls = lookup_table global_ls r in
                  let d = Decl.create_param_decl ls in
                  sl := d :: !sl
                with NotFO ->
                  ()
              done;
              Decl.create_ty_decl ts :: tl, dl, !sl
            end else
              tl, d :: dl, sl
          in
          let tl, dl, sl = List.fold_right add dl ([], [], []) in
          let decl =
            if dl = [] then None else Some (Decl.create_data_decl dl)
          in
          (* Format.printf "decl = %a@." Pretty.print_decl decl; *)
          List.iter (add_new_decl dep !dep') tl;
          List.iter (add_dep dep') tl;
          Opt.iter (add_new_decl dep !dep') decl;
          Opt.iter (add_dep dep') decl;
          List.iter (add_new_decl dep !dep') sl;
          lookup_table global_ts r

(* the function/predicate symbol for r *)
and tr_task_ls dep env evd r =
  let ls = tr_global_ls dep env evd r in
  if Ident.Mid.mem ls.ls_name !global_decl then begin
    let d = Ident.Mid.find ls.ls_name !global_decl in
    add_local_decls d
  end;
  ls

(* the function/predicate symbol declaration for r *)
and tr_global_ls dep env evd r =
  try
    let ls = lookup_table global_ls r in
    begin try
      let d = Ident.Mid.find ls.ls_name !global_decl in add_dep dep d
    with Not_found -> () end;
    ls
  with Not_found ->
    add_table global_ls r None;
    let dep' = empty_dep () in
    (* type_of_global may fail on a local, higher-order variable *)
    let ty = try type_of_global env r with Not_found -> raise NotFO in
    let (tvm, _), env, t = decomp_type_quantifiers env evd ty in
    if is_Set evd t || is_Type evd t then raise NotFO;
    let _, t = decompose_arrows evd t in
    match r with
      | ConstructRef _ ->
          assert (not (is_Prop evd t)); (* is a proof *)
          let evd,s = type_of env evd t in
          if not (is_Set evd s || is_Type evd s) then raise NotFO;
          ignore (tr_type dep' tvm env evd t);
          lookup_table global_ls r
      | ConstRef c ->
          let pl, d = decompose_definition dep' env evd c in
          List.iter (add_new_decl dep !dep') pl;
          List.iter (add_dep dep') pl;
          Opt.iter (add_new_decl dep !dep') d;
          lookup_table global_ls r
      | IndRef i ->
          assert (is_Prop evd t);
          let pl, d = decompose_inductive dep' env evd i in
          List.iter (add_new_decl dep !dep') pl;
          List.iter (add_dep dep') pl;
          Opt.iter (add_new_decl dep !dep') d;
          lookup_table global_ls r
      | VarRef _ ->
          make_one_ls dep' env evd r;
          let ls = lookup_table global_ls r in
          let decl = Decl.create_param_decl ls in
          add_new_decl dep !dep' decl;
          ls

and make_one_ls dep env evd r =
  let ty = type_of_global env r in
  let (tvm, vars), env, t = decomp_type_quantifiers env evd ty in
  if is_Set evd t || is_Type evd t then raise NotFO;
  let l, t = decompose_arrows evd t in
  let args = List.map (tr_type dep tvm env evd) l in
  let ls =
    let id = preid_of_id (Nametab.basename_of_global r) in
    if is_Prop evd t then
        (* predicate definition *)
      create_lsymbol id args None
    else
      let evd,s = type_of env evd t in
      if is_Set evd s || is_Type evd s then
          (* function definition *)
        let ty = tr_type dep tvm env evd t in
        create_lsymbol id args (Some ty)
      else
        raise NotFO
  in
  add_table global_ls r (Some ls);
  add_poly_arity ls vars

and decompose_definition dep env evd c =
  let dl = match body_of_constant env c with
    | None ->
        [ConstRef c, None]
    | Some b ->
        let b = force b in
        let rec decomp vars t = match Constr.kind t with
          | Lambda (n, a, t) ->
              decomp ((n, a) :: vars) t
          | Fix (_, (names, _, bodies)) ->
              let lc = rec_names_for c names in
              let l = List.rev_map Constr.mkConst lc in
              let n = List.length vars in
              let db_vars = Array.init n (fun i -> Constr.mkRel (n - i)) in
              let l = List.map (fun t -> appvect (t, db_vars)) l in
              let bodies = Array.to_list bodies in
              let bodies = List.map (Vars.substl l) bodies in
              let add_lambdas b =
                List.fold_left (fun t (n,a) -> Constr.mkLambda (n,a,t)) b vars
              in
              let bodies = List.map add_lambdas bodies in
              List.fold_right2
                (fun c b acc -> (ConstRef c, Some b) :: acc) lc bodies []
          | _ ->
              [ConstRef c, Some b]
        in
        decomp [] b
  in
  List.iter (fun (r, _) -> make_one_ls dep env evd r) dl;
  let make_one_decl (r, b) =
    let ls = lookup_table global_ls r in
    match b with
      | None ->
          assert false
      | Some b ->
          let tvs = List.fold_left Ty.ty_freevars Stv.empty
            (Ty.oty_cons ls.ls_args ls.ls_value) in
          let add tv tvm = Stdlib.Mstr.add tv.tv_name.Ident.id_string tv tvm in
          let tvm = Stv.fold add tvs Stdlib.Mstr.empty in
          let ty = type_of_global env r in
          let (_, vars), env, _ = decomp_type_quantifiers env evd ty in
          let conv tv = Stdlib.Mstr.find tv.tv_name.Ident.id_string tvm in
          let vars = List.map conv vars in
          let tvm, env, b = decomp_type_lambdas Idmap.empty env evd vars (of_constr b) in
          let (bv, vsl), env, b =
            decomp_lambdas dep tvm Idmap.empty env evd ls.ls_args b
          in
          begin match ls.ls_value with
            | None ->
                let b = tr_formula dep tvm bv env evd b in
                Decl.make_ls_defn ls vsl b
            | Some _ ->
                let b = tr_term dep tvm bv env evd b in
                Decl.make_ls_defn ls vsl b
          end
  in
  match dl with
    | [r, None] ->
        [Decl.create_param_decl (lookup_table global_ls r)], None
    | _ ->
        let add (r, _ as d) (pl, dl) =
          try
            pl, make_one_decl d :: dl
          with NotFO ->
            Decl.create_param_decl (lookup_table global_ls r) :: pl, dl
        in
        let pl, dl = List.fold_right add dl ([], []) in
        pl, if dl = [] then None else Some (Decl.create_logic_decl dl)

and decompose_inductive dep env evd i =
  let mib, _ = Global.lookup_inductive i in
  (* first, the inductive types *)
  let make_one_ls j _ = (* j-th inductive *)
    make_one_ls dep env evd (IndRef (ith_mutual_inductive i j))
  in
  Array.iteri make_one_ls mib.mind_packets;
  (* second, the inductive predicate declarations *)
  let make_one j oib = (* j-th inductive *)
    let j = ith_mutual_inductive i j in
    let ls = lookup_table global_ls (IndRef j) in
    let mk_constructor k _tyk = (* k-th constructor *)
      let r = ConstructRef (j, k+1) in
      let ty = type_of_global env r in
      let (_,vars), env, f = decomp_type_quantifiers env evd ty in
      let tvm =
        let add v1 v2 tvm =
          let v2 = Some (Ty.ty_var v2) in
          Idmap.add (id_of_string v1.tv_name.Ident.id_string) v2 tvm
        in
        List.fold_right2 add vars (get_poly_arity ls) Idmap.empty
      in
      let f = tr_formula dep tvm Idmap.empty env evd f in
      let id = preid_of_id (Nametab.basename_of_global r) in
      let pr = Decl.create_prsymbol id in
      pr, f
    in
    let cl =
      try Array.to_list (Array.mapi mk_constructor oib.mind_nf_lc)
      with NotFO -> []
    in
    ls, cl
  in
  let dl = Array.mapi make_one mib.mind_packets in
  let dl = Array.to_list dl in
  let add (ls, cl as d) (pl, dl) =
    if cl = [] then Decl.create_param_decl ls :: pl, dl else pl, d :: dl
  in
  let pl, dl = List.fold_right add dl ([], []) in
  let s = if finite_ind mib.mind_finite then Decl.Ind else Decl.Coind in
  pl, if dl = [] then None else Some (Decl.create_ind_decl s dl)

(* translation of a Coq term
   assumption: t:T:Set *)
and tr_term dep tvm bv env evd t =
  try
    tr_arith_constant evd dep t
  with NotArithConstant -> match kind evd t with
    (* binary operations on integers *)
    | App (c, [|a;b|]) when is_global evd coq_Zplus c ->
        let ls = why_constant_int dep ["infix +"] in
        Term.fs_app ls [tr_term dep tvm bv env evd a; tr_term dep tvm bv env evd b]
          Ty.ty_int
    | App (c, [|a;b|]) when is_global evd coq_Zminus c ->
        let ls = why_constant_int dep ["infix -"] in
        Term.fs_app ls [tr_term dep tvm bv env evd a; tr_term dep tvm bv env evd b]
          Ty.ty_int
    | App (c, [|a;b|]) when is_global evd coq_Zmult c ->
        let ls = why_constant_int dep ["infix *"] in
        Term.fs_app ls [tr_term dep tvm bv env evd a; tr_term dep tvm bv env evd b]
          Ty.ty_int
    | App (c, [|a;b|]) when is_global evd coq_Zdiv c ->
        let ls = why_constant_eucl dep ["div"] in
        Term.fs_app ls [tr_term dep tvm bv env evd a; tr_term dep tvm bv env evd b]
          Ty.ty_int
    | App (c, [|a|]) when is_global evd coq_Zopp c ->
        let ls = why_constant_int dep ["prefix -"] in
        Term.fs_app ls [tr_term dep tvm bv env evd a] Ty.ty_int
    (* binary operations on reals *)
    | App (c, [|a;b|]) when is_global evd coq_Rplus c ->
        let ls = why_constant_real dep ["infix +"] in
        Term.fs_app ls [tr_term dep tvm bv env evd a; tr_term dep tvm bv env evd b]
          Ty.ty_real
    | App (c, [|a;b|]) when is_global evd coq_Rminus c ->
        let ls = why_constant_real dep ["infix -"] in
        Term.fs_app ls [tr_term dep tvm bv env evd a; tr_term dep tvm bv env evd b]
          Ty.ty_real
    | App (c, [|a;b|]) when is_global evd coq_Rmult c ->
        let ls = why_constant_real dep ["infix *"] in
        Term.fs_app ls [tr_term dep tvm bv env evd a; tr_term dep tvm bv env evd b]
          Ty.ty_real
    | App (c, [|a;b|]) when is_global evd coq_Rdiv c ->
        let ls = why_constant_real dep ["infix /"] in
        Term.fs_app ls [tr_term dep tvm bv env evd a; tr_term dep tvm bv env evd b]
          Ty.ty_real
    | App (c, [|a|]) when is_global evd coq_Ropp c ->
        let ls = why_constant_real dep ["prefix -"] in
        Term.fs_app ls [tr_term dep tvm bv env evd a] Ty.ty_real
    | App (c, [|a|]) when is_global evd coq_Rinv c ->
        let ls = why_constant_real dep ["inv"] in
        Term.fs_app ls [tr_term dep tvm bv env evd a] Ty.ty_real
          (* first-order terms *)
    | Var id when Idmap.mem id bv ->
        let vs = match Idmap.find id bv with
          | None -> raise NotFO
          | Some vs -> vs
        in
        Term.t_var vs
    | Case (ci, _, e, br) ->
        let evd,ty = type_of env evd e in
        let ty = tr_type dep tvm env evd ty in
        let e = tr_term dep tvm bv env evd e in
        let branch j bj =
          let evd,tj = type_of env evd bj in
          let (_,tvars), _, tj = decomp_type_quantifiers env evd tj in
          let tyl, _ = decompose_arrows evd tj in
          let tyl = List.map (tr_type dep tvm env evd) tyl in
          let tvm, env, bj = decomp_type_lambdas tvm env evd tvars bj in
          let (bv, vars), env, bj = decomp_lambdas dep tvm bv env evd tyl bj in
          let cj = ith_constructor_of_inductive ci.ci_ind (j+1) in
          let ls = tr_global_ls dep env evd (ConstructRef cj) in
          if List.length vars <> List.length ls.ls_args then raise NotFO;
          let pat = pat_app ls (List.map pat_var vars) ty in
          t_close_branch pat (tr_term dep tvm bv env evd bj)
        in
        let evd,ty = type_of env evd t in
        let _ty = tr_type dep tvm env evd ty in
        t_case e (Array.to_list (Array.mapi branch br))
    | LetIn (x, e1, ty1, e2) ->
        if is_Prop evd ty1 || is_fo_kind evd ty1 then
          let e2 = subst1 e1 e2 in
          tr_term dep tvm bv env evd e2
        else begin
          let evd,s1 = type_of env evd ty1 in
          if not (is_Set evd s1 || is_Type evd s1) then raise NotFO;
          let t1 = tr_term dep tvm bv env evd e1 in
          let vs, _, bv, env, e2 = quantifiers x ty1 e2 dep tvm bv env evd in
          let t2 = tr_term dep tvm bv env evd e2 in
          t_let_close vs t1 t2
        end
    | CoFix _ | Fix _ | Lambda _ | Prod _ | Sort _ | Evar _ | Meta _ ->
        raise NotFO
    | Rel _ ->
        assert false
    | Cast (t, _, _) ->
        tr_term dep tvm bv env evd t
    | Var _ | App _ | Construct _ | Ind _ | Const _ ->
        let f, cl = decompose_app evd t in
        (* a local variable cannot be applied (not FO) *)
        begin match kind evd f with
          | Var id when Idmap.mem id bv -> raise NotFO
          | _ -> ()
        end;
        let r = try global_of_constr evd f with _ -> raise NotFO in
        let ls = tr_task_ls dep env evd r in
        begin match ls.Term.ls_value with
          | Some _ ->
              let cl = List.filter (fun c -> not (has_WhyType env evd c)) cl in
              let k = get_poly_arity ls in
              let cl = skip_k_args k cl in
              let evd,ty = type_of env evd t in
              let ty = tr_type dep tvm env evd ty in
              Term.fs_app ls (List.map (tr_term dep tvm bv env evd) cl) ty
          | None  ->
              raise NotFO
        end
        (* TODO: we could abstract some part of (f cl) when not FO *)
(*               let rec abstract app = function *)
(*                   | [] -> *)
(*                       Fol.App (make_term_abstraction tv env app, []) *)
(*                   | x :: l as args -> *)
(*                       begin try *)
(*                         let s = make_term_abstraction tv env app in *)
(*                         Fol.App (s, List.map (tr_term dep tvm bv env) args) *)
(*                       with NotFO -> *)
(*                         abstract (applist (app, [x])) l *)
(*                       end *)
(*               in *)
(*               let app,l = match cl with *)
(*                   | x :: l -> applist (f, [x]), l | [] -> raise NotFO *)
(*               in *)
(*               abstract app l *)
  | _ (* Proj *) ->
      raise NotFO

and quantifiers n a b dep tvm bv env evd =
  let id, env = coq_rename_var env evd n a in
  let b = subst1 (mkVar id) b in
  let t = tr_type dep tvm env evd a in
  let vs = Term.create_vsymbol (preid_of_id id) t in
  let bv = Idmap.add id (Some vs) bv in
  vs, t, bv, env, b

(* translation of a Coq formula
   assumption f:Prop *)
and tr_formula dep tvm bv env evd f = match kind evd f with
  | App(c, [|t;a;b|]) when is_global evd coq_eq c ->
      let evd,ty = type_of env evd t in
      if not (is_Set evd ty || is_Type evd ty) then raise NotFO;
      let _ = tr_type dep tvm env evd t in
      Term.t_equ (tr_term dep tvm bv env evd a) (tr_term dep tvm bv env evd b)
  (* comparisons on integers *)
  | App(c, [|a;b|]) when is_global evd coq_Zle c ->
      let ls = why_constant_int dep ["infix <="] in
      Term.ps_app ls [tr_term dep tvm bv env evd a; tr_term dep tvm bv env evd b]
  | App(c, [|a;b|]) when is_global evd coq_Zlt c ->
      let ls = why_constant_int dep ["infix <"] in
      Term.ps_app ls [tr_term dep tvm bv env evd a; tr_term dep tvm bv env evd b]
  | App(c, [|a;b|]) when is_global evd coq_Zge c ->
      let ls = why_constant_int dep ["infix >="] in
      Term.ps_app ls [tr_term dep tvm bv env evd a; tr_term dep tvm bv env evd b]
  | App(c, [|a;b|]) when is_global evd coq_Zgt c ->
      let ls = why_constant_int dep ["infix >"] in
      Term.ps_app ls [tr_term dep tvm bv env evd a; tr_term dep tvm bv env evd b]
  (* comparisons on reals *)
  | App(c, [|a;b|]) when is_global evd coq_Rle c ->
      let ls = why_constant_real dep ["infix <="] in
      Term.ps_app ls [tr_term dep tvm bv env evd a; tr_term dep tvm bv env evd b]
  | App(c, [|a;b|]) when is_global evd coq_Rlt c ->
      let ls = why_constant_real dep ["infix <"] in
      Term.ps_app ls [tr_term dep tvm bv env evd a; tr_term dep tvm bv env evd b]
  | App(c, [|a;b|]) when is_global evd coq_Rge c ->
      let ls = why_constant_real dep ["infix >="] in
      Term.ps_app ls [tr_term dep tvm bv env evd a; tr_term dep tvm bv env evd b]
  | App(c, [|a;b|]) when is_global evd coq_Rgt c ->
      let ls = why_constant_real dep ["infix >"] in
      Term.ps_app ls [tr_term dep tvm bv env evd a; tr_term dep tvm bv env evd b]
  (* propositional logic *)
  | _ when is_global evd coq_False f ->
      Term.t_false
  | _ when is_global evd coq_True f ->
      Term.t_true
  | App(c, [|a|]) when is_global evd coq_not c ->
      Term.t_not (tr_formula dep tvm bv env evd a)
  | App(c, [|a;b|]) when is_global evd coq_and c ->
      Term.t_and (tr_formula dep tvm bv env evd a) (tr_formula dep tvm bv env evd b)
  | App(c, [|a;b|]) when is_global evd coq_or c ->
      Term.t_or (tr_formula dep tvm bv env evd a) (tr_formula dep tvm bv env evd b)
  | App(c, [|a;b|]) when is_global evd coq_iff c ->
      Term.t_iff (tr_formula dep tvm bv env evd a) (tr_formula dep tvm bv env evd b)
  | Prod (n, a, b) ->
      let evd,ty = type_of env evd a in
      if is_imp_term evd f && is_Prop evd ty then
        Term.t_implies
          (tr_formula dep tvm bv env evd a) (tr_formula dep tvm bv env evd b)
      else
        let vs, _t, bv, env, b = quantifiers n a b dep tvm bv env evd in
        Term.t_forall_close [vs] [] (tr_formula dep tvm bv env evd b)
  | App(c, [|_; a|]) when is_global evd coq_ex c ->
      begin match kind evd a with
        | Lambda(n, a, b) ->
            let vs, _t, bv, env, b = quantifiers n a b dep tvm bv env evd in
            Term.t_exists_close [vs] [] (tr_formula dep tvm bv env evd b)
        | _ ->
              (* unusual case of the shape (ex p) *)
              (* TODO: we could eta-expanse *)
          raise NotFO
      end
  | Case (ci, _, e, br) ->
      let evd,ty = type_of env evd e in
      let ty = tr_type dep tvm env evd ty in
      let t = tr_term dep tvm bv env evd e in
      let branch j bj =
        let evd,tj = type_of env evd bj in
        let (_,tvars), _, tj = decomp_type_quantifiers env evd tj in
        let tyl, _ = decompose_arrows evd tj in
        let tyl = List.map (tr_type dep tvm env evd) tyl in
        let tvm, env, bj = decomp_type_lambdas tvm env evd tvars bj in
        let (bv, vars), env, bj = decomp_lambdas dep tvm bv env evd tyl bj in
        let cj = ith_constructor_of_inductive ci.ci_ind (j+1) in
        let ls = tr_global_ls dep env evd (ConstructRef cj) in
        if List.length vars <> List.length ls.ls_args then raise NotFO;
        let pat = pat_app ls (List.map pat_var vars) ty in
        t_close_branch pat (tr_formula dep tvm bv env evd bj)
      in
      t_case t (Array.to_list (Array.mapi branch br))
  | Var _ ->
      raise NotFO (* no propositional variables *)
  | CoFix _ | Fix _ | Lambda _ | Sort _ | Evar _ | Meta _ ->
      raise NotFO
  | LetIn (x, e1, ty1, e2) ->
      if is_Prop evd ty1 || is_Set evd ty1 || is_Type evd ty1 then
        let e2 = subst1 e1 e2 in
        tr_formula dep tvm bv env evd e2
      else begin
        let evd,s1 = type_of env evd ty1 in
        if not (is_Set evd s1 || is_Type evd s1) then raise NotFO;
        let t1 = tr_term dep tvm bv env evd e1 in
        let vs, _, bv, env, e2 = quantifiers x ty1 e2 dep tvm bv env evd in
        let f2 = tr_formula dep tvm bv env evd e2 in
        t_let_close vs t1 f2
      end
  | Rel _ ->
      assert false (* quantified variables should be named at this point *)
  | Cast (c, _, _) ->
      tr_formula dep tvm bv env evd c
  | Construct _ | Ind _ | Const _ | App _ ->
      let c, args = decompose_app evd f in
      let r = try global_of_constr evd c with _ -> raise NotFO in
      let ls = tr_task_ls dep env evd r in
      begin match ls.Term.ls_value with
        | None ->
            let args = List.filter (fun c -> not (has_WhyType env evd c)) args in
            let k = get_poly_arity ls in
            let args = skip_k_args k args in
            Term.ps_app ls (List.map (tr_term dep tvm bv env evd) args)
        | Some _ ->
          raise NotFO
      end
  | _ (* Proj *) ->
      raise NotFO

let is_global_var id =
  try ignore (Environ.lookup_named id (Global.env ())); true
  with Not_found -> false

let tr_goal gl evd =
  let env = pf_env gl in
  let dep = empty_dep () in
  let rec tr_ctxt tvm bv = function
    | [] ->
        tr_formula dep tvm bv env evd (pf_concl gl)
    | (id, _, _) :: ctxt when is_global_var id ->
        tr_ctxt tvm bv ctxt
    | (id, None, ty) :: ctxt when is_Set evd ty || is_Type evd ty ->
        let v = Ty.create_tvsymbol (preid_of_id id) in
        let tvm = Idmap.add id (Some (Ty.ty_var v)) tvm in
        tr_ctxt tvm bv ctxt
    | (id, None, ty) :: ctxt when is_fo_kind evd ty ->
        let tvm = Idmap.add id None tvm in
        tr_ctxt tvm bv ctxt
    | (id, None, ty) :: ctxt when is_WhyType evd ty ->
        let bv = Idmap.add id None bv in
        tr_ctxt tvm bv ctxt
    | (id, None, ty) :: ctxt ->
        let evd,t = type_of env evd ty in
        begin try
          if is_Set evd t || is_Type evd t then
            let ty = tr_type dep tvm env evd ty in (* DO NOT INLINE! *)
            let vs = Term.create_vsymbol (preid_of_id id) ty in
            let bv = Idmap.add id (Some vs) bv in
            Term.t_forall_close [vs] [] (tr_ctxt tvm bv ctxt)
          else if is_Prop evd t then
            let h = tr_formula dep tvm bv env evd ty in (* DO NOT INLINE! *)
            Term.t_implies h (tr_ctxt tvm bv ctxt)
          else
            raise NotFO
        with NotFO ->
          let bv = Idmap.add id None bv in
          tr_ctxt tvm bv ctxt
        end
    | (id, Some d, ty) :: ctxt ->
        (* local definition -> let or skip *)
        let evd,t = type_of env evd ty in
        begin try
          if not (is_Set evd t || is_Type evd t) then raise NotFO;
          let d = tr_term dep tvm bv env evd d in
          let ty = tr_type dep tvm env evd ty in
          let vs = Term.create_vsymbol (preid_of_id id) ty in
          let bv = Idmap.add id (Some vs) bv in
          Term.t_let_close vs d (tr_ctxt tvm bv ctxt)
        with NotFO ->
          let bv = Idmap.add id None bv in
          tr_ctxt tvm bv ctxt
        end
  in
  let f = tr_ctxt Idmap.empty Idmap.empty (List.rev (pf_hyps gl)) in
  let pr = Decl.create_prsymbol (Ident.id_fresh "goal") in
  if debug then Format.printf "---@\n%a@\n---@." Pretty.print_term f;
  task := Task.add_prop_decl !task Decl.Pgoal pr f

let () = Printexc.record_backtrace true

let is_goal s =
  let n = String.length s in
  n >= 11 && String.sub s 0 11 = "Unnamed_thm" ||
  n >= 9 && String.sub s (n - 9) 9 = "_admitted"

let tr_reference env evd r s =
  let dep = empty_dep () in
  let bv = Idmap.empty in
  let id = Ident.id_fresh s in
  let c = constr_of_reference r in
  let evd,ty = type_of env evd (of_constr c) in
  try
    if is_fo_kind evd ty then
      ignore (tr_task_ts (empty_dep ()) env evd r)
    else
      let evd,t = type_of env evd ty in
      if is_Set evd t || is_Type evd t then
        ignore (tr_task_ls (empty_dep ()) env evd r)
      else if is_Prop evd t then
        let (tvm,_), env, f = decomp_type_quantifiers env evd ty in
        let f = tr_formula dep tvm bv env evd f in
        let pr = Decl.create_prsymbol id in
        task := Task.add_prop_decl !task Decl.Paxiom pr f
      else
        raise NotFO
  with NotFO ->
    (* Format.eprintf "  IGNORING top decl %s@." s; *)
    ()

(* decide whether we translate the Coq declaration or not, based on its
   kernel name; if so, returns (Some s) where s will be the Why3 name,
   otherwise returns None

   FIXME: currently, we simply check for the toplevel module "Top"
   and for modules imported from Why3's library of realizations
   (with paths as Why3.X.Y); later we will improve this with vernacular
   commands to select modules and/or constants to be translated/not
   translated *)
let rec is_acceptable_dirpath = function
  | [id] -> let s = string_of_id id in s <> "Coq" (*s = "Top" || s = "Why3"*)
  | [] -> false
  | _ :: p -> is_acceptable_dirpath p

let why3_builtin = [id_of_string "BuiltIn"; id_of_string "Why3"]
let is_acceptable_dirpath dp =
  dp <> why3_builtin && is_acceptable_dirpath dp

let tr_kernel_name kn =
  (* Format.eprintf "  kn = %s@." (string_of_kn kn); *)
  let mp, _, lab = repr_kn kn in
  let s = string_of_label lab in
  match mp with
    | MPfile dp when is_acceptable_dirpath (repr_dirpath dp) ->
        Some s
    | _ ->
        None

let tr_top_constant env evd c = match tr_kernel_name (user_con c) with
  | Some s ->
      (* Format.eprintf "tr_top_constant %s@." (string_of_con c); *)
      tr_reference env evd (ConstRef c) s
  | None -> ()

let tr_top_decls evd =
  let env = Global.env () in
  let prenv = Environ.pre_env env in
  Cmap_env.iter (fun c _ -> tr_top_constant env evd c)
    prenv.Pre_env.env_globals.Pre_env.env_constants

let pr_fp fp =
  pr_str (Pp.string_of_wnl Whyconf.print_filter_prover fp)

let plugins_loaded = ref false

let why3tac ?(timelimit=timelimit) s gl =
  (* print_dep Format.err_formatter; *)
  let evd,concl_type = Tacmach.pf_type_of gl (pf_concl gl) in
  if not (is_Prop evd concl_type) then error "Conclusion is not a Prop";
  task := Task.use_export None Theory.builtin_theory;
  let res = try
    (* OCaml doesn't let us do it at the initialisation time *)
    if not !plugins_loaded then begin
      Whyconf.load_plugins main;
      plugins_loaded := true
    end;
    (* add global declarations from modules Top and Why3.X.Y *)
    tr_top_decls evd;
    (* then translate the goal *)
    tr_goal gl evd;
    let cp, drv = get_prover s in
    let command = String.concat " " (cp.command :: cp.extra_options) in
    if debug then Format.printf "@[%a@]@\n---@." Pretty.print_task !task;
    if debug then Format.printf "@[%a@]@\n---@." (Driver.print_task drv) !task;
    let limit =
    { Call_provers.empty_limit with Call_provers.limit_time = timelimit } in
    let call = Driver.prove_task ~command ~limit drv !task in
    wait_on_call call
  with
    | NotFO ->
        if debug then Printexc.print_backtrace stderr; flush stderr;
        error "Not a first order goal"
    | Whyconf.ProverNotFound (_, fp) ->
        let pl =
          Mprover.fold (fun prover p l -> if not p.interactive
            then ("\"" ^ Whyconf.prover_parseable_format prover ^ "\"") :: l
            else l)
          (get_provers config) [] in
        let msg = pr_str "No such prover `"
          ++ pr_fp fp
          ++ pr_str "'." ++
          pr_spc () ++ pr_str "Available provers are:" ++ pr_fnl () ++
          prlist (fun s -> pr_str s ++ pr_fnl ()) (List.rev pl) in
        errorlabstrm "Whyconf.ProverNotFound" msg
    | Whyconf.ProverAmbiguity (_, fp,provers) ->
        let pl = Mprover.keys provers in
        let pl = List.map (fun prover ->
          "\"" ^ Whyconf.prover_parseable_format prover ^ "\"") pl in
        let msg = pr_str "More than one prover corresponding to `" ++
          pr_fp fp ++ pr_str "'." ++
          pr_spc () ++ pr_str "Corresponding provers are:" ++ pr_fnl () ++
          prlist (fun s -> pr_str s ++ pr_fnl ()) (List.rev pl) in
        errorlabstrm "Whyconf.ProverAmbiguity" msg
    | Whyconf.ParseFilterProver s ->
      let msg = pr_str "Syntax error prover identification '" ++
        pr_str s ++ pr_str "' :  name[,version[,alternative]|,,alternative]" in
      errorlabstrm "Whyconf.ParseFilterProver" msg
(*
    | e ->
        Printexc.print_backtrace stderr; flush stderr;
        Format.eprintf "@[exception: %a@]@." Exn_printer.exn_printer e;
        raise e
*)
  in
  match res.pr_answer with
  | Valid -> Tacticals.tclIDTAC gl
  | Invalid -> error "Invalid"
  | Call_provers.Unknown (s, _) -> error ("Don't know: " ^ s)
  | Call_provers.Failure s -> error ("Failure: " ^ s)
  | Call_provers.Timeout -> error "Timeout"
  | OutOfMemory -> error "Out Of Memory"
  | StepLimitExceeded -> error "Step Limit Exceeded"
  | HighFailure -> error ("Prover failure\n" ^ res.pr_output ^ "\n")

let why3tac ?timelimit s = Proofview.V82.tactic (why3tac ?timelimit s)

end

TACTIC EXTEND Why3
  [ "why3" string(s) ] -> [ Why3tac.why3tac s ]
| [ "why3" string(s) "timelimit" integer(n) ] -> [ Why3tac.why3tac ~timelimit:n s ]
END

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. lib/coq-tactic/why3tac.cmxs"
End:
*)
