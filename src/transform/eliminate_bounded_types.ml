open Ident
open Decl
open Theory
open Task

(* Boolean flag to decide if generated applications of inrange functions
   should be inlined whenever possible *)
let inline_inrange = true

(* Boolean flag to decide if a warning should be generated when a constraint
   is forgotten. *)
let output_warning = true

type bounded_types_env =
    { (* Map from symbols of bounded types to (ty, p)
         where ty is the base type and p (t) should be used to create
         applications of the in_range predicate *)
      bounded : (Ty.ty * (Term.term -> Term.term)) Ty.Mts.t;
      (* Set of conversion functions that should be removed *)
      conv    : Term.Sls.t;
      (* Translation of type symbols *)
      types   : Ty.tysymbol Ty.Mts.t;
      (* Translation of function symbols *)
      funs    : Term.lsymbol Term.Mls.t;
      (* symbol of a bounded type for which we have not yet found the
         definition of the in_range predicate symbol *)
      waiting : Ty.tysymbol option }

let empty = 
    { bounded = Ty.Mts.empty;
      conv    = Term.Sls.empty;
      types   = Ty.Mts.empty;
      funs    = Term.Mls.empty;
      waiting = None }

(* Eliminate bounded types in types. *)
let rec eliminate_type env ty =
  match ty.Ty.ty_node with
    | Ty.Tyapp (ts, []) when Ty.Mts.mem ts env.bounded ->
      fst (Ty.Mts.find ts env.bounded)
    | Ty.Tyapp (ts, args) ->
      let ts = try Ty.Mts.find ts env.types
        with Not_found ->
          match env.waiting with
            | None -> assert false
            | Some ts2 -> if Ty.ts_equal ts ts2 then
                failwith ("Bounded type " ^ ts2.Ty.ts_name.id_string ^
                             " is used before its inrange function was found.")
              else assert false in
      let args = List.map (eliminate_type env) args in
      Ty.ty_app ts args
    | Ty.Tyvar _ -> ty

let is_bounded_type env ty =
  match ty.Ty.ty_node with
    | Ty.Tyapp (tys, []) -> Ty.Mts.mem tys env.bounded
    | _ -> false

let is_bounded_opt_type env oty =
  match oty with
    | None -> false
    | Some ty -> is_bounded_type env ty

let eliminate_opt_type env oty = 
  match oty with
    | None -> None
    | Some ty -> Some (eliminate_type env ty)

(* Eliminate bounded types in type definitions.
   Keep existing type symbol if no bounded type is found
   (necessary for special type symbols like int) *)
let eliminate_tys env tys =
  match tys.Ty.ts_def with
    | None -> tys
    | Some ty ->
      let nty = eliminate_type env ty in
      if Ty.ty_equal ty nty then tys
      else
        let ts_name = id_clone tys.Ty.ts_name in
        Ty.create_tysymbol ts_name tys.Ty.ts_args (Some nty)

(* Eliminate bounded types in a variable symbols.*)
let eliminate_vs env vsymbols vs =
  try Term.Mvs.find vs vsymbols with
      Not_found -> 
        let vs_ty = eliminate_type env vs.Term.vs_ty in
        let vs_name = id_clone vs.Term.vs_name in
        let vs = Term.create_vsymbol vs_name vs_ty in
        vs

(* Translate pattern with the appropriate types and function symbols.
   Do not generate constraints. *)
let rec eliminate_pattern env vsymbols vars pat =
  match pat.Term.pat_node with
    | Term.Pwild ->
      let pat_ty = eliminate_type env pat.Term.pat_ty in
      vars, Term.pat_wild pat_ty, vsymbols
    | Term.Pvar vs ->
      let nvs = eliminate_vs env vsymbols vs in
      Term.Svs.add nvs vars, Term.pat_var nvs, Term.Mvs.add vs nvs vsymbols
    | Term.Papp (ls, [pat]) when Term.Sls.mem ls env.conv ->
      (* Ignore conversion functions *)
      eliminate_pattern env vsymbols vars pat
    | Term.Papp (ls, pl) ->
      let nls = try Term.Mls.find ls env.funs with
          Not_found -> assert false in
      let vars, pl, vsymbols = List.fold_right (fun pat (vars, pl, vsymbols) ->
        let vars, pat, vsymbols = eliminate_pattern env vsymbols vars pat in
        (vars, pat :: pl, vsymbols)) pl (vars, [], vsymbols) in
      let pat_ty = eliminate_type env pat.Term.pat_ty in
      vars, Term.pat_app nls pl pat_ty, vsymbols
    | Term.Por (p1, p2) ->
        let vars, p1, vsymbols = eliminate_pattern env vsymbols vars p1 in
        let vars, p2, vsymbols = eliminate_pattern env vsymbols vars p2 in
        vars, Term.pat_or p1 p2, vsymbols
    | Term.Pas (p, vs) ->
      let vars, p, vsymbols = eliminate_pattern env vsymbols vars p in
      let nvs = eliminate_vs env vsymbols vs in
      Term.Svs.add nvs vars, Term.pat_as p nvs, Term.Mvs.add vs nvs vsymbols

let eliminate_pattern env vsymbols pat =
  eliminate_pattern env vsymbols Term.Svs.empty pat

let reconstruct pol t guards =
  if pol then
    Term.Sterm.fold Term.t_and guards t
  else
    Term.Sterm.fold Term.t_implies guards t

let rec all_open_quant q b =
  let (vl, trs, t) as res = Term.t_open_quant b in
  if trs <> [] then res
  else
    match t.Term.t_node with
      | Term.Tquant (q2, _) when q2 <> q -> res
      | Term.Tquant (_, b) ->
        let vl2, trs2, t2 = all_open_quant q b in
        vl @ vl2, trs2, t2
      | _ -> res

let eliminate_vs_with_guards env vs (vars, vsymbols, guards) =
  let nvs = eliminate_vs env vsymbols vs in
  let guards = match vs.Term.vs_ty.Ty.ty_node with
    | Ty.Tyapp (ts, []) when Ty.Mts.mem ts env.bounded ->
      let _, p = Ty.Mts.find ts env.bounded in
      Term.Sterm.add (p (Term.t_var nvs)) guards
    | _ -> guards in
  (nvs :: vars, Term.Mvs.add vs nvs vsymbols, guards)

(* Mode used to specify what should be done with computed constraints.
   - Use Inline (polarity) to inline them
   - Use Keep (vars, with_error) to keep those which do not contain vars.
     If with_error is true then fail when a constraint is missed. *)
type reconstruction_mode = 
  | Keep of (Term.Svs.t * bool) 
  | Inline of bool

let mode_keep_guards with_error mode =
  match mode with
    | Keep _ -> mode
    | Inline _ -> Keep (Term.Svs.empty, with_error)

let mode_add_bounded_variables vs mode =
  match mode with
    | Inline _ -> mode
    | Keep (vs2, b) -> Keep (Term.Svs.union vs vs2, b)

exception Unable_to_compute

let new_guard suppressed mode p guards =
  match mode with
    | Inline _ -> suppressed, Term.Sterm.add p guards
    | Keep (vs, b) ->
      if Term.t_v_any (fun v -> Term.Svs.mem v vs) p then
        if b then raise Unable_to_compute else true, guards
      else suppressed, Term.Sterm.add p guards

(* Compute assumptions for terms of bounded types in t.
   For each subterm t' of a bounded type in t, generates an additionnal
   constraint in_range (t') *)
let rec compute_guards suppressed mode guards env vsymbols t =
  match t.Term.t_node with
    | Term.Tvar vs -> 
      suppressed, (try Term.t_var (Term.Mvs.find vs vsymbols)
        with Not_found -> assert false), guards
    | Term.Tapp (ls, [t]) when Term.Sls.mem ls env.conv ->
      (* Ignore conversion functions *)
      compute_guards suppressed mode guards env vsymbols t
    | Term.Tapp (ls, []) when is_bounded_opt_type env (ls.Term.ls_value) ->
      (* Do not add constraints for constants *)
      let nls = try (Term.Mls.find ls env.funs) with
          Not_found -> assert false in
      let ty = eliminate_opt_type env t.Term.t_ty in
      let nt = Term.t_app nls [] ty in
      suppressed, nt, guards
    | Term.Tapp (ls, tl) ->
      (* If the result of the application is a bounded type,
         add a corresponding inrange constraint over it *)
      let mode = mode_keep_guards false mode in
      let suppressed, tl, guards = List.fold_right 
        (fun t (suppressed, tl, guards) ->
          let suppressed, t, guards = 
            eliminate_term suppressed mode guards env vsymbols t in
          suppressed, t :: tl, guards) tl (suppressed, [], guards) in
      let nls = try (Term.Mls.find ls env.funs) with
          Not_found -> assert false in
      let ty = eliminate_opt_type env t.Term.t_ty in
      let nt = Term.t_app nls tl ty in
      let suppressed, guards = match t.Term.t_ty with
        | None -> suppressed, guards
        | Some ty ->
          match ty.Ty.ty_node with
            | Ty.Tyapp (tys, []) ->
              (try let _, p = Ty.Mts.find tys env.bounded in
                   new_guard suppressed mode (p nt) guards
               with Not_found -> suppressed, guards)
            | _ -> suppressed, guards in
      suppressed, nt, guards
    | Term.Tif (t1, t2, t3) ->
      (* In if t1 then t2 else t3, t1 has both polarities.
         If mode is inline, then try to keep the guards g1 generated for t1 
         to output g1 /\ if t1 then t2 else t3.
         If some constraint is lost, rather transform into
         (t1 -> t2) /\ (not t1 -> t3) *)
      let suppressed, t2, guards = 
        eliminate_term suppressed mode guards env vsymbols t2 in
      let suppressed, t3, guards = 
        eliminate_term suppressed mode guards env vsymbols t3 in
      (match mode with
        | Keep _ ->
          let suppressed, t1, guards = 
            eliminate_term suppressed mode guards env vsymbols t1 in
          let t = Term.t_if t1 t2 t3 in
          suppressed, t, guards
        | Inline pol ->
          try 
            let mode = mode_keep_guards true mode in
            let suppressed, t1, guards = 
              eliminate_term suppressed mode guards env vsymbols t1 in
            let t = Term.t_if t1 t2 t3 in
            suppressed, t, guards
          with Unable_to_compute ->
            let suppressed, nt1, guards = 
              eliminate_term suppressed (Inline (not pol)) guards env
                vsymbols (Term.t_not t1) in
            let suppressed, t1, guards = 
              eliminate_term suppressed (Inline (not pol)) guards env
                vsymbols t1 in
            let t = Term.t_and (Term.t_implies t1 t2) (Term.t_implies nt1 t3) in
            suppressed, t, guards)
    | Term.Tlet (t, tbound) ->
      (* In let x = t1 in t2, t1 can have both polarities.
         If mode is inline, then keep as many guards g1 generated for t1 as
         possible and output g1 /\ let x = t1 in t2.
         If mode is keep, replace x by t1 in the guards of t2 *)
      let suppressed, t, guards =
        let mode = mode_keep_guards false mode in
        eliminate_term suppressed mode guards env vsymbols t in
      let vs, t2 = Term.t_open_bound tbound in
      let nvs = eliminate_vs env vsymbols vs in
      let vsymbols = Term.Mvs.add vs nvs vsymbols in
      let suppressed, t2, guards2 = 
        eliminate_term suppressed mode Term.Sterm.empty env vsymbols t2 in
      let guards = Term.Sterm.fold (fun p guards ->
        let p = Term.t_subst_single nvs t p in
        Term.Sterm.add p guards) guards2 guards in
      let tbound = Term.t_close_bound nvs t2 in
      suppressed, Term.t_let t tbound, guards
    | Term.Tcase (t, tbrl) -> 
      (* If mode is inline, then keep as many guards g generated for t as
         possible and output g /\ match t with (p1 -> t1 ...).
         If mode is keep, only keep guards of t1 ... that do not contain
         variables of p1 ... *)
      let suppressed, t, guards = 
        let mode = mode_keep_guards false mode in
        eliminate_term suppressed mode guards env vsymbols t in
      let suppressed, tbrl, guards = List.fold_right 
        (fun br (suppressed, tbrl, guards) ->
          let (pat, t) = Term.t_open_branch br in
          let vars, pat, vsymbols = eliminate_pattern env vsymbols pat in
          let mode = mode_add_bounded_variables vars mode in
          let suppressed, t, guards = 
            eliminate_term suppressed mode guards env vsymbols t in
          suppressed, (Term.t_close_branch pat t) :: tbrl, guards) tbrl 
        (suppressed, [], guards) in
      suppressed, Term.t_case t tbrl, guards
    | Term.Teps (tbound) ->
      (* If mode is keep, only keep guards of f that do not contain
         variables of vs *)
      let vs, t = Term.t_open_bound tbound in
      let nvs = eliminate_vs env vsymbols vs in
      let vsymbols = Term.Mvs.add vs nvs vsymbols in
      let mode = mode_keep_guards false mode in
      let suppressed, t, guards = 
        eliminate_term suppressed mode guards env vsymbols t in
      let tbound = Term.t_close_bound nvs t in
      suppressed, Term.t_eps tbound, guards
    | Term.Tconst _ -> suppressed, t, guards
    | Term.Tbinop (b, t1, t2) ->
      (match b, mode with
        | Term.Timplies, Inline pol ->
          let suppressed, t1, guards = 
            eliminate_term suppressed (Inline (not pol)) guards env 
              vsymbols t1 in
          let suppressed, t2, guards = 
            eliminate_term suppressed mode guards env vsymbols t2 in
          suppressed, Term.t_implies t1 t2, guards
        | Term.Tiff, Inline pol ->
          (* In t1 <-> t2, t1 and t2 have both polarities.
             If mode is inline, then try to keep the guards gi generated for ti 
             to output g1 /\ g2 /\ (t1 <-> t2).
             If some constraint is lost, rather transform into:
             - if pol then (t1 -> t2) /\ (t2 -> t1)
             - if not pol then (t1 /\ t2) \/ (not t1 /\ not t2) *)
          (try
             let mode = mode_keep_guards true mode in
             let suppressed, t1, guards = 
               eliminate_term suppressed mode guards env vsymbols t1 in
             let suppressed, t2, guards = 
               eliminate_term suppressed mode guards env vsymbols t2 in
             suppressed, Term.t_iff t1 t2, guards
           with Unable_to_compute ->
             let suppressed, nt1, guards = 
               eliminate_term suppressed mode guards env vsymbols 
                 (Term.t_not t1) in
             let suppressed, nt2, guards = 
               eliminate_term suppressed mode guards env vsymbols 
                 (Term.t_not t2) in
             let suppressed, t1, guards = 
               eliminate_term suppressed mode guards env vsymbols t1 in
             let suppressed, t2, guards = 
               eliminate_term suppressed mode guards env vsymbols t2 in
             let t =
               if pol then Term.t_and (Term.t_or nt1 t2) (Term.t_or t1 nt2)
               else Term.t_or (Term.t_and t1 t2) (Term.t_and nt1 nt2) in
             suppressed, t, guards)
        | _, _ ->
          let suppressed, t1, guards = 
            eliminate_term suppressed mode guards env vsymbols t1 in
          let suppressed, t2, guards = 
            eliminate_term suppressed mode guards env vsymbols t2 in
          suppressed, Term.t_binary b t1 t2, guards)
    | Term.Ttrue | Term.Tfalse -> suppressed, t, guards
    | Term.Tnot t -> 
      let suppressed, t, guards = 
        eliminate_term suppressed mode guards env vsymbols t in
      suppressed, Term.t_not t, guards
    | Term.Tquant (q, tquant) ->
      (* forall x : bounded. f (x) is translated as forall x : bounded.
         in_range (x) -> f (x)
         exits x : bounded. f (x) is translated as exists x : bounded.
         in_range (x) /\ f (x)
         If mode is keep, only keep guards of f (x) that do not contain x *)
      let (vsl, trs, t) = all_open_quant q tquant in
      let vsl, vsymbols, q_guards = List.fold_right
        (eliminate_vs_with_guards env) vsl 
        ([], vsymbols, Term.Sterm.empty) in
      let trs = 
        let mode = mode_keep_guards false mode in
        List.map (fun l -> List.map (fun tr ->
          let _, tr, _ =
            eliminate_term suppressed mode guards env vsymbols tr in
          tr) l) trs in
      let mode = mode_add_bounded_variables (Term.Svs.of_list vsl) mode in
      let suppressed, nt, guards = 
        eliminate_term suppressed mode guards env vsymbols t in
      let nt = reconstruct (q = Term.Texists) nt q_guards in
      suppressed, Term.t_quant q (Term.t_close_quant vsl trs nt), guards

and eliminate_term suppressed mode guards env vsymbols t =
  let suppressed, nt, guards = 
    compute_guards suppressed mode guards env vsymbols t in
  match mode with
    | Inline pol -> suppressed, reconstruct pol nt guards, Term.Sterm.empty
    | Keep _ -> suppressed,  nt, guards

let eliminate_form env ?(polarity = true) ?(vsymbols = Term.Mvs.empty) t = 
  let suppressed, t, _ = 
    eliminate_term false (Inline polarity) Term.Sterm.empty env 
      vsymbols t in
  if output_warning && suppressed then
    prerr_endline "Constraints were forgotten during eliminate_bounded_types";
  t

let eliminate_term env ?(with_error = false) ?(vsymbols = Term.Mvs.empty) t =
  let suppressed, t, guards = 
    eliminate_term false (Keep (Term.Svs.empty, with_error)) 
      Term.Sterm.empty env vsymbols t in
  if output_warning && suppressed then
    prerr_endline "Constraints were forgotten during eliminate_bounded_types";
  t, guards

(* Eliminate bounded types in a function declaration
   Keep existing function symbol if no bounded type is found
   (necessary for special function symbols).*)
let eliminate_ls env ls =
  let ls_args, b = List.fold_right (fun ty (ls_args, b) ->
    let nty = eliminate_type env ty in
    if Ty.ty_equal ty nty then
      nty :: ls_args, b
    else  nty :: ls_args, true) ls.Term.ls_args ([], false) in
  let ls_value, b = match ls.Term.ls_value with
    | None -> None, b
    | Some ty ->
      let nty = eliminate_type env ty in
      if Ty.ty_equal ty nty then Some nty, b else Some nty, true in
  (* ??? Handle ls_opaque *)
  if b then
    let ls_name = id_clone ls.Term.ls_name in
    Term.create_lsymbol ~opaque:ls.Term.ls_opaque ~constr:ls.Term.ls_constr
      ls_name ls_args ls_value
  else ls

(* Eliminate bounded types in a function definition.
   Try to keep the definition and generate an additionnal axiom for
   constraints. Constraints should not be inlined in the definition.
   If some constraint is lost, then rather translate the definition into
   a declaration with a defining axiom. *)
let eliminate_ls_defn env (ls, defn) nls =
  let vars, t = open_ls_defn defn in
  let nvars, vsymbols, q_guards = List.fold_right (eliminate_vs_with_guards env)
    vars ([], Term.Mvs.empty, Term.Sterm.empty) in
  try let t, constrs =
        eliminate_term env ~with_error:true ~vsymbols:vsymbols t in
      let ndefn = make_ls_defn nls nvars t in
      if Term.Sterm.is_empty constrs then
        Some ndefn, None
      else
        let nargs = List.map Term.t_var nvars in
        let napp = Term.t_app nls nargs nls.Term.ls_value in
        let p = reconstruct true Term.t_true constrs in
        let p_guarded = reconstruct false p q_guards in
        let ntquant = Term.t_close_quant nvars [[napp]] p_guarded in
        let nax = Term.t_forall ntquant in
        Some ndefn, Some nax
  with Unable_to_compute ->
    let args = List.map Term.t_var vars in
    let app = Term.t_app ls args ls.Term.ls_value in
    let p = if nls.Term.ls_value = None then
        Term.t_iff app t else Term.t_equ app t in
    let tquant = Term.t_close_quant vars [[app]] p in
    let ax = Term.t_forall tquant in
    let nax = eliminate_form env ax in
    None, Some nax

(* Generic transformation.
   Should be called with theories of the form:
     type t "ty_lab"
     predicate inrange "p_lab" (x : base) = ...
     function of_base "f_lab" (x : base) : t
     function to_base "f_lab" (x : t) : base
     axiom to_base__def "ax_lab": ...
     ...
   Replace t every where with base and generates applications of inrange
   if needed.
   Remove applications of of_base and to_base.
   Remove axiom to_base__def.
*)
let generic_eliminate_bounded_types ty_lab f_lab p_lab ax_lab =
 Trans.fold_map (fun thd (env, tsk) ->
   match thd.task_decl.td_node with
     | Decl d ->
       (match d.d_node with
         | Dtype tys ->
           (* For logic type declarations:
              - if tys is a bounded type, store the declaration in waiting
              - otherwise, translate the type declaration
           *)
           if Slab.mem ty_lab tys.Ty.ts_name.id_label then
             if (tys.Ty.ts_args = [] && tys.Ty.ts_def = None) then
               match env.waiting with
                 | Some tys ->
                   failwith ("No predicate was found for bounded type " ^
                              tys.Ty.ts_name.id_string);
                 | None ->
                   (* A bounded type was found, wait for in_range function. *)
                   ({ env with waiting = Some tys }, tsk)
             else
               if tys.Ty.ts_args <> [] then
                 failwith ("Bounded type " ^ tys.Ty.ts_name.id_string ^ 
                              " should not have a definition")
               else failwith ("Bounded type " ^ tys.Ty.ts_name.id_string ^ 
                                 " should not be polymorphic")
           else 
             let ntys = eliminate_tys env tys in
             let tsk = add_ty_decl tsk ntys in
             let types = Ty.Mts.add tys ntys env.types in
             ({ env with types = types }, tsk)
         | Ddata dl ->
           (* For a declaration of recursive data types:
              - translate every type declaration
              - translate all the constructors
           *) 
           let types, dl = List.fold_right
             (fun (tys, cstrl) (types, dl) ->
               let ntys = eliminate_tys 
                 { env with types = types } tys in
               let types = Ty.Mts.add tys ntys types in
               types, (ntys, cstrl) :: dl) dl (env.types, []) in
           let env = { env with types = types } in
           let funs, dl = List.fold_right
             (fun (ntys, cstrl) (funs, dl) ->
               let funs, cstrl = List.fold_right
                 (fun (ls, lsol) (funs, cstrl) ->
                   let nls = eliminate_ls 
                     { env with funs = funs } ls in
                   let funs = Term.Mls.add ls nls funs in
                   let funs, lsol = List.fold_right
                     (fun lso (funs, lsol) ->
                       let funs, lso = match lso with
                         | None -> funs, None
                         | Some ls ->
                           let nls = eliminate_ls 
                             { env with funs = funs } ls in
                           let funs = Term.Mls.add ls nls funs in
                           funs, Some nls in
                       funs, lso :: lsol) lsol (funs, []) in
                   (funs, (nls, lsol) :: cstrl)) cstrl (funs, []) in
               funs, (ntys, cstrl) :: dl) dl (env.funs, []) in
           let tsk = add_data_decl tsk dl in
           ({ env with types = types; funs = funs }, tsk)
         | Dparam ({ Term.ls_args = []; 
                    Term.ls_value = 
             Some { Ty.ty_node = Ty.Tyapp (tys, []) } } as ls)
             when Ty.Mts.mem tys env.bounded -> 
           (* For a constant c of bounded type, 
              declare an axiom in_range (c) *)
           let nty, ps = Ty.Mts.find tys env.bounded in
           let nls = eliminate_ls env ls in
           let tsk = add_param_decl tsk nls in
           let p = ps (Term.t_app nls [] (Some nty)) in
           let pr_name = id_fresh (nls.Term.ls_name.id_string ^ "__def") in
           let prs = create_prsymbol pr_name in
           let tsk = add_prop_decl tsk Paxiom prs p in
           let funs = Term.Mls.add ls nls env.funs in
           ({ env with funs = funs }, tsk)
         | Dparam ({ Term.ls_args = [bty]; 
                    Term.ls_value = None } as ls)
             when Slab.mem p_lab ls.Term.ls_name.id_label ->
           (* Some in_range function was found *)
           (match env.waiting with
             | None -> failwith 
               ("No bounded type declaration was found before predicate " ^
                   ls.Term.ls_name.id_string)
             | Some tys ->
                 let nls = eliminate_ls env ls in
                 let tsk = add_param_decl tsk nls in
                 let funs = Term.Mls.add ls nls env.funs in
                 let inrange t = Term.t_app nls [t] None in
                 let bounded = Ty.Mts.add tys (bty, inrange) env.bounded in
                 ({ env with waiting = None; funs = funs; bounded = bounded },
                  tsk))
         | Dparam ({ Term.ls_args = [ty1]; 
                     Term.ls_value = Some ty2 } as ls)
             when Slab.mem f_lab ls.Term.ls_name.id_label ->
           (* Some conversion function was found *)
           let nty1 = eliminate_type env ty1 in
           let nty2 = eliminate_type env ty2 in
           if Ty.ty_equal nty1 nty2 then
             let conv = Term.Sls.add ls env.conv in
             ({ env with conv = conv }, tsk)
           else failwith ("Function " ^ ls.Term.ls_name.id_string ^
                             " is not a conversion function.")
         | Dparam ls ->
           (* For a function declaration, translate the types if needed *)
           let nls = eliminate_ls env ls in
           let tsk = add_param_decl tsk nls in
           let funs = Term.Mls.add ls nls env.funs in
           ({ env with funs = funs }, tsk)
         | Dlogic [{ Term.ls_args = [bty]; 
                     Term.ls_value = None } as ls, defn]
             when Slab.mem p_lab ls.Term.ls_name.id_label ->
           (* Some in_range function was found *)
           (match env.waiting with
             | None -> failwith 
               ("No bounded type declaration was found before predicate " ^
                   ls.Term.ls_name.id_string)
             | Some tys ->
               let nls = eliminate_ls env ls in
               let inlined =
                 if inline_inrange then
                   let _, def = open_ls_defn defn in
                   if Term.t_s_any (fun _ -> false)
                     (fun vls -> Term.ls_equal vls ls) def then
                     (* inrange is recursive, do not inline *)
                     None
                   else
                     match eliminate_ls_defn env (ls, defn) nls with
                       | Some (_, defn), None ->
                         let vs, def = match open_ls_defn defn with
                             [vs], def -> vs, def
                           | _, _ -> assert false in
                         let inrange t = Term.t_subst_single vs t def in
                         let bounded =
                           Ty.Mts.add tys (bty, inrange) env.bounded in
                         let funs = Term.Mls.add ls nls env.funs in
                         let tsk = add_logic_decl tsk [nls, defn] in
                         Some ({ env with waiting = None; bounded = bounded;
                           funs = funs }, tsk)
                       | _, _ -> 
                         (* inrange takes some bounded type argument,
                            do not inline *)
                         None
                 else None in
               match inlined with
                 | Some r -> r
                 | None ->
                   let inrange t = Term.t_app nls [t] None in
                   let funs = Term.Mls.add ls nls env.funs in
                   let bounded = Ty.Mts.add tys (bty, inrange) env.bounded in
                   let env = { env with waiting = None; funs = funs;
                     bounded = bounded } in
                   let defn, ax = 
                     eliminate_ls_defn env (ls, defn) nls in
                   let tsk = match defn with
                     | None -> add_param_decl tsk nls
                     | Some defn -> add_logic_decl tsk [defn] in
                   let tsk = match ax with
                     | None -> tsk
                     | Some ax ->
                       let prs = create_prsymbol 
                         (id_fresh (nls.Term.ls_name.id_string ^ "__def")) in
                       add_prop_decl tsk Paxiom prs ax in
                   (env, tsk))
         | Dlogic ld ->
           (* For recursive function definitions:
              - translate every declaration
              - translate the definitions and add a new axiom if needed
              - assume the new axioms *)
           let (funs, ld) = 
             List.fold_right (fun (ls, defn) (funs, ld) ->
               let nls = eliminate_ls env ls in
               let funs = Term.Mls.add ls nls funs in
               (funs, (ls, nls, defn) :: ld)) ld (env.funs, []) in
           let env = { env with funs = funs } in
           let (tsk, axs, ld) = 
             List.fold_right (fun (ls, nls, defn) (tsk, axs, ld) ->
               let defn, ax = 
                 eliminate_ls_defn env (ls, defn) nls in
               let tsk, ld = match defn with
                 | None -> add_param_decl tsk nls, ld
                 | Some defn -> tsk, defn :: ld in
               let axs = match ax with
                 | None -> axs
                 | Some ax ->
                   let prs = create_prsymbol 
                     (id_fresh (nls.Term.ls_name.id_string ^ "__def")) in
                   (prs, ax) :: axs in
               (tsk, axs, ld)) ld (tsk, [], []) in
           let tsk = if ld = [] then tsk else add_logic_decl tsk ld in
           let tsk = List.fold_left (fun tsk (prs, ax) ->
             add_prop_decl tsk Paxiom prs ax) tsk axs in
           (env, tsk)
         | Dind (sgn, l) ->
           (* For recursive inductive predicates definitions:
              - translate every declaration
              - translate the definitions *)
           let funs, l = List.fold_right (fun (ls, defl) (funs, l) ->
             let nls = eliminate_ls env ls in
             let funs = Term.Mls.add ls nls funs in
             funs, (nls, defl) :: l) l (env.funs, []) in
           let env = { env with funs = funs } in
           let l = List.fold_right (fun (nls, defl) l ->
             let defl = List.map (fun (ps, t) ->
               let t = eliminate_form env t in
               ps, t) defl in
             (nls, defl) :: l) l [] in
           let tsk = add_ind_decl tsk sgn l in
           (env, tsk)
         | Dprop (Paxiom, prs, _)
             when Slab.mem ax_lab prs.pr_name.id_label ->
           (* Some defining axiom for conversion functions was found *)
           (env, tsk)
         | Dprop (Pgoal, prs, t) ->
           (* Goals have negative polarity *)
           let t = eliminate_form env ~polarity:false t in
           let tsk = add_prop_decl tsk Pgoal prs t in
           (env, tsk)
         | Dprop (k, prs, t) ->
           (* Other propositions have positive polarity *)
           let t = eliminate_form env t in
           let tsk = add_prop_decl tsk k prs t in
           (env, tsk)
       )
     | _ -> (env, add_tdecl tsk thd.task_decl)
 ) empty None

let bounded_type_label = create_label "bounded_type"

let eliminate_bounded_types = generic_eliminate_bounded_types
  bounded_type_label bounded_type_label bounded_type_label bounded_type_label

let () =
  Trans.register_transform "eliminate_bounded_types" eliminate_bounded_types
    ~desc:"";
