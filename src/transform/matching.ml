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


exception NoMatch of term * term


(* Utility to remove bool/prop coercions.
   (matching is done modulo those) *)
let rec remove_bp = function
  | {t_node = Tapp(ls,[t;tt])}
    when ls_equal ls ps_equ && t_equal_nt_na tt t_bool_true -> remove_bp t
  | {t_node = Tif (t,tt,tf)}
    when t_equal_nt_na tt t_bool_true
      && t_equal_nt_na tf t_bool_false -> remove_bp t
  | t -> t


(* Term matching:
     Find an extension of the type+term substitution
     [mty,mv] such that [tp[mty,mv]=tm] and such that the
     extension does not pick terms with free variables in [bnd].
     Fail if the extension does not exists.
   [bnd] is used internally to prevent matching from selecting terms with
     variables bound to an inner quantifier. *)
let rec matching bnd mty mv tp tm =
  let fail () = raise (NoMatch (tp,tm)) in
  let tp, tm = remove_bp tp, remove_bp tm in
  match tp.t_node, tm.t_node with
  | Tvar vp, _ ->
    (* Cast prop to bool as variable must be bool-typed. *)
    let tmf = match tm.t_ty with
    | Some _ -> tm
    | None -> t_if tm t_bool_true t_bool_false
    in
    begin match Mvs.find vp mv with
    (* FIXME? If term have distinct attributes/triggers,
       only the attributes/triggers coming from the first match are kept. *)
    | tb -> if t_equal_nt_na (remove_bp tb) tm then mty, mv else fail ()
    | exception Not_found -> match oty_match mty tp.t_ty tmf.t_ty with
    | mty ->
      if Mvs.set_disjoint bnd (t_vars tm)
      then
        mty, Mvs.add vp tmf mv
      else fail ()
    | exception TypeMismatch _ -> fail ()
    end
  | (Tconst _ | Ttrue | Tfalse), _ when t_equal_nt_na tp tm ->
    mty, mv
  | Tapp (lsp,lp), Tapp (lsm,lm) when ls_equal lsp lsm ->
    let mty = try oty_match mty tp.t_ty tm.t_ty
      with TypeMismatch _ -> fail () in
    List.fold_left2 (fun (mty,mv) tp tm ->
      matching bnd mty mv tp tm) (mty,mv) lp lm
  | Tif (tpb,tpt,tpe), Tif (tmb,tmt,tme) ->
    let mty, mv = matching bnd mty mv tpb tmb in
    let mty, mv = matching bnd mty mv tpt tmt in
    matching bnd mty mv tpe tme
  | Tbinop (bp,tp_l,tp_r), Tbinop (bm,tm_l,tm_r) when bp = bm ->
    let mty, mc = matching bnd mty mv tp_l tm_l in
    matching bnd mty mc tp_r tm_r
  | Tnot tp, Tnot tm -> matching bnd mty mv tp tm
  | Tlet (tpd,tpv), Tlet (tmd,tmv) ->
    let mty, mv = matching bnd mty mv tpd tmd in
    let vsp, tpv = t_open_bound tpv in
    let vsm, tmv = t_open_bound tmv in
    let mty, mv =
      matching (Svs.add vsm bnd) mty (Mvs.add vsp (t_var vsm) mv) tpv tmv in
    mty, Mvs.remove vsp mv
  | Tcase (tps,lbrp), Tcase (tms,lbrm) ->
    let mty, mv = matching bnd mty mv tps tms in
    let rec pat_matching bnd mv pp pm =
      match pp.pat_node, pm.pat_node with
      | Pwild, Pwild -> bnd, mv
      | Pvar vsp, Pvar vsm -> Svs.add vsm bnd, Mvs.add vsp (t_var vsm) mv
      | Papp (lsp,lpp), Papp (lsm,lpm) when ls_equal lsp lsm ->
        List.fold_left2 (fun (bnd,mv) pp pm ->
          pat_matching bnd mv pp pm) (bnd,mv) lpp lpm
      | Por (pp_l,pp_r), Por (pm_l,pm_r) ->
        let bnd, mv = pat_matching bnd mv pp_l pm_l in
        pat_matching bnd mv pp_r pm_r
      | Pas (pp,vsp), Pas (pm,vsm) ->
        pat_matching (Svs.add vsm bnd) (Mvs.add vsp (t_var vsm) mv) pp pm
      | _ -> fail ()
    in
    let fn (mty,mv) brp brm =
      let pp, tp = t_open_branch brp in
      let pm, tm = t_open_branch brm in
      let bnd, mv = pat_matching bnd mv pp pm in
      let mty, mv = matching bnd mty mv tp tm in
      mty, Svs.fold Mvs.remove pp.pat_vars mv
    in
    List.fold_left2 fn (mty,mv) lbrp lbrm
  | Teps tpb, Teps tmb ->
    let vsp, tpb = t_open_bound tpb in
    let vsm, tmb = t_open_bound tmb in
    let mty = try ty_match mty vsp.vs_ty vsm.vs_ty
      with TypeMismatch _ -> fail () in
    let mty, mv =
      matching (Svs.add vsm bnd) mty (Mvs.add vsp (t_var vsm) mv) tpb tmb in
    mty, Mvs.remove vsp mv
  | Tquant (qp,tpq), Tquant (qm,tmq) when qp = qm ->
    let vlp, _, tpq = t_open_quant tpq in
    let vlm, _, tmq = t_open_quant tmq in
    let bnd, mty, mv = try List.fold_left2 (fun (bnd,mty,mv) vsp vsm ->
        let mty = ty_match mty vsp.vs_ty vsm.vs_ty in
        Svs.add vsm bnd, mty, Mvs.add vsp (t_var vsm) mv) (bnd,mty,mv) vlp vlm
      with Invalid_argument _ | TypeMismatch _ -> fail ()
    in
    let mty, mv = matching bnd mty mv tpq tmq in
    mty, List.fold_left (fun mv vsp -> Mvs.remove vsp mv) mv vlp
  | _ -> fail ()

(* Root term matching: [bnd] empty. *)
let matching mty mv tp tm = matching Svs.empty mty mv tp tm


(* From now on: compiled matching.
     Provide a mean to convert term patterns into matching
     scripts. Also provide a mean to group matching scripts
     as scripts matching multiple patterns at once.
   The grouping script may be more efficient than running the
     scripts one-by-one, as common prefixes of the matching
     scripts are all executed as the same time. *)

(* Term constructions on which matching scripts may switch:
     If several matching scripts choose to test different constructions,
     the correct one is found before resuming the execution of the
     corresponding scripts. *)
type construction =
  | Crigid of vsymbol
  | Cbound of int
  | Cconst of term
  | Capp of lsymbol
  | Cif
  | Clet
  | Ccase of int
  | Ceps
  | Cquant of quant * int
  | Cbinop of binop
  | Cnot

module C = struct
  type t = construction
  let compare t1 t2 =
    let (--) = Pervasives.compare in
    match t1, t2 with
    | Crigid vs1, Crigid vs2 -> vs_compare vs1 vs2
    | Cbound n1, Cbound n2 | Ccase n1, Ccase n2 -> n1 -- n2
    | Cconst t1, Cconst t2 ->
      (* FIXME? is there a better way to achieve
         attribute-independent comparison ?
         (Note that terms are not nested here, so that
          code actually works) *)
      t_compare (t_attr_set Sattr.empty t1) (t_attr_set Sattr.empty t2)
    | Capp ls1, Capp ls2 -> ls_compare ls1 ls2
    | Cquant (q1,n1), Cquant (q2,n2) ->
      let c = q1 -- q2 in if c <> 0 then c else n1 -- n2
    | Cbinop b1, Cbinop b2 -> b1 -- b2
    | Cif, Cif | Clet, Clet | Ceps, Ceps | Cnot, Cnot -> 0
    | Crigid _, _ -> -1 | _, Crigid _ -> 1
    | Cbound _, _ -> -1 | _, Cbound _ -> 1
    | Cconst _, _ -> -1 | _, Cconst _ -> 1
    | Capp _, _   -> -1 | _, Capp _   -> 1
    | Cif, _      -> -1 | _, Cif      -> 1
    | Clet, _     -> -1 | _, Clet     -> 1
    | Ccase _, _  -> -1 | _, Ccase _  -> 1
    | Ceps, _     -> -1 | _, Ceps     -> 1
    | Cquant _, _ -> -1 | _, Cquant _ -> 1
    | Cbinop _, _ -> -1 | _, Cbinop _ -> 1
end
module MC = Extmap.Make(C)

(* Same construction for types (type matching can be necessary) *)
type ty_construction =
  | TyCrigid of tvsymbol
  | TyCapp of tysymbol

module Cty = struct
  type t = ty_construction
  let compare ty1 ty2 =
    match ty1, ty2 with
    | TyCrigid tv1, TyCrigid tv2 -> tv_compare tv1 tv2
    | TyCapp ts1, TyCapp ts2 -> ts_compare ts1 ts2
    | TyCrigid _, _ -> -1 | _, TyCrigid _ -> 1
end
module MCty = Extmap.Make(Cty)

(* Same construction for patterns *)
type pat_construction =
  | PatCwild
  | PatCvar
  | PatCapp of lsymbol
  | PatCor
  | PatCas

module Cpat = struct
  type t = pat_construction
  let compare p1 p2 =
    match p1, p2 with
    | PatCapp ls1, PatCapp ls2 -> ls_compare ls1 ls2
    | PatCwild, PatCwild | PatCvar, PatCvar
    | PatCor, PatCor | PatCas, PatCas -> 0
    | PatCwild, _  -> -1 | _, PatCwild  -> 1
    | PatCvar, _   -> -1 | _, PatCvar   -> 1
    | PatCapp _, _ -> -1 | _, PatCapp _ -> 1
    | PatCor, _    -> -1 | _, PatCor    -> 1
end
module MCpat = Extmap.Make(Cpat)

(* Instructions of matching scripts, operating on matching state
   (defined later because it contains the remaining instructions).
   type ['i] is int list for practical purposes, but is a different type
     during compilation of patterns. The list represents:
   . For pattern constructions:
       variables, constants, applications, and epsilons,
     it may be [0] or []. The first say that type should be stored
     when term is analysed, the second say it should not.
   . For quantifier pattern:
     it gives the list of positions (starting from 0)
     of variables whose types should be stored when quantifier is analyzed.
   . For type applications patterns:
     it gives the list of positions (starting from 0)
     of type arguments which should be stored when type application is analyzed.
   In other cases, it must be [] (types in other term positions are entirely
     determined by those at those chosen locations) *)
type 'i instruction =
    (* Pop term at top of term stack and check it against the
       given construction. If successful, push the fragment on the term stack
       in the order they are found in the term, and push the types
       references by the ['i] argument to type stack if pertinent. *)
  | Fragment of 'i * construction
    (* Transfer term at top of term stack to the match stack.
       Push its types to type stack if ['i] says so. *)
  | Store of 'i
    (* Analog of [Fragment] for pattern stack. Types never need to be
       stored as they are determined from the case-construction from
       which the pattern comes from. *)
  | FragmentPat of pat_construction
    (* Analog of [Fragment] for type stack, except only the types selected
       by the ['i] arguments are pushed. *)
  | FragmentTy of 'i * ty_construction
    (* Analog of [Store] for types. *)
  | StoreTv
    (* Pop the top of match stack, and match it to the given matching
       variable. If a matching already exists, test for equality. *)
  | Subst of vsymbol
    (* Analog of [Subst] for types. *)
  | SubstTv of tvsymbol
    (* Check that the matching of given variable does not contains any
       bound variable. *)
  | Occurs of vsymbol
    (* Do nothing. Should not occur in normal proof scripts.
       This was introduced to represent the first instruction of an empty
       script, which was pertinent for representing non-deterministic splitting
       of execution. *)
  | Nop

module IL = struct
  type t = int list
  let compare = Pervasives.compare
end
module MIL = Extmap.Make(IL)

(* Note: this module only compare instruction modulo compatibility. *)
module Instr = struct
  type t = int list instruction
  let compare i1 i2 =
    match i1, i2 with
    | Fragment _, Fragment _ -> 0
    | FragmentPat _, FragmentPat _ -> 0
    | FragmentTy _, FragmentTy _ -> 0
    | Store l1, Store l2 -> IL.compare l1 l2
    | StoreTv, StoreTv | Nop, Nop -> 0
    | (Subst vs1, Subst vs2 | Occurs vs1, Occurs vs2) ->
      vs_compare vs1 vs2
    | SubstTv tv1, SubstTv tv2 -> tv_compare tv1 tv2
    | Fragment _, _    -> -1 | _, Fragment _    -> 1
    | Store _, _       -> -1 | _, Store _       -> 1
    | FragmentPat _, _ -> -1 | _, FragmentPat _ -> 1
    | FragmentTy _, _  -> -1 | _, FragmentTy _  -> 1
    | StoreTv, _       -> -1 | _, StoreTv       -> 1
    | Subst _, _       -> -1 | _, Subst _       -> 1
    | SubstTv _, _     -> -1 | _, SubstTv _     -> 1
    | Occurs _, _      -> -1 | _, Occurs _      -> 1
end
module MInstr = Extmap.Make(Instr)

(* Type of a matching script where patterns are identified by 'id
   (the 'id should be comparable, to break ties with the highest-matching
    pattern)
   [highest_id] represent the identifiant of the highest-'id pattern
     that may be matched with this script, [straight_code] the code
     common for all patterns, and [code_branch] a non-deterministic execution
     point. *)
type 'id code_point = {
  highest_id : 'id;
  straight_code : int list instruction list;
  branch : 'id code_branch;
}

(* Represent non-deterministic branching in matching scripts.
   Respectively represents:
   . Stop: no branching, the scripts merely stops normally and accepts.
   . Fork: incompatible branching: propose several scripts which starts
     by incompatible instructions.
   . Switch[...]: compatible branching. The next scripts starts by compatible
     instructions, so only one of them may succeed, and it can be identified
     directly. For the term/types variant, the list of position can represent
     an immediate incompatibility, which is handled immediately by the
     second map level. *)
and 'id code_branch =
  | Stop
  | Fork of 'id code_point MInstr.t
  | Switch of 'id code_point MIL.t MC.t
  | SwitchTy of 'id code_point MIL.t MCty.t
  | SwitchPat of 'id code_point MCpat.t

(* State of matching engine. *)
type 'id matching_state = {
  (* Term stack: represent the parts of the original term
     that have yet to be analyzed.*)
  mutable term_stack : term list;
  (* Match stack: represent the parts of the original term
     that were at the position of a matching variable. *)
  mutable match_stack : term list;
  (* Type stack/type match stack: type version. *)
  mutable ty_stack : ty list;
  mutable ty_match_stack : ty list;
  (* Pat stack: pat version. *)
  mutable pat_stack : pattern list;
  (* type/term match: found matches. *)
  mutable type_match : ty Mtv.t;
  mutable term_match : term Mvs.t;
  (* Binding levels: [bound_levels] identify bound variables
     to integers, which identify the moment they were introduced.
     The levels starts from 0 and are allocated successively,
     using [bind_level]. *)
  mutable bind_level : int;
  mutable bound_levels : int Mvs.t;
  (* Remaining execution script. *)
  code_loc : 'id code_point;
}


(*(* Debug. *)
let pp_tc fmt =
  let (!) s = Format.fprintf fmt s in
  function
  | Crigid vs -> !"R %a" Pretty.print_vs vs
  | Cbound n -> !"B %d" n
  | Cconst t -> !"C %a" Pretty.print_term t
  | Capp ls -> !"A %a" Pretty.print_ls ls
  | Cif -> !"IF"
  | Clet -> !"LET"
  | Ccase n -> !"CASE %d" n
  | Ceps -> !"EPS"
  | Cquant (q,n) -> !"%a %d" Pretty.print_quant q n
  | Cbinop b -> !"%a" (Pretty.print_binop ~asym:false) b
  | Cnot -> !"NOT"
let pp_tyc fmt =
  let (!) s = Format.fprintf fmt s in
  function
  | TyCrigid tv -> !"R %a" Pretty.print_tv tv
  | TyCapp ts -> !"A %a" Pretty.print_ts ts
let pp_pat fmt =
  let (!) s = Format.fprintf fmt s in
  function
  | PatCwild -> !"_"
  | PatCvar -> !"V"
  | PatCapp ls -> !"A %a" Pretty.print_ls ls
  | PatCor -> !"|"
  | PatCas -> !"AS"
let pp_instr fmt =
  let (!) s = Format.fprintf fmt s in
  let (!!) s fmt = Format.fprintf fmt s in
  let pl = Pp.print_list Pp.space !!"%d" in
  function
  | Fragment (l,c) -> !"FT [%a] [%a]" pl l pp_tc c
  | Store l -> !"SVS [%a]" pl l
  | FragmentPat c -> !"FP [%a]" pp_pat c
  | FragmentTy (l,c) -> !"FTY [%a] [%a]" pl l pp_tyc c
  | StoreTv -> !"STV"
  | Subst vs -> !"SuVS %a" Pretty.print_vs vs
  | SubstTv tv -> !"SuTV %a" Pretty.print_tv tv
  | Occurs vs -> !"OCC %a" Pretty.print_vs vs
  | Nop -> !"NOP"
let pp_instrs = Pp.print_list Pp.semi pp_instr

let rec pp_code ipp fmt cp =
  Format.fprintf fmt "Id: %a|" ipp cp.highest_id;
  pp_instrs fmt cp.straight_code;
  pp_branch ipp fmt cp.branch

and pp_branch ipp fmt =
  let pp_code = pp_code ipp in
  let (!) s = Format.fprintf fmt s in
  let (!!) s fmt = Format.fprintf fmt s in
  let pl = Pp.print_list Pp.space !!"%d" in
  let pp_mil fmt m =
    MIL.iter (fun l cp -> !!"[<%a>|%a]" fmt pl l pp_code cp) m in
  function
  | Stop -> !"MATCH";
  | Fork m -> !"FORK[";
    MInstr.iter (fun i cp -> !"[<%a>|%a]" pp_instr i pp_code cp) m;
    !"]"
  | Switch mc -> !"SWITCH";
    MC.iter (fun c mil -> !"[<%a>|FORK[%a]]" pp_tc c pp_mil mil) mc
  | SwitchTy mc -> !"SWITCHTY";
    MCty.iter (fun c mil -> !"[<%a>|FORK[%a]]" pp_tyc c pp_mil mil) mc
  | SwitchPat mc -> !"SWITCHPAT";
    MCpat.iter (fun c cp -> !"[<%a>|%a]" pp_pat c pp_code cp) mc*)










(* Utilities to update matching state. *)
let ms_bind ms vs =
  ms.bound_levels <- Mvs.add vs ms.bind_level ms.bound_levels;
  ms.bind_level <- ms.bind_level + 1
let drop ms f lis locs =
  let rec aux acc cur lim locs = function
    | [] -> assert false
    | el :: lis ->
      if cur = lim
      then let acc = f el :: acc in
        match locs with
        | [] -> acc
        | lim :: q -> aux acc (cur+1) lim q lis
      else aux acc (cur+1) lim locs lis
  in
  match locs with
  | [] -> ()
  | lim :: q -> ms.ty_stack <- aux ms.ty_stack 0 lim q lis
let ms_tyl ms tyl locs = drop ms (fun x -> x) tyl locs
let ms_quant ms vl tm locs =
  ms.term_stack <- tm :: ms.term_stack;
  List.iter (ms_bind ms) vl;
  drop ms (fun vs -> vs.vs_ty) vl locs
let add_dty ms t = function
  | [] -> ()
  | _ -> ms.ty_stack <- (Opt.get_def ty_bool t.t_ty) :: ms.ty_stack

(* Update the matching state by running a single instruction.
   Returns true if successful, false if the instruction fails. *)
let instr ms = function
  | Fragment (l,c) ->
    let t = match ms.term_stack with
      | [] -> assert false
      | x :: q -> ms.term_stack <- q; remove_bp x
    in
    begin match t.t_node, c with
    | Tvar vsm, Crigid vsp when vs_equal vsm vsp ->
      add_dty ms t l; true
    | Tvar vsm, Cbound n ->
      begin match Mvs.find vsm ms.bound_levels with
      | m -> n = m && (add_dty ms t l; true)
      | exception Not_found -> false
      end
    | (Tconst _ | Ttrue | Tfalse), Cconst tp
      when t_equal (t_attr_set Sattr.empty t) (t_attr_set Sattr.empty tp) ->
      add_dty ms t l; true
    | Tapp (lsm,tl), Capp lsp when ls_equal lsm lsp ->
      ms.term_stack <- List.rev_append tl ms.term_stack;
      add_dty ms t l; true
    | Tif (tmb,tmt,tme), Cif ->
      ms.term_stack <- tme :: tmt :: tmb :: ms.term_stack;
      true
    | Tlet (tmd,tmb), Clet ->
      let vsm, tmb = t_open_bound tmb in
      ms_bind ms vsm;
      ms.term_stack <- tmb :: tmd :: ms.term_stack;
      true
    | Tcase (tcs,brl), Ccase n ->
      List.length brl = n && begin
        ms.term_stack <- tcs :: ms.term_stack;
        let pr br =
          let pat, tbr = t_open_branch br in
          ms.term_stack <- tbr :: ms.term_stack;
          ms.pat_stack <- pat :: ms.pat_stack
        in
        List.iter pr brl;
        true
      end
    | Teps tmb, Ceps ->
      let vsm, tmb = t_open_bound tmb in
      ms_bind ms vsm;
      ms.term_stack <- tmb :: ms.term_stack;
      add_dty ms t l; true
    | Tquant (qm,tmq), Cquant (qp,np) when qm = qp ->
      let vl, _, tmq = t_open_quant tmq in
      List.length vl = np && (ms_quant ms vl tmq l; true)
    | Tbinop (bm,tml,tmr), Cbinop bp when bm = bp ->
      ms.term_stack <- tmr :: tml :: ms.term_stack;
      true
    | Tnot tm, Cnot ->
      ms.term_stack <- tm :: ms.term_stack; true
    | _ -> false
    end
  | FragmentPat c ->
    let p = match ms.pat_stack with
      | [] -> assert false
      | x :: q -> ms.pat_stack <- q; x
    in
    begin match p.pat_node, c with
    | Pwild, PatCwild -> true
    | Pvar vs, PatCvar -> ms_bind ms vs; true
    | Papp (lsm,pml), PatCapp lsp when ls_equal lsm lsp ->
      ms.pat_stack <- List.rev_append pml ms.pat_stack; true
    | Por (pm1,pm2), PatCor ->
      ms.pat_stack <- pm2 :: pm1 :: ms.pat_stack; true
    | Pas (pm,vs), PatCas ->
      ms_bind ms vs; ms.pat_stack <- pm :: ms.pat_stack; true
    | _ -> false
    end
  | FragmentTy (l,c) ->
    let ty = match ms.ty_stack with
      | [] -> assert false
      | x :: q -> ms.ty_stack <- q; x
    in
    begin match ty.ty_node, c with
    | Tyvar tvm, TyCrigid tvp when tv_equal tvm tvp -> true
    | Tyapp (tsm,tyl), TyCapp tsp when ts_equal tsm tsp ->
      ms_tyl ms tyl l;
      true
    | _ -> false
    end
  | Store l ->
    let t = match ms.term_stack with
      | [] -> assert false
      | x :: q -> ms.term_stack <- q; remove_bp x
    in
    ms.match_stack <- t :: ms.match_stack; add_dty ms t l; true
  | StoreTv ->
    let ty = match ms.ty_stack with
      | [] -> assert false
      | x :: q -> ms.ty_stack <- q; x
    in
    ms.ty_match_stack <- ty :: ms.ty_match_stack; true
  | Subst vs ->
    let t = match ms.match_stack with
      | [] -> assert false
      | x :: q -> ms.match_stack <- q; x
    in
    let t = match t.t_ty with
      | Some _ -> t
      | None -> t_if t t_bool_true t_bool_false
    in
    begin match Mvs.find vs ms.term_match with
    | t0 -> t_equal_nt_na t t0
    | exception Not_found ->
      ms.term_match <- Mvs.add vs t ms.term_match; true
    end
  | SubstTv tv ->
    let ty = match ms.ty_match_stack with
      | [] -> assert false
      | x :: q -> ms.ty_match_stack <- q; x
    in
    begin match Mtv.find tv ms.type_match with
    | ty0 -> ty_equal ty ty0
    | exception Not_found ->
      ms.type_match <- Mtv.add tv ty ms.type_match; true
    end
  | Occurs vs ->
    let t = Mvs.find vs ms.term_match in
    Mvs.set_disjoint ms.bound_levels (t_vars t)
  | Nop -> true

(* Lifting to instruction sequences. *)
let rec instrs ms = function
  | [] -> true
  | x :: q -> instr ms x && instrs ms q


(* Full execution of a matching script. *)
let run_match (type i) icmp cp mty mv t =
  let origin = {
    term_stack = [t];
    match_stack = [];
    ty_stack = [];
    ty_match_stack = [];
    pat_stack = [];
    type_match = mty;
    term_match = mv;
    bind_level = 0;
    bound_levels = Mvs.empty;
    code_loc = cp
  } in
  let module MS = struct
    let dummy = origin
    type t = i matching_state
    let compare t1 t2 = icmp t2.code_loc.highest_id t1.code_loc.highest_id
  end in
  let module HMS = Pqueue.Make(MS) in
  let h = HMS.create () in
  HMS.insert origin h;
  let rec run () =
    match HMS.extract_min_exn h with
    | ms ->
      if instrs ms ms.code_loc.straight_code
      then
        match ms.code_loc.branch with
        | Stop -> Some (ms.code_loc.highest_id,ms.type_match,ms.term_match)
        | Fork cm ->
          MInstr.iter (fun _ cp -> HMS.insert {ms with code_loc = cp} h) cm;
          run ()
        | Switch mp ->
          let t = match ms.term_stack with
            | [] -> assert false
            | x :: _ -> remove_bp x
          in
          let c = match t.t_node with
            | Tvar vs ->
              begin match Mvs.find vs ms.bound_levels with
              | n -> Cbound n
              | exception Not_found -> Crigid vs
              end
            | (Tconst _ | Ttrue | Tfalse) -> Cconst t
            | Tapp (ls,_) -> Capp ls
            | Tif _ -> Cif
            | Tlet _ -> Clet
            | Tcase (_,tbr) -> Ccase (List.length tbr)
            | Teps _ -> Ceps
            | Tquant (q,tq) ->
              let vl, _, _ = t_open_quant tq in
              Cquant (q,List.length vl)
            | Tbinop (bp,_,_) -> Cbinop bp
            | Tnot _ -> Cnot
          in
          begin match MC.find c mp with
          | mil -> MIL.iter (fun l cp ->
              let ms = {ms with code_loc = cp} in
              if instr ms (Fragment (l,c)) then HMS.insert ms h) mil
          | exception Not_found -> ()
          end;
          run ()
        | SwitchTy mp ->
          let ty = match ms.ty_stack with [] -> assert false | x :: _ -> x in
          let c = match ty.ty_node with
            | Tyvar tv -> TyCrigid tv
            | Tyapp (ts,_) -> TyCapp ts
          in
          begin match MCty.find c mp with
          | mil -> MIL.iter (fun l cp ->
            let ms = {ms with code_loc = cp} in
            if instr ms (FragmentTy (l,c)) then HMS.insert ms h) mil
          | exception Not_found -> ()
          end;
          run ()
        | SwitchPat mp ->
          let p = match ms.pat_stack with [] -> assert false | x :: _ -> x in
          let c = match p.pat_node with
            | Pwild -> PatCwild
            | Papp (ls,_) -> PatCapp ls
            | Por _ -> PatCor
            | Pas _ -> PatCas
            | Pvar _ -> PatCvar
          in
          begin match MCpat.find c mp with
          | cp ->
            if instr ms (FragmentPat c) then HMS.insert {ms with code_loc = cp} h
          | exception Not_found -> ()
          end;
          run ()
      else run ()
    | exception HMS.Empty -> None
  in
  run ()

(* Utilities for joining matching scripts. *)

(* Default instructions to represent switches. *)
let _fragment = Fragment ([],Cif)
let _fragment_ty = FragmentTy ([],TyCapp ts_int)
let _fragment_pat = FragmentPat PatCwild
let id_branch b = match b with
  | Stop -> Nop
  | Fork _ -> assert false
  | Switch _ -> _fragment
  | SwitchTy _ -> _fragment_ty
  | SwitchPat _ -> _fragment_pat

(* Lifting fragmentation instruction as switch maps. *)
let sw_fragment l tc c = MC.singleton tc (MIL.singleton l c)
let sw_fragment_ty l tyc c = MCty.singleton tyc (MIL.singleton l c)
let sw_fragment_pat pc c = MCpat.singleton pc c

(* Join two matching codes as one, matching the reunion of the
   patterns associated to both codes. *)
let join_code_points icmp c1 c2 =
  let (^) c l = { c with straight_code = l } in
  let (><) i c = MInstr.singleton i c in
  let (!!) c = id_branch c.branch><c^[] in
  let rec join c1 c2 =
    let imx = let cmp = icmp c1.highest_id c2.highest_id in
      if cmp < 0 then c2.highest_id else c1.highest_id in
    let rec zip acc s1 s2 =
      let (~+) b =
        { highest_id = imx; straight_code = List.rev acc; branch = b } in
      match s1, s2 with
      | [], [] -> + merge c1 c2
      | [], ((i::q) as s) -> + move_in c1 i q (c2^s)
      | (i::q) as s, [] -> + move_in c2 i q (c1^s)
      | i1 :: q1, i2 :: q2 ->
        let r () = zip (i1::acc) q1 q2 in
        match i1, i2 with
        | Fragment (l1,tc1), Fragment (l2,tc2) ->
          if C.compare tc1 tc2 = 0 && IL.compare l1 l2 = 0
          then r ()
          else + Switch (merge_s (sw_fragment l1 tc1 (c1^q1))
                                 (sw_fragment l2 tc2 (c2^q2)))
        | FragmentTy (l1,tyc1), FragmentTy (l2,tyc2) ->
          if Cty.compare tyc1 tyc2 = 0 && IL.compare l1 l2 = 0
          then r ()
          else + SwitchTy (merge_sty (sw_fragment_ty l1 tyc1 (c1^q1))
                                     (sw_fragment_ty l2 tyc2 (c2^q2)))
        | FragmentPat pc1, FragmentPat pc2 ->
          if Cpat.compare pc1 pc2 = 0
          then r ()
          else + SwitchPat (merge_spat (sw_fragment_pat pc1 (c1^q1))
                                       (sw_fragment_pat pc2 (c2^q2)))
        | Store l1, Store l2 when IL.compare l1 l2 = 0 -> r ()
        | StoreTv, StoreTv | Nop, Nop -> r ()
        | (Subst vs1, Subst vs2 | Occurs vs1, Occurs vs2)
          when vs_equal vs1 vs2 -> r ()
        | SubstTv tv1, SubstTv tv2 when tv_equal tv1 tv2 -> r ()
        | _ -> + Fork (merge_fork (i1><c1^s1) (i2><c2^s2))
    in
    zip [] c1.straight_code c2.straight_code
  and move_in c1 i tl c2 =
    match c1.branch, i with
    | Fork m, _ -> Fork (merge_fork m (i><c2))
    | Switch mp, Fragment (l,tc) ->
      Switch (merge_s mp (sw_fragment l tc (c2^tl)))
    | SwitchTy mp, FragmentTy (l,tyc) ->
      SwitchTy (merge_sty mp (sw_fragment_ty l tyc (c2^tl)))
    | SwitchPat mp, FragmentPat pc ->
      SwitchPat (merge_spat mp (sw_fragment_pat pc (c2^tl)))
    | _, _ ->
      Fork (merge_fork !!c1 (i><c2))
  and merge c1 c2 =
    match c1.branch, c2.branch with
    | Stop, Stop -> Stop
    | Switch m1, Switch m2 -> Switch (merge_s m1 m2)
    | SwitchTy m1, SwitchTy m2 -> SwitchTy (merge_sty m1 m2)
    | SwitchPat m1, SwitchPat m2 -> SwitchPat (merge_spat m1 m2)
    | Fork m1, Fork m2 -> Fork (merge_fork m1 m2)
    | Fork m1, _ -> Fork (merge_fork m1 !!c2)
    | _, Fork m2 -> Fork (merge_fork !!c1 m2)
    | _, _ -> Fork (merge_fork !!c1 !!c2)
  and merge_s m1 m2 = MC.union jn m1 m2
  and merge_sty m1 m2 = MCty.union jn m1 m2
  and merge_spat m1 m2 = MCpat.union jn0 m1 m2
  and merge_fork m1 m2 = MInstr.union jn0 m1 m2
  and jn0 : 'a. 'a -> 'b -> 'b -> 'b option
    = fun _ c1 c2 -> Some (join c1 c2)
  and jn : 'a. 'a -> 'c -> 'c -> 'c option
    = fun _ mi1 mi2 -> Some (MIL.union jn0 mi1 mi2)
  in
  join c1 c2







(* Next: effective compilation of term patterns. *)

(* Specific storage of types for matching compilation:
     graph equipped with an union-find structure to represent
     known identities, derived from the signature of operators.
     (ex: if we perform matching on constructor "identity" of type
      'a -> 'a, then we can derive than the input and output type
      are equal. In particular, it is not necessary to perform checks
      on both)
     We also store whether the structure of a type node has already
       been established by the signature (example: if we match over
       "Nil" of type list 'a, then there is no need to check that
       the type is indeed list later, since it must be by typing)
     The most important function in this module is [collect],
     which collect those informations from a type signature. *)
module TyG = struct

  type ty_vertex = ty_vertex_content ref

  and ty_vertex_content =
    | Link of ty_vertex
    | Root of int * bool * ty_g_node

  and ty_g_node =
    | TyVvar of tvsymbol
    | TyVapp of tysymbol * ty_vertex list

  (* Create a cascade of cells representing a type. *)
  let rec create ty =
    let fresh tyn = ref (Root (0,false,tyn)) in
    match ty.ty_node with
    | Tyvar tv -> fresh (TyVvar tv)
    | Tyapp (ts,tyl) -> fresh (TyVapp (ts,List.map create tyl))

  (* Find in union-find. *)
  let find a = match !a with
    | Link b ->
      let rec finda a b = match !b with
        | Link c ->
          let r = finda b c in a := Link r; r
        | Root _ -> b
      in
      finda a b
    | Root _ -> a

  (* 'unify' the types represented by two cascade of cells,
     in the sense that sub-cells are identified. This function
     suppose that the types were already identified as equals
     by other means (like a typing invariant) *)
  let rec unify a b =
    let a, b = find a, find b in
    if a != b then match !a, !b with
    | Root (ra,ka,na), Root (rb,kb,nb) ->
      if ra < rb then begin
        a := Link b;
        b := Root (rb,ka||kb,nb);
      end else begin
        b := Link a;
        let ra = if ra = rb then ra + 1 else ra in
        a := Root (ra,ka||kb,na);
      end;
      begin match na, nb with
      | TyVapp (_, la), TyVapp (_,lb) -> List.iter2 unify la lb
      | _ -> ()
      end
    | _ -> assert false

  (* Given:
     . [ty] a type
     . [rigid_tv] a collection of type variables that are rigid in
       [ty]'s context, equivalently that should be treated as type symbols
       in the context of [ty]
     . [reference] a partial map from non-rigid type variables
       in [ty]'s context to a "canonical" cell that was matched to
       that variable
     . [a] a specific representation of a type that can match [ty]
       for some extension of [reference]
     mark all the "rigid" cells of a that occurs in ty as known,
       and extends the reference by the cells that occurs in a for
       that variables. In case multiple choices are found for a given
       variable, unify all those choices (including previously present
       mapping if applicable).
  *)
  let rec collect rigid_tv reference ty a =
    let a = find a in
    match ty.ty_node, !a with
    | Tyvar tv, _ when not (Mtv.mem tv rigid_tv) ->
      begin match Mtv.find tv reference with
      | b -> unify b a; reference
      | exception Not_found -> Mtv.add tv a reference
      end
    | Tyvar _, Root (ra,_,na) -> a := Root (ra,true,na); reference
    | Tyapp (_,tyl), Root (ra,_,(TyVapp (_,tyl2) as na)) ->
      a := Root (ra,true,na);
      List.fold_left2 (fun reference ty a ->
        collect rigid_tv reference ty a) reference tyl tyl2
    | _ -> assert false

end



(* Compile a term [tp] as a pattern, for term/type variables not
   occuring in [rigid_tv]/[rigid_vs]. Those lasts are treated as
   if they were logical/type symbols in current context. *)
let compile rigid_tv rigid_vs tp =
  (* [code]: accumulate in reverse order the code
     for matching [tp]. *)
  let code = ref [] in
  let emit i = code := i :: !code in
  (* [ty_roots]: accumulate the type graphs in the order
       they will be found in the matching state
       after purely structural matching on
       the term structure of [tp].
     Also accumulate references to change a posteriori
       [t_code] so that it stores only the needed types. *)
  let ty_roots = ref [] in
  let emitr r tyg = ty_roots := (r,tyg) :: !ty_roots in
  (* [stored_vs]: accumulates the variables in the order
     they will be found in the matching state after
     purely structural matching on
     the term structure of [tp]. *)
  let stored_vs = ref [] in
  (* [potential]: accumulates the bound variables that must be checked
     for absence in the term for each matching variable.
     Accumulation is done with intersection, since after equality
     check, only the variables permitted at all occurences
     may still be there. *)
  let potential = ref Mvs.empty in
  let store_vs vs bnd =
    stored_vs := vs :: !stored_vs;
    potential := match Mvs.find vs !potential with
    | b0 -> Mvs.add vs (Mvs.set_inter b0 bnd) !potential
    | exception Not_found -> Mvs.add vs bnd !potential
  in
  (* [blvl]: accumulates the representative level of a bound
     variable, as it will be accumulated by fragmentation of binding
     constructs. *)
  let blvl = ref 0 in
  let genb () = let l = !blvl in blvl := l + 1; l in
  (* [reg_vs_tyg]: cache the type graphs for variables. *)
  let reg_vs_tyg = ref Mvs.empty in
  let get_tyg vs =
    try Mvs.find vs !reg_vs_tyg with Not_found ->
    let ntyg = TyG.create vs.vs_ty in
    reg_vs_tyg := Mvs.add vs ntyg !reg_vs_tyg;
    if Mvs.mem vs rigid_vs
    then ignore (TyG.collect rigid_tv Mtv.empty vs.vs_ty ntyg);
    ntyg
  in
  (* tyg_bool: known type graph for boolean. Used as the type graph
     for formulas (e.g for prop), which handles the removal of bool/prop
     conversions. *)
  let tyg_bool = TyG.create ty_bool in
  ignore (TyG.collect rigid_tv Mtv.empty ty_bool tyg_bool);
  (* [structure]: accumulates the initial part of the code,
       responsible for matching against the structure of [tp].
       Argument [bnd] stores the level of currently bound variables. *)
  let rec structure bnd tp =
    let tp = remove_bp tp in
    match tp.t_node with
    | Tvar vs ->
      let r = ref false in
      let tyg = get_tyg vs in
      if Mvs.mem vs rigid_vs
      then emit (Fragment ([r],Crigid vs))
      else begin match Mvs.find vs bnd with
       | lvl -> emit (Fragment ([r],Cbound lvl))
       | exception Not_found -> store_vs vs bnd; emit (Store [r])
      end;
      emitr r tyg;
      tyg
    | (Tconst _ | Ttrue | Tfalse) ->
      let r = ref false in
      emit (Fragment ([r],Cconst tp));
      begin match tp.t_ty with
      | None -> tyg_bool
      | Some ty -> let tyg = TyG.create ty in
        emitr r tyg;
        tyg
      end
    | Tapp (ls,tl) ->
      let r = ref false in
      emit (Fragment ([r],Capp ls));
      let tyg, rf = match ls.ls_value with
        | None -> tyg_bool, Mtv.empty
        | Some ty ->
          let tyg = TyG.create (Opt.get tp.t_ty) in
          let rf = TyG.collect Mtv.empty Mtv.empty ty tyg in
          emitr r tyg;
          tyg, rf
      in
      let pr rf tp typ =
        TyG.collect Mtv.empty rf typ (structure bnd tp) in
      let _ = List.fold_left2 pr rf (List.rev tl) (List.rev ls.ls_args) in
      tyg
    | Tif (tpb,tpt,tpe) ->
      emit (Fragment ([],Cif));
      let tyge = structure bnd tpe in
      let tygt = structure bnd tpt in
      TyG.unify tyge tygt;
      TyG.unify tyg_bool (structure bnd tpb);
      tygt
    | Tlet (tpd,tpv) ->
      emit (Fragment ([],Clet));
      let vsp, tpv = t_open_bound tpv in
      let tygv = structure (Mvs.add vsp (genb ()) bnd) tpv in
      let tygd = structure bnd tpd in
      let tyg = get_tyg vsp in
      TyG.unify tygd tyg;
      tygv
    | Tcase (tcs,brl) ->
      emit (Fragment ([],Ccase (List.length brl)));
      let rec pat_structure bnd patp =
        let ptyg = TyG.create patp.pat_ty in
        begin match patp.pat_node with
        | Pwild -> emit (FragmentPat PatCwild); bnd
        | Pvar vsp ->
          emit (FragmentPat PatCvar);
          TyG.unify ptyg (get_tyg vsp);
          Mvs.add vsp (genb ()) bnd
        | Papp (ls,pl) ->
          emit (FragmentPat (PatCapp ls));
          let pr (bnd,rf) pat typ =
            let bnd, ptyg = pat_structure bnd pat in
            bnd, TyG.collect Mtv.empty rf typ ptyg
          in
          let bs = (bnd,Mtv.empty) in
          let (bnd,rf) =
            List.fold_left2 pr bs (List.rev pl) (List.rev ls.ls_args) in
          let _ = TyG.collect Mtv.empty rf (Opt.get ls.ls_value) ptyg in
          bnd
        | Por (p1,p2) ->
          emit (FragmentPat PatCor);
          let bnd, ptyg2 = pat_structure bnd p2 in
          let bnd, ptyg1 = pat_structure bnd p1 in
          TyG.unify ptyg ptyg1;
          TyG.unify ptyg ptyg2;
          bnd
        | Pas (p,vsp) ->
          emit (FragmentPat PatCas);
          let bnd, ptyga = pat_structure (Mvs.add vsp (genb ()) bnd) p in
          TyG.unify ptyg (get_tyg vsp);
          TyG.unify ptyg ptyga;
          bnd
        end, ptyg
      in
      let tyres = ref None in
      let tycs = ref None in
      let pr br =
        let pat, tbr = t_open_branch br in
        let bnd, ptyg = pat_structure bnd pat in
        let tyg = structure bnd tbr in
        begin match !tyres with
        | None -> tyres := Some tyg
        | Some tyg0 -> TyG.unify tyg0 tyg
        end;
        begin match !tycs with
        | None -> tycs := Some ptyg
        | Some tyg0 -> TyG.unify tyg0 ptyg
        end
      in
      List.iter pr (List.rev brl);
      TyG.unify (Opt.get !tycs) (structure bnd tcs);
      Opt.get !tyres
    | Teps tpb ->
      let vsp, tpb = t_open_bound tpb in
      let r = ref false in
      emit (Fragment ([r],Ceps));
      let tyg = get_tyg vsp in
      emitr r tyg;
      TyG.unify tyg_bool (structure (Mvs.add vsp (genb ()) bnd) tpb);
      tyg
    | Tquant (q,tpq) ->
      let vl, _, tpq = t_open_quant tpq in
      let fn vs = let r = ref false in emitr r (get_tyg vs); r in
      let l = List.map fn vl in
      emit (Fragment (l,Cquant (q,List.length l)));
      let bnd = List.fold_left (fun bnd vs ->
          Mvs.add vs (genb ()) bnd) bnd vl in
      TyG.unify tyg_bool (structure bnd tpq);
      tyg_bool
    | Tbinop (bp,t1,t2) ->
      emit (Fragment ([],Cbinop bp));
      TyG.unify tyg_bool (structure bnd t2);
      TyG.unify tyg_bool (structure bnd t1);
      tyg_bool
    | Tnot t -> emit (Fragment ([],Cnot));
      TyG.unify tyg_bool (structure bnd t);
      tyg_bool
  in
  let _ = structure Mvs.empty tp in
  let stored_tv = ref [] in
  (* [process_ty_root]: accumulates (in [code]) the code responsible
       for matching the current type root, if there is any. In that case,
       we assign the root reference a posteriori to signal that the
       type should have been stored by the initial pass.
       As a side-effect, this procedure also mark as known the node it
       matches, so that redundant code is not generated.
       Also accumulates the stored types variables in [stored_tv]. *)
  let process_ty_root (r,tyg) =
    let ty_code = ref [] in
    let emit i = ty_code := i :: !ty_code in
    let stv = ref [] in
    (* [process_tyg]: subroutine of [process_ty_root]
         that accumulates accumulates in the inverse order with
         respect to [process_ty_root].
       It must be done in that order because we can only decide
         whether to emit the fragmenting instruction after processing
         all sub-nodes, whose code occurs later. *)
    let rec process_tyg tyg =
      let a = TyG.find tyg in
      match !a with
      | TyG.Root (rk,k,n) ->
        if not k then a := TyG.Root (rk,true,n);
        begin match n with
        | TyG.TyVvar tv when Mtv.mem tv rigid_tv ->
          not k && (emit (FragmentTy ([],TyCrigid tv)); true)
        | TyG.TyVvar tv ->
          not k && (stv := tv :: !stv; emit StoreTv; true)
        | TyG.TyVapp (ts,tygl) ->
          let pr lis tyg = process_tyg tyg :: lis in
          let lis = List.fold_left pr [] tygl in
          (not k || List.exists (fun b -> b) lis)
          && (emit (FragmentTy (List.rev_map ref lis,TyCapp ts)); true)
        end
      | _ -> assert false
    in
    if process_tyg tyg then begin
      code := List.rev_append !ty_code !code;
      stored_tv := List.rev_append !stv !stored_tv;
      r := true
    end
  in
  (* Generates code for actually matching variables and checking for
     occurrences of bound variables. *)
  List.iter process_ty_root !ty_roots;
  List.iter (fun tv -> emit (SubstTv tv)) !stored_tv;
  List.iter (fun vs -> emit (Subst vs)) !stored_vs;
  Mvs.iter (fun vs bnd ->
    if not (Mvs.is_empty bnd) then emit (Occurs vs)) !potential;
  (* Post-processing of code: replace the list of boolean reference by
     sorted lists of locations for the elements that should be stored. *)
  let rec compress ind = function
    | [] -> []
    | r :: q -> let cq = compress (ind+1) q in
      if !r then ind :: cq else cq
  in
  let compress l = compress 0 l in
  let post_process = function
    | Fragment (l,c) -> Fragment (compress l,c)
    | Store l -> Store (compress l)
    | FragmentTy (l,c) -> FragmentTy (compress l,c)
    | FragmentPat p -> FragmentPat p
    | StoreTv -> StoreTv
    | Subst vs -> Subst vs
    | SubstTv tv -> SubstTv tv
    | Occurs vs -> Occurs vs
    | Nop -> Nop
  in
  List.rev_map post_process !code

let compile id rigid_tv rigid_vs tp =
  { highest_id = id;
    straight_code = compile rigid_tv rigid_vs tp;
    branch = Stop }

(*let matching_debug _ =
  Trans.goal (fun pr t ->
    Format.printf "Called with %a\n" Pretty.print_term t;
    let mty = ref Mtv.empty in
    let mv = ref Mvs.empty in
    let acc = ref None in
    let r = ref 0 in
    let gen () = let u = !r in r := !r + 1; u in
    let add x =
      match !acc with
      | None -> acc := Some x
      | Some y -> acc := Some (join_code_points Pervasives.compare x y)
    in
    let rec agg_term t = match t.t_node with
      | Tbinop (Tand,a,b) -> agg_term a; agg_term b
      | _ -> add (compile (gen ()) Mtv.empty Mvs.empty t)
    in
    let rec unfold_term t = match t.t_node with
      | Tquant (_,tq) -> let vl,_,tq = t_open_quant tq in
        List.iter (fun vs ->
          if Sattr.mem (create_attribute "rigid") vs.vs_name.id_attrs
          then begin mv := Mvs.add vs (t_var vs) !mv;
            mty := Stv.fold (fun tv mty ->
              Mtv.add tv (ty_var tv) mty
            ) (ty_freevars Stv.empty vs.vs_ty) !mty
          end) vl;
        unfold_term tq
      | Tapp (_,[a;b]) | Tbinop (_,a,b) ->
        agg_term a;
        let acc = Opt.get !acc in
        Format.printf "CODE: %a@." (pp_code Pp.int) acc;
        begin match run_match Pervasives.compare acc !mty !mv b with
        | Some (id,mty,mv) ->
          Format.printf "Match rule %d@." id;
          Mtv.iter (fun tv ty -> Format.printf
            "%a -> %a@." Pretty.print_tv tv Pretty.print_ty ty) mty;
          Mvs.iter (fun vs t -> Format.printf
            "%a -> %a@." Pretty.print_vs vs Pretty.print_term t) mv
        | None -> Format.printf "No Match@."
        | exception (Assert_failure (file,line,char)) ->
          Format.printf "fail: %s %d %d@." file line char
        | exception e ->
          Format.printf "%s@." (Printexc.to_string e)
        end
      | _ -> assert false
    in
    unfold_term t;
    [Decl.create_prop_decl Decl.Pgoal pr t]
  )

let () = Trans.register_env_transform "a" matching_debug ~desc:"DEBUG"*)
