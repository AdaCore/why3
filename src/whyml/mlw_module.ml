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

open Stdlib
open Ident
open Ty
open Term
open Theory
open Mlw_ty
open Mlw_ty.T
open Mlw_expr
open Mlw_decl

(*
  module =
    theory +
    namespace +
    program decls (no logic decl here)

  extraction to OCaml
    1. all types
         follow order given by theory, and retrieve program types when necessary
    2. logic decls (no types)
    3. program decls
*)

type type_symbol =
  | PT of itysymbol
  | TS of tysymbol

type prog_symbol =
  | PV of pvsymbol
  | PS of psymbol
  | PL of plsymbol
  | XS of xsymbol
  | LS of lsymbol

type namespace = {
  ns_ts : type_symbol Mstr.t;  (* type symbols *)
  ns_ps : prog_symbol Mstr.t;  (* program symbols *)
  ns_ns : namespace   Mstr.t;  (* inner namespaces *)
}

let empty_ns = {
  ns_ts = Mstr.empty;
  ns_ps = Mstr.empty;
  ns_ns = Mstr.empty;
}

let ns_replace sub chk x vo vn =
  if not chk then vn else
  if sub vo vn then vn else
  raise (ClashSymbol x)

let tsym_sub t1 t2 = match t1,t2 with
  | PT t1, PT t2 -> its_equal t1 t2
  | TS t1, TS t2 -> ts_equal t1 t2
  | _, _ -> false

let psym_sub p1 p2 = match p1,p2 with
  | PV p1, PV p2 -> pv_equal p1 p2
  | PS p1, PS p2 -> ps_equal p1 p2
  | PL p1, PL p2 -> pl_equal p1 p2
  | XS p1, XS p2 -> xs_equal p1 p2
  | LS p1, LS p2 -> ls_equal p1 p2
  (* program symbols may overshadow pure symbols *)
  | LS _, (PV _|PS _|PL _|XS _) -> true
  | _, _ -> false

let rec merge_ns chk ns1 ns2 =
  if ns1 == ns2 then ns1 else
  let join sub x n o = Some (ns_replace sub chk x o n) in
  let ns_union sub m1 m2 =
    if m1 == m2 then m1 else Mstr.union (join sub) m1 m2 in
  let fusion _ ns1 ns2 = Some (merge_ns chk ns1 ns2) in
  { ns_ts = ns_union tsym_sub ns1.ns_ts ns2.ns_ts;
    ns_ps = ns_union psym_sub ns1.ns_ps ns2.ns_ps;
    ns_ns = Mstr.union fusion ns1.ns_ns ns2.ns_ns; }

let add_ns chk x ns m = Mstr.change (function
  | Some os -> Some (merge_ns chk ns os)
  | None    -> Some ns) x m

let ns_add sub chk x vn m = Mstr.change (function
  | Some vo -> Some (ns_replace sub chk x vo vn)
  | None    -> Some vn) x m

let add_ts chk x ts ns = { ns with ns_ts = ns_add tsym_sub chk x ts ns.ns_ts }
let add_ps chk x pf ns = { ns with ns_ps = ns_add psym_sub chk x pf ns.ns_ps }
let add_ns chk x nn ns = { ns with ns_ns = add_ns          chk x nn ns.ns_ns }

let rec convert_pure_ns ns =
  { ns_ts = Mstr.map (fun ts -> TS ts) ns.Theory.ns_ts;
    ns_ps = Mstr.map (fun ls -> LS ls) ns.Theory.ns_ls;
    ns_ns = Mstr.map convert_pure_ns ns.Theory.ns_ns; }

let rec ns_find get_map ns = function
  | []   -> assert false
  | [a]  -> Mstr.find a (get_map ns)
  | a::l -> ns_find get_map (Mstr.find a ns.ns_ns) l

let ns_find_type_symbol = ns_find (fun ns -> ns.ns_ts)
let ns_find_prog_symbol = ns_find (fun ns -> ns.ns_ps)
let ns_find_ns          = ns_find (fun ns -> ns.ns_ns)

let ns_find_its ns s = match ns_find_type_symbol ns s with
  | PT its -> its | _ -> raise Not_found

let ns_find_ts ns s = match ns_find_type_symbol ns s with
  | TS ts -> ts | _ -> raise Not_found

let ns_find_pv ns s = match ns_find_prog_symbol ns s with
  | PV pv -> pv | _ -> raise Not_found

let ns_find_ps ns s = match ns_find_prog_symbol ns s with
  | PS ps -> ps | _ -> raise Not_found

let ns_find_pl ns s = match ns_find_prog_symbol ns s with
  | PL pl -> pl | _ -> raise Not_found

let ns_find_xs ns s = match ns_find_prog_symbol ns s with
  | XS xs -> xs | _ -> raise Not_found

let ns_find_ls ns s = match ns_find_prog_symbol ns s with
  | LS ls -> ls | _ -> raise Not_found

(** Module *)

type modul = {
  mod_theory: theory;			(* pure theory *)
  mod_decls : pdecl list;		(* module declarations *)
  mod_export: namespace;		(* exported namespace *)
  mod_known : known_map;		(* known identifiers *)
  mod_local : Sid.t;			(* locally declared idents *)
  mod_used  : Sid.t;			(* used modules *)
}

(** Module under construction *)

type module_uc = {
  muc_theory : theory_uc;
  muc_name   : string;
  muc_path   : string list;
  muc_decls  : pdecl list;
  muc_prefix : string list;
  muc_import : namespace list;
  muc_export : namespace list;
  muc_known  : known_map;
  muc_local  : Sid.t;
  muc_used   : Sid.t;
  muc_env    : Env.env option;
}
(* FIXME? We wouldn't need to store muc_name, muc_path,
   and muc_prefix if theory_uc was exported *)

let empty_module env n p = {
  muc_theory = create_theory ~path:p n;
  muc_name   = n.Ident.pre_name;
  muc_path   = p;
  muc_decls  = [];
  muc_prefix = [];
  muc_import = [empty_ns];
  muc_export = [empty_ns];
  muc_known  = Mid.empty;
  muc_local  = Sid.empty;
  muc_used   = Sid.empty;
  muc_env    = env;
}

let close_module, restore_module =
  let h = Hid.create 17 in
  (fun uc ->
     let th = close_theory uc.muc_theory in (* catches errors *)
     let m = { mod_theory = th;
               mod_decls  = List.rev uc.muc_decls;
               mod_export = List.hd uc.muc_export;
               mod_known  = uc.muc_known;
               mod_local  = uc.muc_local;
               mod_used   = uc.muc_used; } in
     Hid.add h th.th_name m;
     m),
  (fun th -> Hid.find h th.th_name)

let get_theory uc = uc.muc_theory
let get_namespace uc = List.hd uc.muc_import
let get_known uc = uc.muc_known

let open_scope uc s = match uc.muc_import with
  | ns :: _ -> { uc with
      muc_theory = Theory.open_scope uc.muc_theory s;
      muc_prefix =        s :: uc.muc_prefix;
      muc_import =       ns :: uc.muc_import;
      muc_export = empty_ns :: uc.muc_export; }
  | [] -> assert false

let close_scope uc import =
  let th = Theory.close_scope uc.muc_theory import in (* catches errors *)
  match uc.muc_prefix, uc.muc_import, uc.muc_export with
  | s :: prf, _ :: i1 :: sti, e0 :: e1 :: ste ->
      let i1 = if import then merge_ns false e0 i1 else i1 in
      let _  = if import then merge_ns true  e0 e1 else e1 in
      let i1 = add_ns false s e0 i1 in
      let e1 = add_ns true  s e0 e1 in
      { uc with
	  muc_theory = th;
          muc_prefix = prf;
	  muc_import = i1 :: sti;
	  muc_export = e1 :: ste; }
  | _ ->
      assert false

(** Use *)

let add_to_module uc th ns =
  match uc.muc_import, uc.muc_export with
  | i0 :: sti, e0 :: ste -> { uc with
      muc_theory = th;
      muc_import = merge_ns false ns i0 :: sti;
      muc_export = merge_ns true  ns e0 :: ste; }
  | _ -> assert false

let use_export uc m =
  let mth = m.mod_theory in
  let id = mth.th_name in
  let uc =
    if Sid.mem id uc.muc_used then uc else { uc with
      muc_known = merge_known uc.muc_known m.mod_known;
      muc_used  = Sid.add id uc.muc_used } in
  let th = Theory.use_export uc.muc_theory mth in
  add_to_module uc th m.mod_export

(** Logic decls *)

let add_to_theory f uc x = { uc with muc_theory = f uc.muc_theory x }

let store_path, store_module, restore_path =
  let id_to_path = Wid.create 17 in
  let store_path uc path id =
    (* this symbol already belongs to some theory *)
    if Wid.mem id_to_path id then () else
    let prefix = List.rev (id.id_string :: path @ uc.muc_prefix) in
    Wid.set id_to_path id (uc.muc_path, uc.muc_name, prefix)
  in
  let store_module m =
    let id = m.mod_theory.th_name in
    (* this symbol is already a module *)
    if Wid.mem id_to_path id then () else
    Wid.set id_to_path id (m.mod_theory.th_path, id.id_string, []) in
  let restore_path id = Wid.find id_to_path id in
  store_path, store_module, restore_path

let close_module uc =
  let m = close_module uc in
  store_module m;
  m

let add_symbol add id v uc =
  store_path uc [] id;
  match uc.muc_import, uc.muc_export with
  | i0 :: sti, e0 :: ste -> { uc with
      muc_import = add false id.id_string v i0 :: sti;
      muc_export = add true  id.id_string v e0 :: ste }
  | _ -> assert false

let add_decl uc d =
  let add_ts uc ts = add_symbol add_ts ts.ts_name (TS ts) uc in
  let add_ls uc ls = add_symbol add_ps ls.ls_name (LS ls) uc in
  let add_pj uc pj = Opt.fold add_ls uc pj in
  let add_cs uc (cs,pjl) = List.fold_left add_pj (add_ls uc cs) pjl in
  let add_data uc (ts,csl) = List.fold_left add_cs (add_ts uc ts) csl in
  let add_logic uc (ls,_) = add_ls uc ls in
  let uc = match d.Decl.d_node with
    | Decl.Dtype ts -> add_ts uc ts
    | Decl.Ddata dl -> List.fold_left add_data uc dl
    | Decl.Dparam ls -> add_ls uc ls
    | Decl.Dlogic dl -> List.fold_left add_logic uc dl
    | Decl.Dind (_,dl) -> List.fold_left add_logic uc dl
    | Decl.Dprop _ -> uc
  in
  add_to_theory (Theory.add_decl ?warn:None) uc d

let use_export_theory uc th =
  let nth = Theory.use_export uc.muc_theory th in
  let nns = convert_pure_ns th.th_export in
  add_to_module uc nth nns

let clone_export_theory uc th inst =
  let nth = Theory.clone_export uc.muc_theory th inst in
  let sm = match Theory.get_rev_decls nth with
    | { td_node = Clone (_,sm) } :: _ -> sm
    | _ -> assert false in
  let g_ts _ ts = not (Mts.mem ts inst.inst_ts) in
  let g_ls _ ls = not (Mls.mem ls inst.inst_ls) in
  let f_ts p ts =
    try let ts = Mts.find ts sm.sm_ts in store_path uc p ts.ts_name; TS ts
    with Not_found -> TS ts in
  let f_ls p ls =
    try let ls = Mls.find ls sm.sm_ls in store_path uc p ls.ls_name; LS ls
    with Not_found -> LS ls in
  let rec f_ns p ns = {
    ns_ts = Mstr.map (f_ts p) (Mstr.filter g_ts ns.Theory.ns_ts);
    ns_ps = Mstr.map (f_ls p) (Mstr.filter g_ls ns.Theory.ns_ls);
    ns_ns = Mstr.mapi (fun n -> f_ns (n::p)) ns.Theory.ns_ns; }
  in
  add_to_module uc nth (f_ns [] th.th_export)

let add_meta uc m al =
  { uc with muc_theory = Theory.add_meta uc.muc_theory m al }

(** Program decls *)

let add_type uc its =
  add_symbol add_ts its.its_ts.ts_name (PT its) uc

let add_data uc (its,csl,_) =
  let add_pl uc pl = add_symbol add_ps pl.pl_ls.ls_name (PL pl) uc in
  let add_pj uc pj = Opt.fold add_pl uc pj in
  let add_cs uc (cs,pjl) = List.fold_left add_pj (add_pl uc cs) pjl in
  let uc = add_symbol add_ts its.its_ts.ts_name (PT its) uc in
  if its.its_abst then uc else List.fold_left add_cs uc csl

let add_let uc = function
  | LetV pv -> add_symbol add_ps pv.pv_vs.vs_name (PV pv) uc
  | LetA ps -> add_symbol add_ps ps.ps_name (PS ps) uc

let add_rec uc { fun_ps = ps } =
  add_symbol add_ps ps.ps_name (PS ps) uc

let add_exn uc xs =
  add_symbol add_ps xs.xs_name (XS xs) uc

let pdecl_ns uc d = match d.pd_node with
  | PDtype its -> add_type uc its
  | PDdata tdl -> List.fold_left add_data uc tdl
  | PDval lv | PDlet { let_sym = lv } -> add_let uc lv
  | PDrec fdl -> List.fold_left add_rec uc fdl
  | PDexn xs -> add_exn uc xs

let pdecl_vc ~wp env km th d = match d.pd_node with
  | PDtype _ | PDdata _ | PDexn _ -> th
  | PDval lv -> Mlw_wp.wp_val ~wp env km th lv
  | PDlet ld -> Mlw_wp.wp_let ~wp env km th ld
  | PDrec rd -> Mlw_wp.wp_rec ~wp env km th rd

let pdecl_vc ~wp uc d = match uc.muc_env with
  | Some env -> add_to_theory (pdecl_vc ~wp env uc.muc_known) uc d
  | None -> uc

let pure_data_decl tdl =
  let proj pj = Opt.map (fun pls -> pls.pl_ls) pj in
  let cons (pls,pjl) = pls.pl_ls, List.map proj pjl in
  let defn (its,csl,_) = its.its_ts, List.map cons csl in
  List.map defn tdl

let pdecl_pure th d = match d.pd_node with
  | PDtype its -> Theory.add_ty_decl th its.its_ts
  | PDdata tdl -> Theory.add_data_decl th (pure_data_decl tdl)
  | PDval _ | PDlet _ | PDrec _ | PDexn _ -> th

let add_pdecl ~wp uc d =
  let uc = { uc with
    muc_decls = d :: uc.muc_decls;
    muc_known = known_add_decl (Theory.get_known uc.muc_theory) uc.muc_known d;
    muc_local = Sid.union uc.muc_local d.pd_news }
  in
  let uc = pdecl_ns uc d in
  let uc = pdecl_vc ~wp uc d in
  let uc = add_to_theory pdecl_pure uc d in
  uc

(* we can safely add a new type invariant as long as
   the type was introduced in the last program decl,
   and no let, rec or val could see it *)

exception TooLateInvariant

let add_invariant uc its p =
  let rec add = function
    | d :: dl when Mid.mem its.its_ts.ts_name d.pd_news ->
        let d = Mlw_decl.add_invariant d its p in d, d :: dl
    | { pd_node = PDtype _ } as d :: dl ->
        let nd, dl = add dl in nd, d :: dl
    | _ -> raise TooLateInvariant in
  let decl, decls = add uc.muc_decls in
  let kn = Mid.map (Util.const decl) decl.pd_news in
  let kn = Mid.set_union kn uc.muc_known in
  { uc with muc_decls = decls; muc_known = kn }

(* create module *)

let xs_exit = create_xsymbol (id_fresh "%Exit") ity_unit

let mod_prelude =
  let pd_exit = create_exn_decl xs_exit in
  let uc = empty_module None (id_fresh "Prelude") ["why3";"Prelude"] in
  let uc = add_pdecl ~wp:false uc pd_exit in
  close_module uc

let create_module env ?(path=[]) n =
  let m = empty_module (Some env) n path in
  let m = use_export_theory m builtin_theory in
  let m = use_export_theory m bool_theory in
  let m = use_export_theory m unit_theory in
  let m = use_export m mod_prelude in
  m

(** WhyML language *)

type mlw_file = modul Mstr.t * theory Mstr.t

let mlw_language =
  (Env.register_language Env.base_language snd : mlw_file Env.language)

let () = Env.add_builtin mlw_language (function
  | [s] when s = mod_prelude.mod_theory.th_name.id_string ->
      Mstr.singleton s mod_prelude,
      Mstr.singleton s mod_prelude.mod_theory
  | _ -> raise Not_found)

let () = Env.add_builtin Env.base_language (function
  | [s] when s = Mlw_wp.mark_theory.th_name.id_string ->
      Mstr.singleton s Mlw_wp.mark_theory
  | _ -> raise Not_found)

exception ModuleNotFound of Env.pathname * string
exception ModuleOrTheoryNotFound of Env.pathname * string

type module_or_theory = Module of modul | Theory of theory

let read_module env path s =
  let path = if path = [] then ["why3"; s] else path in
  let mm, _ = Env.read_library mlw_language env path in
  Mstr.find_exn (ModuleNotFound (path,s)) s mm

let read_module_or_theory env path s =
  let path = if path = [] then ["why3"; s] else path in
  try
    let mm, mt = Env.read_library mlw_language env path in
    try Module (Mstr.find s mm) with Not_found ->
    try Theory (Mstr.find s mt) with Not_found ->
      raise (ModuleOrTheoryNotFound (path,s))
  with Env.InvalidFormat _ | Env.LibraryNotFound _ ->
    let mt = Env.read_library Env.base_language env path in
    try Theory (Mstr.find s mt) with Not_found ->
      raise (ModuleOrTheoryNotFound (path,s))

let print_path fmt sl =
  Pp.print_list (Pp.constant_string ".") Format.pp_print_string fmt sl

let () = Exn_printer.register (fun fmt e -> match e with
  | ModuleNotFound (sl,s) -> Format.fprintf fmt
      "Module %s not found in library %a" s print_path sl
  | ModuleOrTheoryNotFound (sl,s) -> Format.fprintf fmt
      "Module/theory %s not found in library %a" s print_path sl
  | TooLateInvariant -> Format.fprintf fmt
      "Cannot add a type invariant after another program declaration"
  | _ -> raise e)

(** Clone *)

type mod_inst = {
  inst_pv : pvsymbol Mpv.t;
  inst_ps : psymbol Mps.t;
}

let clone_export uc m minst inst =
  let nth = Theory.clone_export uc.muc_theory m.mod_theory inst in
  let sm = match Theory.get_rev_decls nth with
    | { td_node = Clone (_,sm) } :: _ -> sm
    | _ -> assert false in
  let psm = pl_clone sm in
  let conv_its its = Mits.find_def its its psm.sm_its in
  let conv_ts ts = Mts.find_def ts ts sm.Theory.sm_ts in
  let conv_ls ls = Mls.find_def ls ls sm.Theory.sm_ls in
  let extras = Mid.set_diff m.mod_known m.mod_local in
  let regh = Hreg.create 5 in
  let rec conv_ity ity = match ity.ity_node with
    | Ityapp (s,tl,rl) ->
        ity_app (conv_its s) (List.map conv_ity tl) (List.map conv_reg rl)
    | Itypur (s,tl) -> ity_pur (conv_ts s) (List.map conv_ity tl)
    | Ityvar _ -> ity
  and conv_reg r =
    if Mid.mem r.reg_name extras then r else
    try Hreg.find regh r with Not_found ->
    let nr = create_region (id_clone r.reg_name) (conv_ity r.reg_ity) in
    Hreg.replace regh r nr;
    nr in
  let conv_pv pv =
    create_pvsymbol (id_clone pv.pv_vs.vs_name)
      ~ghost:pv.pv_ghost (conv_ity pv.pv_ity) in
  let psh = Hid.create 3 in
  let conv_xs xs = try match Hid.find psh xs.xs_name with
    | XS xs -> xs | _ -> assert false with Not_found -> xs in
  let conv_eff mv eff =
    let e = eff_empty in
    let conv ghost r e = eff_write ~ghost e (conv_reg r) in
    let e = Sreg.fold (conv false) eff.eff_writes e in
    let e = Sreg.fold (conv true)  eff.eff_ghostw e in
    let conv ghost xs e = eff_raise ~ghost e (conv_xs xs) in
    let e = Sexn.fold (conv false) eff.eff_raises e in
    let e = Sexn.fold (conv true)  eff.eff_ghostx e in
    let conv r u e = match u with
      | Some u -> eff_refresh e (conv_reg r) (conv_reg u)
      | None   -> eff_reset e (conv_reg r) in
    let e = Mreg.fold conv eff.eff_resets e in
    let tvs = Mvs.fold (fun _ vs s -> ty_freevars s vs.vs_ty) mv Stv.empty in
    let tvs = Stv.inter tvs eff.eff_compar in
    Stv.fold (fun tv e -> eff_compare e tv) tvs e in
  let conv_term mv t = t_gen_map (ty_s_map conv_ts) conv_ls mv t in
  let addx mv xs t q = Mexn.add (conv_xs xs) (conv_term mv t) q in
  let conv_vari mv (t,r) = conv_term mv t, Opt.map conv_ls r in
  let conv_spec mv c = {
    c_pre     = conv_term mv c.c_pre;
    c_post    = conv_term mv c.c_post;
    c_xpost   = Mexn.fold (addx mv) c.c_xpost Mexn.empty;
    c_effect  = conv_eff mv c.c_effect;
    c_variant = List.map (conv_vari mv) c.c_variant;
    c_letrec  = 0; } in
  let rec conv_aty mv a =
    let args = List.map conv_pv a.aty_args in
    let add mv pv npv = Mvs.add pv.pv_vs npv.pv_vs mv in
    let mv = List.fold_left2 add mv a.aty_args args in
    let spec = conv_spec mv a.aty_spec in
    let vty = match a.aty_result with
      | VTarrow a -> VTarrow (conv_aty mv a)
      | VTvalue v -> VTvalue (conv_ity v) in
    vty_arrow args ~spec vty in
  let mvs = ref (Mvs.singleton pv_old.pv_vs pv_old.pv_vs) in
  let add_pdecl uc d = { uc with
    muc_decls = d :: uc.muc_decls;
    muc_known = known_add_decl (Theory.get_known nth) uc.muc_known d;
    muc_local = Sid.union uc.muc_local d.pd_news } in
  let rnth = ref nth in
  let add_pd uc pd = match pd.pd_node with
    | PDtype its ->
        add_pdecl uc (create_ty_decl (conv_its its))
    | PDdata _ ->
        add_pdecl uc (clone_data_decl psm pd)
    | PDexn xs ->
        let ity = conv_ity xs.xs_ity in
        let nxs = create_xsymbol (id_clone xs.xs_name) ity in
        Hid.add psh xs.xs_name (XS nxs);
        add_pdecl uc (create_exn_decl nxs)
    | PDlet _ ->
        Loc.errorm "Cannot clone top-level computations"
        (* TODO? Should we clone the defining expression and
           let it participate in the top-level module WP?
           If not, what do we do about its effects? *)
    | PDval (LetV pv) when Mpv.mem pv minst.inst_pv ->
        (* TODO: ensure that we do not introduce undetected aliases.
           This may happen when the cloned module uses a base module
           with a global variable, and then we instantiate another
           global variable with it. *)
          Loc.errorm "Cannot instantiate top-level variables"
    | PDval (LetV pv) ->
        let npv = conv_pv pv in
        Hid.add psh pv.pv_vs.vs_name (PV npv);
        mvs := Mvs.add pv.pv_vs npv.pv_vs !mvs;
        add_pdecl uc (create_val_decl (LetV npv))
    | PDval (LetA ps) when Mps.mem ps minst.inst_ps ->
        let nps = Mps.find ps minst.inst_ps in
        let aty = conv_aty !mvs ps.ps_aty in
        let app = match aty.aty_result, nps.ps_aty.aty_result with
          | VTvalue res, VTvalue _ ->
              let argl = List.map (fun pv -> pv.pv_ity) aty.aty_args in
              e_app (e_arrow nps argl res) (List.map e_value aty.aty_args)
          | _ -> Loc.errorm "Program@ symbol@ instantiation@ does@ not@ \
              support@ specifications@ for@ partially@ applied@ symbols" in
        let spec = { aty.aty_spec with c_variant = []; c_letrec = 0 } in
        let lam = { l_args = aty.aty_args; l_expr = app; l_spec = spec } in
        let (lp,md,nm) = restore_path ps.ps_name in
        let sl = String.concat " " in
        let nm = sl lp ^ "  " ^ md ^ "  " ^ sl nm in
        let id = id_derive nm ps.ps_name in
        let fd = create_fun_defn id lam in
        if fd.fun_ps.ps_ghost && not ps.ps_ghost then Loc.errorm
          "Program@ symbol@ instantiation@ must@ preserve@ ghostness";
        let oeff = aty.aty_spec.c_effect in
        let neff = fd.fun_ps.ps_aty.aty_spec.c_effect in
        if not (Sreg.subset neff.eff_writes oeff.eff_writes &&
                Sexn.subset neff.eff_raises oeff.eff_raises &&
                Sreg.subset neff.eff_ghostw oeff.eff_ghostw &&
                Sexn.subset neff.eff_ghostx oeff.eff_ghostx &&
                Mreg.submap (fun _ -> Opt.equal reg_equal)
                  neff.eff_resets oeff.eff_resets &&
                Stv.subset neff.eff_compar oeff.eff_compar &&
                (oeff.eff_diverg || not neff.eff_diverg)) then
          Loc.errorm "Extra effects in program symbol instantiation";
        if not (Spv.subset nps.ps_pvset (aty_pvset aty)) then
          Loc.errorm "Extra hidden state in program symbol instantiation";
        begin match uc.muc_env with
        | Some env ->
            rnth := Mlw_wp.wp_rec ~wp:true env uc.muc_known !rnth [fd]
        | None -> ()
        end;
        Hid.add psh ps.ps_name (PS nps);
        uc
    | PDval (LetA { ps_name = id; ps_ghost = ghost; ps_aty = aty }) ->
        let aty = conv_aty !mvs aty in
        let nps = Mlw_expr.create_psymbol (id_clone id) ~ghost aty in
        Hid.add psh id (PS nps);
        add_pdecl uc (create_val_decl (LetA nps))
    | PDrec fdl ->
        let conv_fd uc { fun_ps = ps } =
          if Mps.mem ps minst.inst_ps then
            raise (Theory.CannotInstantiate ps.ps_name);
          let id = id_clone ps.ps_name in
          let aty = conv_aty !mvs ps.ps_aty in
          let vari = Spv.fold (fun pv l ->
            (t_var (Mvs.find_def pv.pv_vs pv.pv_vs !mvs), None)::l)
            ps.ps_pvset [] in
          (* we save all external pvsymbols to preserve the effects *)
          let spec = { aty.aty_spec with c_variant = vari } in
          let aty = vty_arrow ~spec aty.aty_args aty.aty_result in
          let nps = Mlw_expr.create_psymbol id ~ghost:ps.ps_ghost aty in
          Hid.add psh ps.ps_name (PS nps);
          add_pdecl uc (create_val_decl (LetA nps)) in
        List.fold_left conv_fd uc fdl
  in
  let uc = { uc with
    muc_known = merge_known uc.muc_known extras;
    muc_used = Sid.union uc.muc_used m.mod_used } in
  let uc = List.fold_left add_pd uc m.mod_decls in
  let nth = !rnth in
  let g_ts _ = function
    | TS ts -> not (Mts.mem ts inst.inst_ts)
    | _ -> true in
  let g_ps _ = function
    | LS ls -> not (Mls.mem ls inst.inst_ls)
    | PV pv -> not (Mpv.mem pv minst.inst_pv)
    | PS ps -> not (Mps.mem ps minst.inst_ps)
    | _ -> true in
  let f_ts p = function
    | TS ts ->
        begin try let ts = Mts.find ts sm.Theory.sm_ts in
          store_path uc p ts.ts_name; TS ts
        with Not_found -> TS ts end
    | PT pt ->
        begin try let pt = Mits.find pt psm.sm_its in
          store_path uc p pt.its_ts.ts_name; PT pt
        with Not_found -> PT pt end in
  let find_prs p def id =
    try let s = Hid.find psh id in match s with
      | PV pv -> store_path uc p pv.pv_vs.vs_name; s
      | PS ps -> store_path uc p ps.ps_name; s
      | XS xs -> store_path uc p xs.xs_name; s
      | LS _ | PL _ -> assert false
    with Not_found -> def in
  let f_ps p prs = match prs with
    | LS ls ->
        begin try let ls = Mls.find ls sm.Theory.sm_ls in
          store_path uc p ls.ls_name; LS ls
        with Not_found -> LS ls end
    | PL pl ->
        begin try let pl = Mls.find pl.pl_ls psm.sm_pls in
          store_path uc p pl.pl_ls.ls_name; PL pl
        with Not_found -> PL pl end
    | PV pv -> find_prs p prs pv.pv_vs.vs_name
    | PS ps -> find_prs p prs ps.ps_name
    | XS xs -> find_prs p prs xs.xs_name in
  let rec f_ns p ns = {
    ns_ts = Mstr.map (f_ts p) (Mstr.filter g_ts ns.ns_ts);
    ns_ps = Mstr.map (f_ps p) (Mstr.filter g_ps ns.ns_ps);
    ns_ns = Mstr.mapi (fun n -> f_ns (n::p)) ns.ns_ns; } in
  add_to_module uc nth (f_ns [] m.mod_export)
