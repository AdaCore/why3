(* open Why3 *)
open Term
open Ident
open Ty
open Theory
open Decl
open Task

(* type base = *)
(*   (* NULL ? *) *)
(*   | Absolute *)
(* (* Address of a variable taken with & or memory range allocated with malloc
   *) *)
(* | Address of int *)

(* type loc = Defined of { base_addr : base; offset : int } | Undefined of
   term *)

type loc =
  | Defined
  | Undefined of term

type update =
  | Empty
  | Singleton of loc * int
  | Union of update * update

type modif = {
  (* The prsymbol of the axiom introducing the assign clause *)
  pr : prsymbol;
  mp : term;
  update : update;
  prev_mc : term;
  prev_mp : term;
  loc_set : term;
}

(* Info about a memory content (a state of the memory at one point in time *)
type mc_info = {
  (* The previous memory content upon which this one is derived *)
  modif : modif option;
}

type loc_info = {
  (* The values of the loc at different memory states *)
  mc_values : int option Mterm.t;
  (* (lo1,hi1,lo2,hi2) means \separated(ls1[lo1..hi1],ls2[lo2..hi2]) *)
  separations : (int * int * int * int) list Mterm.t;
}

let default_info = { mc_values = Mterm.empty; separations = Mterm.empty }

type info = {
  mcs_info : mc_info Mterm.t;
  locs_info : loc_info Mterm.t;
}

type symbols = {
  (* loc_ts : tysymbol; *)
  (* mc_ts : tysymbol; *)
  initialized : lsymbol;
  separated : lsymbol;
  assign : lsymbol;
  empty : lsymbol;
  singleton : lsymbol;
  union : lsymbol;
  load_int32 : lsymbol;
  bv_add : lsymbol;
  bv_sub : lsymbol;
  bv_mul : lsymbol;
  bv_to_logic_signed : lsymbol;
  bv32_ts : tysymbol;
}

let symbols = ref None
let ( !! ) s = Opt.get !s
let zero = t_const (Constant.int_const_of_int 0) ty_int
let four = t_const (Constant.int_const_of_int 4) ty_int

let ls_equal ls1 ls2 =
  match ls1.ls_name.id_loc with
  | Some loc1 -> (
    match ls2.ls_name.id_loc with
    | Some loc2 -> Loc.equal loc1 loc2
    | None -> false)
  | None -> false

(* Returns a list of pairs (loc, mc). Each pair corresponds to a loc of which we
   want to know the value in mc *)
let rec get_locs t =
  match t.t_node with
  | Tcase (t1, bl) ->
    let l = get_locs t1 in
    List.fold_left
      (fun l b ->
        let _, t = t_open_branch b in
        l @ get_locs t)
      l bl
  | Teps b ->
    let _, f = t_open_bound b in
    get_locs f
  | Tquant (_, b) ->
    let _, _, t = t_open_quant b in
    get_locs t
  | Tif (t1, t2, t3) -> get_locs t1 @ get_locs t2 @ get_locs t3
  | Tbinop (_, t1, t2) -> get_locs t1 @ get_locs t2
  | Tnot t -> get_locs t
  | Tapp (ls, [ mc; mp; loc ]) when ls_equal ls !!symbols.load_int32 ->
    [ (ls, mc, mp, loc) ]
  | Tapp (_, tl) -> List.fold_left (fun l t -> l @ get_locs t) [] tl
  | _ -> []

let rec get_initialized t =
  match t.t_node with
  | Tbinop (Tand, t1, t2) -> get_initialized t1 @ get_initialized t2
  | Tapp (ls, [ mc; loc; lo; hi ]) when ls_equal ls !!symbols.initialized ->
    [ (ls, mc, loc, lo, hi) ]
  (* | Tquant (_, b) -> TODO *)
  | _ -> []

let get_loc_info info t =
  try Mterm.find t info.locs_info with
  | Not_found -> { mc_values = Mterm.empty; separations = Mterm.empty }

exception NoCst

let rec int_of_term t =
  match t.t_node with
  | Tconst (ConstInt i) -> BigInt.to_int i.il_int
  | Tconst (ConstReal _) ->
    Format.printf "Unsupported real cst %a@." Pretty.print_term t;
    raise NoCst
  | Tapp (ls, [ t1; t2 ]) ->
    if ls_equal !!symbols.bv_add ls then
      int_of_term t1 + int_of_term t2
    else if ls_equal !!symbols.bv_mul ls then
      int_of_term t1 * int_of_term t2
    else if ls_equal !!symbols.bv_sub ls then
      int_of_term t1 - int_of_term t2
    else
      let _ =
        Format.printf "Bad term '%a', need a constant@." Pretty.print_term t
      in
      raise NoCst
  | Tapp (ls, [ t ]) when ls_equal !!symbols.bv_to_logic_signed ls ->
    int_of_term t
  | _ ->
    Format.printf "Bad term '%a', need a constant@." Pretty.print_term t;
    raise NoCst

let add_separated info t1 lo1 hi1 t2 lo2 hi2 =
  try
    let lo1, hi1 = (int_of_term lo1, int_of_term hi1) in
    let lo2, hi2 = (int_of_term lo2, int_of_term hi2) in
    let t1_info = get_loc_info info t1 in
    let t2_info = get_loc_info info t2 in
    let t1_info =
      let l =
        try (lo1, hi1, lo2, hi2) :: Mterm.find t2 t1_info.separations with
        | Not_found -> [ (lo1, hi1, lo2, hi2) ]
      in
      { t1_info with separations = Mterm.add t2 l t1_info.separations }
    in
    let t2_info =
      let l =
        try (lo2, hi2, lo1, hi1) :: Mterm.find t1 t2_info.separations with
        | Not_found -> [ (lo2, hi2, lo1, hi1) ]
      in
      { t2_info with separations = Mterm.add t1 l t2_info.separations }
    in
    let locs_info = Mterm.add t1 t1_info info.locs_info in
    let locs_info = Mterm.add t2 t2_info locs_info in
    { info with locs_info }
  with
  | NoCst ->
    Format.printf "No cst for separation@.";
    info

let term_to_loc t =
  match t.t_node with
  | Tapp (_, []) -> Undefined t
  | _ -> failwith "Unsupported defined loc"

let rec term_to_update t =
  match t.t_node with
  | Tapp (ls, []) when ls_equal ls !!symbols.empty -> Empty
  | Tapp (ls, [ loc; offset ]) when ls_equal ls !!symbols.singleton ->
    Singleton (term_to_loc loc, int_of_term offset)
  | Tapp (ls, [ loc_set1; loc_set2 ]) when ls_equal ls !!symbols.union ->
    Union (term_to_update loc_set1, term_to_update loc_set2)
  | _ -> assert false

let add_mc_update info pr old_mc new_mc old_mp new_mp loc_set =
  let update = term_to_update loc_set in
  (* Add the previous mc to info if it's not already there *)
  let mcs_info =
    if Mterm.mem old_mc info.mcs_info then
      info.mcs_info
    else
      Mterm.add old_mc { modif = None } info.mcs_info
  in
  let mc_info =
    {
      modif =
        Some
          {
            pr;
            update;
            prev_mc = old_mc;
            prev_mp = old_mp;
            mp = new_mp;
            loc_set;
          };
    }
  in
  let mcs_info = Mterm.add new_mc mc_info mcs_info in
  { info with mcs_info }

let rec collect pr info f =
  let collect = collect pr in
  match f.t_node with
  | Tbinop (Tand, f1, f2) ->
    let info = collect info f1 in
    collect info f2
  | Tapp (ls, [ t1; lo1; hi1; t2; lo2; hi2 ])
    when ls_equal ls !!symbols.separated ->
    add_separated info t1 lo1 hi1 t2 lo2 hi2
  | Tapp (ls, [ old_mc; old_mp; new_mc; new_mp; loc_set ])
    when ls_equal ls !!symbols.assign ->
    add_mc_update info pr old_mc new_mc old_mp new_mp loc_set
  | Tapp (ls, _) when ls_equal ls !!symbols.load_int32 ->
    (* We read some info about the value of a loc at a point in memory *)
    Format.printf "TODO: Load int32";
    info
  (* TODO: This is terrible, we need to fix this *)
  | Tapp (ls, _) when ls_equal ls !!symbols.initialized ->
    symbols := Some { !!symbols with initialized = ls };
    info
  | _ -> info

let collect_info info d =
  match d.d_node with
  | Dprop (kind, pr, f) when kind = Paxiom || kind = Plemma -> collect pr info f
  | _ -> info

let init_symbols env =
  let mm =
    (Env.read_theory env [ "BV_memory_model" ] "MemoryBV_Gen").th_export
  in
  let bv = (Env.read_theory env [ "logicint" ] "BVLogic").th_export in
  let cint = (Env.read_theory env [ "cint" ] "BVCheck_Gen").th_export in
  let bv32 = (Env.read_theory env [ "tis_bv" ] "BV32").th_export in
  symbols :=
    Some
      {
        initialized = ns_find_ls mm [ "acsl_initialized" ];
        separated = ns_find_ls mm [ "acsl_separated" ];
        assign = ns_find_ls mm [ "assign" ];
        empty = ns_find_ls mm [ "empty" ];
        singleton = ns_find_ls mm [ "singleton" ];
        union = ns_find_ls mm [ "union" ];
        load_int32 = ns_find_ls mm [ "load_int32" ];
        bv_add = ns_find_ls bv [ "add" ];
        bv_sub = ns_find_ls bv [ "sub" ];
        bv_mul = ns_find_ls bv [ "mul" ];
        bv_to_logic_signed = ns_find_ls cint [ "to_logic_signed" ];
        bv32_ts = ns_find_ts bv32 [ "t" ];
      }

(* TODO: "Transitivity" *)
let rec potentially_affected_by_update info loc update =
  match update with
  | Empty -> false
  | Singleton (loc', _offset) -> (
    match loc' with
    | Defined -> failwith "Unsupported defined loc"
    | Undefined t ->
      (* let loc_info = Mterm.find t info.locs_info in *)
      let loc_info = Mterm.find loc info.locs_info in
      let separations = Mterm.find t loc_info.separations in
      (* TODO: Separation analysis :
       * We have a separation between x[lo1..hi1] and y[lo2..hi2]
       * If we have an update on y[lo3..hi3] then
       * the memory interval which is unnafected for x is :
       * x[lo1 + max(0, hi3 - hi2) .. hi1 - max (0, lo2 - lo3)]
       *)
      let f _b (_lo1, _hi1, _lo2, _hi2) = false in
      List.fold_left f true separations)
  | Union (update1, update2) ->
    potentially_affected_by_update info loc update1
    || potentially_affected_by_update info loc update2

let rec print_term printer fmt t =
  let print_term = print_term printer in
  match t.t_node with
  | Tvar v -> Format.fprintf fmt "%s" (id_unique printer v.vs_name)
  | Tapp (ls, []) -> Format.fprintf fmt "%s" (id_unique printer ls.ls_name)
  | Tapp (ls, tl) -> (
    let s = id_unique printer ls.ls_name in
    match (Ident.sn_decode s, tl) with
    | Ident.SNinfix s, [ t1; t2 ] ->
      Format.fprintf fmt "(%a %s %a)" print_term t1 s print_term t2
    | _ ->
      Format.fprintf fmt "(%s %a)"
        (id_unique printer ls.ls_name)
        (Format.pp_print_list ~pp_sep:Pp.space print_term)
        tl)
  | Tconst (Constant.ConstInt i) -> (
    let ty = Opt.get t.t_ty in
    match ty.ty_node with
    | Tyapp (ts, []) ->
      Format.fprintf fmt "(%d : %s)" (BigInt.to_int i.il_int)
        (id_unique printer ts.ts_name)
    | _ -> Format.fprintf fmt "%a" Pretty.print_term t)
  | _ -> Pretty.print_term fmt t

let term_to_str printer t = Format.asprintf "%a" (print_term printer) t

let rec initialized mcs_info printer strat mp prev_mp mc =
  match (Mterm.find mc mcs_info).modif with
  | Some modif ->
    let s =
      term_to_str printer modif.prev_mc
      ^ ","
      ^ term_to_str printer prev_mp
      ^ "," ^ term_to_str printer mp ^ ","
      ^ term_to_str printer modif.loc_set
    in
    let s' =
      initialized mcs_info printer strat prev_mp modif.prev_mp modif.prev_mc
    in
    Strategy.Sapply_trans
      ("apply", [ "initialized_assign"; "with"; s ], [ Sdo_nothing; s' ])
  (* Initial memory state *)
  | None -> strat

let rec treat_info info printer strat (ls, mc, mp, loc) =
  let loc_info = Mterm.find loc info.locs_info in
  if Mterm.mem mc loc_info.mc_values then
    (* We don't need to go unfold mcs, we already have a value here *)
    strat
  else
    let mc_info = Mterm.find mc info.mcs_info in
    match mc_info.modif with
    | None -> Strategy.Sdo_nothing
    | Some modif ->
      if potentially_affected_by_update info loc modif.update then
        Strategy.Sdo_nothing
      else
        let ty = ty_app !!symbols.bv32_ts [] in
        let t1 = fs_app ls [ mc; mp; loc ] ty in
        let t2 = fs_app ls [ modif.prev_mc; mp; loc ] ty in
        let t1 = term_to_str printer t1 in
        let t2 = term_to_str printer t2 in
        let strat' =
          treat_info info printer strat (ls, modif.prev_mc, mp, loc)
        in
        let s1 =
          initialized info.mcs_info printer Strategy.Sdo_nothing mp
            modif.prev_mp mc
        in
        let pr = id_unique printer modif.pr.pr_name in
        let s2 = Strategy.Sapply_trans ("apply", [ pr ], [ Sdo_nothing ]) in
        let strats = [ s1; s2; s2; s2; s2 ] in
        let s1 = Strategy.Sapply_trans ("split_vc", [], strats) in
        let s1 =
          Strategy.Sapply_trans ("apply", [ "load_int32_assign" ], [ s1 ])
        in
        Strategy.Sapply_trans ("replace", [ t1; t2 ], [ strat'; s1 ])

(* TODO: Use eliminate_let  *)
(* TODO: Handle assigns goals *)
(* TODO: Handle universal quantification, eg. forall i. a[i] == ... *)
let f env task =
  let printer = (Args_wrapper.build_naming_tables task).Trans.printer in
  init_symbols env;
  let goal = task_goal_fmla task in
  let initialized_goals = get_initialized goal in
  if List.length initialized_goals != 0 then
    let info =
      List.fold_left collect_info
        { mcs_info = Mterm.empty; locs_info = Mterm.empty }
        (task_decls task)
    in
    let strat =
      List.fold_left
        (fun strat (_, mc, _, _, _) ->
          match (Mterm.find mc info.mcs_info).modif with
          | None -> strat
          | Some modif ->
            initialized info.mcs_info printer strat modif.mp modif.prev_mp mc)
        Strategy.Sdo_nothing initialized_goals
    in
    strat
  else
    let locs = get_locs goal in
    if List.length locs = 0 then
      Strategy.Sdo_nothing
    else
      let info =
        List.fold_left
          (fun info (_, _, _, loc) ->
            { info with locs_info = Mterm.add loc default_info info.locs_info })
          { mcs_info = Mterm.empty; locs_info = Mterm.empty }
          locs
      in
      let info = List.fold_left collect_info info (task_decls task) in
      let strat =
        List.fold_left (treat_info info printer) Strategy.Sdo_nothing locs
      in
      let prs =
        Mterm.fold
          (fun t mc_info s ->
            match mc_info.modif with
            | None -> s
            | Some modif ->
              let pr = id_unique printer modif.pr.pr_name in
              if s = "" then
                pr
              else
                s ^ "," ^ pr)
          info.mcs_info ""
      in
      Strategy.Sapply_trans ("unfold", [ "assign"; "in"; prs ], [ strat ])

let () =
  Strategy.register_strat ~desc:"Strategy@ for@ memory@ analysis." "mem_auto" f
