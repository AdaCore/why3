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

(* TODO

  - no more parentheses in drivers (the printer will add them with protect_on)

  - driver uses %1, %2, etc. and translation eta-expanses if necessary
      introduce a let when %1 appears several times?

  - simplications
      let x = y in ...
      let x = 17 in ... (converter)
      let x = () in ...
      let f (us: unit) = ... (when variable us is not used)
      some beta-reductions, at least (fun _ -> e) ()

  - singleton types
    record/constructor fields of type unit

  - ghost code
    remove it as much as possible (in types and function arguments)

*)

open Format
open Pp
open Stdlib
open Ident
open Ty
open Term
open Theory
open Printer

let debug =
  Debug.register_info_flag "extraction"
    ~desc:"Print@ details@ of@ program@ extraction."

let clean_fname fname =
  let fname = Filename.basename fname in
  (try Filename.chop_extension fname with _ -> fname)

let modulename ?fname path t =
  let fname = match fname, path with
    | Some fname, _ -> clean_fname fname
    | None, [] -> "why3"
    | None, _ -> String.concat "__" path
  in
  fname ^ "__" ^ t

(** Abstract syntax of ML *)

module ML = struct

  type ty =
    | Tvar    of ident
    | Tapp    of ident * ty list
    | Ttuple  of ty list
    | Tsyntax of string * ty list

  type var = ident * ty

  type pat =
    | Pwild
    | Pident  of ident
    | Papp    of ident * pat list
    | Ptuple  of pat list
    | Precord of (ident * pat) list
    | Psyntax of string * pat list
    | Por     of pat * pat
    | Pas     of pat * ident

  type is_rec = bool

  type binop = Band | Bor | Beq

  type for_direction = To | DownTo

  type exn =
    | Xident  of ident
    | Xsyntax of string
    | Xexit             (* Pervasives.Exit *)

  type expr =
    | Econst  of Number.integer_constant
    | Ebool   of bool
    | Eident  of ident
    | Esyntax of string * expr list
    | Eapp    of expr * expr list
    | Efun    of var list * expr
    | Elet    of ident * expr * expr
    | Eletrec of is_rec * (ident * var list * expr) list * expr
    | Eif     of expr * expr * expr
    | Ecast   of expr * ty
    | Etuple  of expr list (* at least 2 expressions *)
    | Econstr of ident * expr list
    | Ematch  of expr * (pat * expr) list
    | Ebinop  of expr * binop * expr
    | Enot    of expr
    | Eblock  of expr list
    | Ewhile  of expr * expr
    | Efor    of ident * ident * for_direction * ident * expr
    | Eraise  of exn * expr option
    | Etry    of expr * (exn * ident option * expr) list
    | Eabsurd
    (* records *)
    | Erecord   of (ident * expr) list
    | Egetfield of expr * ident
    | Esetfield of expr * ident * expr

  type is_mutable = bool

  type typedef =
    | Dabstract
    | Ddata     of (ident * ty list) list
    | Drecord   of (is_mutable * ident * ty) list
    | Dalias    of ty

  type decl =
    | Dtype of (ident * ident list * typedef) list
    | Dlet  of is_rec * (ident * var list * expr) list
        (* TODO add return type? *)
    | Dexn  of ident * ty option

  (** smart constructors *)

  let tunit = Ttuple []

  let enop = Eblock []

  let etuple = function
    | []  -> enop
    | [e] -> e
    | l   -> Etuple l

  let eseq e1 e2 = match e1, e2 with
    | Eblock [], e | e, Eblock [] -> e
    | Eblock l1, Eblock l2 -> Eblock (l1 @ l2)
    | _, Eblock l2 -> Eblock (e1 :: l2)
    | Eblock l1, _ -> Eblock (l1 @ [e2])
    | _ -> Eblock [e1; e2]

end

(** Translation from WhyML to ML *)

type info = {
  exec: Mlw_exec.t;
  info_syn: syntax_map;
  converters: syntax_map;
  current_theory: Theory.theory;
  current_module: Mlw_module.modul option;
  th_known_map: Decl.known_map;
  mo_known_map: Mlw_decl.known_map;
  fname: string option;
  unsafe_int: bool;
}

module Translate = struct

  open Decl

  let type_unit = ML.Ttuple []

  let rec type_ info ty = match ty.ty_node with
    | Tyvar v ->
        ML.Tvar v.tv_name
    | Tyapp (ts, tl) when is_ts_tuple ts ->
        ML.Ttuple (List.map (type_ info) tl)
    | Tyapp (ts, tl) ->
        begin match query_syntax info.info_syn ts.ts_name with
        | Some s -> ML.Tsyntax (s, List.map (type_ info) tl)
        | None -> ML.Tapp (ts.ts_name, List.map (type_ info) tl)
        end

  let vsty info vs = vs.vs_name, type_ info vs.vs_ty

  let has_syntax info id = Mid.mem id info.info_syn

  let get_record info ls =
    match Mid.find_opt ls.ls_name info.th_known_map with
      | Some { d_node = Ddata dl } ->
        let rec lookup = function
          | [] -> []
          | (_, [cs, pjl]) :: _ when ls_equal cs ls ->
            (try List.map Opt.get pjl with _ -> [])
          | _ :: dl -> lookup dl
        in
        lookup dl
      | Some _ | None ->
        []

  let type_decl info ts = match ts.ts_def with
    | NoDef | Range _ | Float _ ->
        (* FIXME: how should we extract Range and Float? *)
        ML.Dabstract
    | Alias ty ->
        ML.Dalias (type_ info ty)

  let type_args = List.map (fun tv -> tv.tv_name)

  let type_decl info ts =
    if has_syntax info ts.ts_name then [] else
    [ML.Dtype [ts.ts_name, type_args ts.ts_args, type_decl info ts]]

  let data_decl info (ts, csl) =
    let default () =
      let constr (cs, _) = cs.ls_name, List.map (type_ info) cs.ls_args in
      ML.Ddata (List.map constr csl) in
    let field ls = false, ls.ls_name, type_ info (Opt.get ls.ls_value) in
    let defn = function
      | [cs, _] ->
          let pjl = get_record info cs in
          if pjl = [] then default () else ML.Drecord (List.map field pjl)
      | _ ->
          default ()
    in
    ts.ts_name, type_args ts.ts_args, defn csl

  let data_decl info (ts, _ as d) =
    if has_syntax info ts.ts_name then [] else [data_decl info d]

  let projections _info (ts, csl) =
    let pjl = List.filter ((<>) None) (snd (List.hd csl)) in
    let pjl = List.map Opt.get pjl in
    let x = id_register (id_fresh "x") in
    let projection ls =
      let branch (cs, pjl) =
        let arg = function
          | Some ls' when ls_equal ls' ls -> ML.Pident x
          | _ -> ML.Pwild in
        ML.Papp (cs.ls_name, List.map arg pjl), ML.Eident x
      in
      let id = id_register (id_fresh "x") in
      let ty =
        ML.Tapp (ts.ts_name,
                 List.map (fun tv -> ML.Tvar tv.tv_name) ts.ts_args) in
      let def = ML.Ematch (ML.Eident id, List.map branch csl) in
      ML.Dlet (false, [ls.ls_name, [id, ty], def])
    in
    List.map projection pjl

  let is_record = function
    | _, [_, pjl] -> List.for_all ((<>) None) pjl
    | _ -> false

  let projections info (ts, _ as d) =
    if has_syntax info ts.ts_name || is_record d then []
    else projections info d

  let filter_ghost_fields ls def al =
    let flt fd arg = if fd.Mlw_expr.fd_ghost then def else arg in
    try List.map2 flt (Mlw_expr.restore_pl ls).Mlw_expr.pl_args al
    with Not_found -> al

  let rec pat info p = match p.pat_node with
    | Pwild ->
        ML.Pwild
    | Pvar v ->
        ML.Pident v.vs_name
    | Pas (p, v) ->
        ML.Pas (pat info p, v.vs_name)
    | Por (p, q) ->
        ML.Por (pat info p, pat info q)
    | Papp (cs, pl) when is_fs_tuple cs ->
        ML.Ptuple (List.map (pat info) pl)
    | Papp (cs, pl) ->
        begin match query_syntax info.info_syn cs.ls_name with
        | Some s -> ML.Psyntax (s, List.map (pat info) pl)
        | None ->
          let pat_void = Term.pat_app Mlw_expr.fs_void [] Mlw_ty.ty_unit in
          let pl = filter_ghost_fields cs pat_void pl in
          let pjl = get_record info cs in
          if pjl = [] then
            ML.Papp (cs.ls_name, List.map (pat info) pl)
          else
            let field ls p = ls.ls_name, pat info p in
            ML.Precord (List.map2 field pjl pl)
        end

  let is_constructor info ls =
  (* eprintf "is_constructor: ls=%s@." ls.ls_name.id_string; *)
    match Mid.find_opt ls.ls_name info.th_known_map with
      | Some { d_node = Ddata dl } ->
        let constr (_,csl) = List.exists (fun (cs,_) -> ls_equal cs ls) csl in
        List.exists constr dl
      | _ -> false

  (* can the type of a value be derived from the type of the arguments? *)
  let unambig_fs fs =
    let rec lookup v ty = match ty.ty_node with
      | Tyvar u when tv_equal u v -> true
      | _ -> ty_any (lookup v) ty
    in
    let lookup v = List.exists (lookup v) fs.ls_args in
    let rec inspect ty = match ty.ty_node with
      | Tyvar u when not (lookup u) -> false
      | _ -> ty_all inspect ty
    in
    Opt.fold (fun _ -> inspect) true fs.ls_value

  let oty_int = Some ty_int

  let rec app ls info tl =
    let isconstr = is_constructor info ls in
    let is_field (_, csl) = match csl with
      | [_, pjl] ->
        let is_ls = function None -> false | Some ls' -> ls_equal ls ls' in
        List.for_all ((<>) None) pjl && List.exists is_ls pjl
      | _ -> false in
    let isfield = match Mid.find_opt ls.ls_name info.th_known_map with
      | Some { d_node = Ddata dl } -> not isconstr && List.exists is_field dl
      | _ -> false
    in
    let id = ls.ls_name in
    match tl with
      | tl when isconstr ->
          let tl = filter_ghost_fields ls Mlw_expr.t_void tl in
          let pjl = get_record info ls in
          if pjl = [] then
            ML.Econstr (id, List.map (term info) tl)
          else
            let field ls t = ls.ls_name, term info t in
            ML.Erecord (List.map2 field pjl tl)
      | [t1] when isfield ->
          ML.Egetfield (term info t1, id)
      | tl ->
          ML.Eapp (ML.Eident id, List.map (term info) tl)

  and term info t = match t.t_node with
    | Tvar v ->
        let gh = try (Mlw_ty.restore_pv v).Mlw_ty.pv_ghost
          with Not_found -> false in
        if gh then ML.enop else ML.Eident v.vs_name
    | Ttrue ->
        ML.Ebool true
    | Tfalse ->
        ML.Ebool false
    | Tconst (Number.ConstInt c) ->
        ML.Econst c
    | Tconst (Number.ConstReal _) ->
        assert false
    | Tapp (fs, tl) when is_fs_tuple fs ->
        ML.etuple (List.map (term info) tl)
    | Tapp (fs, [t1; t2]) when not info.unsafe_int
        && ls_equal fs ps_equ && oty_equal t1.t_ty oty_int ->
        ML.Esyntax ("(Why3extract.Why3__BigInt.eq %1 %2)",
                    [term info t1; term info t2])
    | Tapp (fs, tl) ->
        begin match query_syntax info.info_syn fs.ls_name with
        | Some s -> ML.Esyntax (s, List.map (term info) tl)
        | None when unambig_fs fs -> app fs info tl
        | None -> ML.Ecast (app fs info tl, type_ info (t_type t))
        end
    | Tif (t1, t2, t3) ->
        ML.Eif (term info t1, term info t2, term info t3)
    | Tlet (t1, tb) ->
        let v, t2 = t_open_bound tb in
        ML.Elet (v.vs_name, term info t1, term info t2)
    | Tcase (t1, bl) ->
        ML.Ematch (term info t1, List.map (tbranch info) bl)
    | Teps _ when t_is_lambda t ->
        let vl, _, t1 = t_open_lambda t in
        ML.Efun (List.map (vsty info) vl, term info t1)
    | Teps _ | Tquant _ ->
        Format.eprintf "t = %a@." Pretty.print_term t;
        assert false
    | Tbinop (op, t1, t2) ->
        let t1 = term info t1 in
        let t2 = term info t2 in
        begin match op with
          | Tand -> ML.Ebinop (t1, ML.Band, t2)
          | Tor -> ML.Ebinop (t1, ML.Bor, t2)
          | Tiff -> ML.Ebinop (t1, ML.Beq, t2)
          | Timplies -> ML.Ebinop (ML.Enot t1, ML.Bor, t2) end
    | Tnot t1 ->
        ML.Enot (term info t1)

  and tbranch info br =
    let p, t = t_open_branch br in
    pat info p, term info t

  let logic_defn info (ls, ld) =
    let vl, t = open_ls_defn ld in
    (ls.ls_name, List.map (vsty info) vl, term info t)

  let logic_defn info (ls, _ as d) =
    if has_syntax info ls.ls_name then [] else [logic_defn info d]

  let logic_decl info d = match d.d_node with
    | Dtype ts ->
        type_decl info ts
    | Ddata tl ->
        begin match List.flatten (List.map (data_decl info) tl) with
          | [] -> []
          | dl -> [ML.Dtype dl] end @
        List.flatten (List.map (projections info) tl)
    | Dlogic [ls, _ as ld] ->
        if has_syntax info ls.ls_name then [] else
        let isrec = Sid.mem ls.ls_name d.d_syms in
        [ML.Dlet (isrec, logic_defn info ld)]
    | Dlogic ll ->
        begin match List.flatten (List.map (logic_defn info) ll) with
          | [] -> []
          | dl -> [ML.Dlet (true, dl)] end
    | Decl.Dparam _
    | Dind _
    | Dprop _ ->
        []

  let logic_decl info d =
    if Mlw_exec.is_exec_decl info.exec d then logic_decl info d else []

  let logic_decl info td = match td.td_node with
    | Decl d ->
        let union = Sid.union d.d_syms d.d_news in
        let inter = Mid.set_inter union info.mo_known_map in
        if Sid.is_empty inter then logic_decl info d else []
    | Use _ | Clone _ | Meta _ ->
        []

  let theory info th =
    List.flatten (List.map (logic_decl info) th.th_decls)

  (** programs *)

  open Mlw_ty
  open Mlw_ty.T
  open Mlw_expr
  open Mlw_decl
  open Mlw_module

  let rec ity info t = match t.ity_node with
    | Ityvar v ->
        ML.Tvar v.tv_name
    | Itypur (ts, tl) when is_ts_tuple ts ->
        ML.Ttuple (List.map (ity info) tl)
    | Itypur (ts, tl)
    | Ityapp ({its_ts=ts}, tl, _) ->
        begin match query_syntax info.info_syn ts.ts_name with
        | Some s -> ML.Tsyntax (s, List.map (ity info) tl)
        | None -> ML.Tapp (ts.ts_name, List.map (ity info) tl)
        end

  let is_underscore pv =
    pv.pv_vs.vs_name.id_string = "_" && ity_equal pv.pv_ity ity_unit

  let is_int_constant e = match e.e_node with
    | Elogic { t_node = Tconst (Number.ConstInt _) } -> true
    | _ -> false
  let get_int_constant e = match e.e_node with
    | Elogic { t_node = Tconst (Number.ConstInt n) } -> n
    | _ -> assert false

  let pv_name pv = pv.pv_vs.vs_name

  let pvty info pv =
    if pv.pv_ghost then (pv.pv_vs.vs_name, type_unit)
    else vsty info pv.pv_vs

  let lv_name = function
    | LetV pv -> pv_name pv
    | LetA ps -> ps.ps_name

  let for_direction = function
    | To     -> ML.To
    | DownTo -> ML.DownTo

  let is_letrec = function
    | [fd] -> fd.fun_lambda.l_spec.c_letrec <> 0
    | _ -> true

  let filter_ghost_params =
(* removal of ghost does not work
    let dummy = create_pvsymbol (Ident.id_fresh "") ity_unit in
    fun args ->
    match List.filter (fun v -> not v.Mlw_ty.pv_ghost) args with
    | [] -> [dummy]
    | l -> l
*)
    fun args -> args (* filtering ghost happens in pvty *)
(*
    List.map
      (fun v -> if v.Mlw_ty.pv_ghost then
                  create_pvsymbol (Ident.id_fresh "") ity_unit
                else v)
 *)
  let rec expr info e =
    assert (not e.e_ghost);
    match e.e_node with
      | Elogic t ->
          term info t
      | Evalue pv when pv.pv_ghost ->
         ML.enop
      | Evalue pv ->
           ML.Eident (pv_name pv)
      | Earrow a ->
          begin match query_syntax info.info_syn a.ps_name with
          | Some s -> ML.Esyntax (s, [])
          | None   -> ML.Eident a.ps_name end
      (* converter *)
      | Elet ({ let_sym = LetV pv; let_expr = e1 },
              { e_node = Eapp ({ e_node = Earrow a }, pv', _) })
        when pv_equal pv' pv
             && Mid.mem a.ps_name info.converters && is_int_constant e1 ->
          let s = fst (Mid.find a.ps_name info.converters) in
          let n = Number.compute_int (get_int_constant e1) in
          let e1 = ML.Esyntax (BigInt.to_string n, []) in
          ML.Esyntax (s, [e1])
      | Eapp (e, v, _) when v.pv_ghost ->
         (* ghost parameters are unit *)
         ML.Eapp (expr info e, [ML.enop])
      | Eapp (e, v, _) ->
          ML.Eapp (expr info e, [ML.Eident (pv_name v)])
      | Elet ({ let_sym = _lv; let_expr = e1 }, e2) when e1.e_ghost ->
         (* TODO: remove superflous let *)
         (* ML.Elet (lv_name lv, ML.enop, *) expr info e2 (* ) *)
      | Elet ({ let_sym = LetV pv }, e2) when ity_equal pv.pv_ity ity_mark ->
          expr info e2
      | Elet ({ let_sym = LetV pv; let_expr = e1 }, e2) when is_underscore pv ->
          ML.eseq (expr info e1) (expr info e2)
      | Elet ({ let_sym = lv ; let_expr = e1 }, e2) ->
          ML.Elet (lv_name lv, expr info e1, expr info e2)
      | Eif (e0, e1, e2) ->
          ML.Eif (expr info e0, expr info e1, expr info e2)
      | Eassign (pl, e1, _, pv) ->
          ML.Esetfield (expr info e1, pl.pl_ls.ls_name,
                        ML.Eident (pv_name pv))
      | Eloop (_, _, e1) ->
          ML.Ewhile (ML.Ebool true, expr info e1)
      | Efor (pv, (pvfrom, dir, pvto), _, e1) ->
          ML.Efor (pv_name pv,
                   pv_name pvfrom, for_direction dir, pv_name pvto,
                   expr info e1)
      | Eraise (xs,_) when xs_equal xs xs_exit ->
          ML.Eraise (ML.Xexit, None)
      | Eraise (xs, e1) ->
          begin match query_syntax info.info_syn xs.xs_name with
          | Some s ->
              ML.Eraise (ML.Xsyntax s, Some (expr info e1))
          | None when ity_equal xs.xs_ity ity_unit ->
              ML.Eraise (ML.Xident xs.xs_name, None)
          | None ->
              ML.Eraise (ML.Xident xs.xs_name, Some (expr info e1))
          end
      | Etry (e1, bl) ->
          ML.Etry (expr info e1, List.map (xbranch info) bl)
      | Eabstr (e1, _) ->
          expr info e1
      | Eabsurd ->
          ML.Eabsurd
      | Eassert _ ->
          ML.enop
      | Eghost _
      | Eany _ ->
          assert false
      | Ecase (e1, [_,e2]) when e1.e_ghost ->
          expr info e2
      | Ecase (e1, bl) ->
          ML.Ematch (expr info e1, List.map (ebranch info) bl)
      | Erec (fdl, e1) ->
          (* FIXME what about ghosts? *)
          let cmp {fun_ps=ps1} {fun_ps=ps2} =
            Pervasives.compare ps1.ps_ghost ps2.ps_ghost in
          let fdl = List.sort cmp fdl in
          ML.Eletrec (is_letrec fdl, List.map (recdef info) fdl, expr info e1)

  and recdef info { fun_ps = ps; fun_lambda = lam } =
    assert (not ps.ps_ghost);
    let args = filter_ghost_params lam.l_args in
    ps.ps_name, List.map (pvty info) args, expr info lam.l_expr

  and ebranch info ({ppat_pattern=p}, e) =
    pat info p, expr info e

  and xbranch info (xs, pv, e) =
    match query_syntax info.info_syn xs.xs_name with
      | Some s ->
          ML.Xsyntax s, Some (pv_name pv), expr info e
      | None when xs_equal xs xs_exit ->
          ML.Xexit, None, expr info e
      | None when ity_equal xs.xs_ity ity_unit ->
          ML.Xident xs.xs_name, None, expr info e
      | None ->
          ML.Xident xs.xs_name, Some (pv_name pv), expr info e

  let pdata_decl info (its, csl, _) =
    let field fd = if fd.fd_ghost then ML.tunit else ity info fd.fd_ity in
    let default () =
      let constr (cs, _) = cs.pl_ls.ls_name, List.map field cs.pl_args in
      ML.Ddata (List.map constr csl) in
    let field (ls, fd) = fd.fd_mut <> None, ls.ls_name, field fd in
    let defn = function
      | [cs, _] ->
        let pjl = get_record info cs.pl_ls in
        if pjl = [] then default ()
        else ML.Drecord (List.map field (List.combine pjl cs.pl_args))
      | _ ->
        default ()
    in
    let ts = its.its_ts in
    ts.ts_name, type_args ts.ts_args, defn csl

  let pdata_decl info (its, _, _ as d) =
    if has_syntax info its.its_ts.ts_name then [] else [pdata_decl info d]

  let pprojections _info ({its_ts=ts}, csl, _) =
    let pjl = List.filter ((<>) None) (snd (List.hd csl)) in
    let pjl = List.map Opt.get pjl in
    let x = id_register (id_fresh "x") in
    let projection ls =
      let branch (cs, pjl) =
        let arg = function
          | Some ls' when pl_equal ls' ls -> ML.Pident x
          | _ -> ML.Pwild in
        ML.Papp (cs.pl_ls.ls_name, List.map arg pjl), ML.Eident x
      in
      let id = id_register (id_fresh "x") in
      let ty =
        ML.Tapp (ts.ts_name,
                 List.map (fun tv -> ML.Tvar tv.tv_name) ts.ts_args) in
      let def = ML.Ematch (ML.Eident id, List.map branch csl) in
      ML.Dlet (false, [ls.pl_ls.ls_name, [id, ty], def])
    in
    List.map projection pjl

  let is_record = function
    | _, [_, pjl], _ -> List.for_all ((<>) None) pjl
    | _ -> false

  let pprojections info (ts, _, _ as d) =
    if has_syntax info ts.its_ts.ts_name || is_record d then []
    else pprojections info d

  let pdecl info pd =
    match pd.pd_node with
    | PDval (LetV pv) when pv_equal pv Mlw_decl.pv_old ->
        []
    | PDval _ ->
        []
    | PDtype ({ its_ts = ts } as its) ->
        let id = ts.ts_name in
        begin match its.its_def with
          | None ->
              [ML.Dtype [id, type_args ts.ts_args, ML.Dabstract]]
          | Some ty ->
              [ML.Dtype [id, type_args ts.ts_args, ML.Dalias (ity info ty)]]
        end
    | PDlet { let_sym = lv ; let_expr = e } ->
       Debug.dprintf debug "extract 'let' declaration %s@."
                     (lv_name lv).id_string;
       [ML.Dlet (false, [lv_name lv, [], expr info e])]
    | PDdata tl ->
        begin match List.flatten (List.map (pdata_decl info) tl) with
          | [] -> []
          | dl -> [ML.Dtype dl] end @
        List.flatten (List.map (pprojections info) tl)
    | PDrec fdl ->
        (* print defined, non-ghost first *)
        let cmp {fun_ps=ps1} {fun_ps=ps2} =
          Pervasives.compare
            (ps1.ps_ghost || has_syntax info ps1.ps_name)
            (ps2.ps_ghost || has_syntax info ps2.ps_name) in
        let fdl = List.sort cmp fdl in
        List.iter
          (fun {fun_ps=ps} ->
           Debug.dprintf debug "extract 'let rec' declaration %s@."
                         ps.ps_name.id_string) fdl;
        [ML.Dlet (is_letrec fdl, List.map (recdef info) fdl)]
    | PDexn xs ->
        let id = xs.xs_name in
        if ity_equal xs.xs_ity ity_unit then
          [ML.Dexn (id, None)]
        else
          [ML.Dexn (id, Some (ity info xs.xs_ity))]

  let warn_non_ghost_non_exec ps =
    if not ps.ps_ghost then
      Warning.emit ?loc:ps.ps_name.id_loc
        "Cannot extract code from non-ghost function %s: body is not executable"
        ps.ps_name.id_string

  let pdecl info d =
    if Mlw_exec.is_exec_pdecl info.exec d then pdecl info d else
      begin
        begin match d.pd_node with
        | PDlet { let_sym = LetA ps } -> warn_non_ghost_non_exec ps
        | PDrec fdl ->
           List.iter
             (fun {fun_ps=ps} -> warn_non_ghost_non_exec ps) fdl
        | _ -> ()
        end;
        []
      end

  let module_ info m =
    List.flatten (List.map (pdecl info) m.mod_decls)

end

(** OCaml printers *)

module Print = struct

  open ML

  let ocaml_keywords =
    ["and"; "as"; "assert"; "asr"; "begin";
     "class"; "constraint"; "do"; "done"; "downto"; "else"; "end";
     "exception"; "external"; "false"; "for"; "fun"; "function";
     "functor"; "if"; "in"; "include"; "inherit"; "initializer";
     "land"; "lazy"; "let"; "lor"; "lsl"; "lsr"; "lxor"; "match";
     "method"; "mod"; "module"; "mutable"; "new"; "object"; "of";
     "open"; "or"; "private"; "rec"; "sig"; "struct"; "then"; "to";
     "true"; "try"; "type"; "val"; "virtual"; "when"; "while"; "with";
     "raise";]

  let is_ocaml_keyword =
    let h = Hstr.create 17 in
    List.iter (fun s -> Hstr.add h s ()) ocaml_keywords;
    Hstr.mem h

  let iprinter,aprinter,_tprinter,_pprinter =
    let isanitize = sanitizer char_to_alpha char_to_alnumus in
    let lsanitize = sanitizer char_to_lalpha char_to_alnumus in
    create_ident_printer ocaml_keywords ~sanitizer:isanitize,
    create_ident_printer ocaml_keywords ~sanitizer:lsanitize,
    create_ident_printer ocaml_keywords ~sanitizer:lsanitize,
    create_ident_printer ocaml_keywords ~sanitizer:isanitize

  let forget_tvs () =
    forget_all aprinter

  (* type variables always start with a quote *)
  let print_tv fmt tv =
    fprintf fmt "'%s" (id_unique aprinter tv)

  let forget_id vs = forget_id iprinter vs
  let _forget_ids = List.iter forget_id
  let forget_var (vs, _) = forget_id vs
  let forget_vars = List.iter forget_var

  let rec forget_pat = function
    | Pwild -> ()
    | Pident id -> forget_id id
    | Papp (_, pl) | Ptuple pl | Psyntax (_, pl) -> List.iter forget_pat pl
    | Precord fl -> List.iter (fun (_, p) -> forget_pat p) fl
    | Por (p1, p2) -> forget_pat p1; forget_pat p2
    | Pas (p, _) -> forget_pat p

  let print_ident fmt id =
    let s = id_unique iprinter id in
    fprintf fmt "%s" s

  let print_path = print_list dot pp_print_string

  let print_qident ~sanitizer info fmt id =
    try
      let lp, t, p =
        try Mlw_module.restore_path id
        with Not_found -> Theory.restore_path id in
      let s = String.concat "__" p in
      let s = Ident.sanitizer char_to_alpha char_to_alnumus s in
      let s = sanitizer s in
      let s = if is_ocaml_keyword s then s ^ "_renamed" else s in
      if Sid.mem id info.current_theory.th_local ||
        Opt.fold (fun _ m -> Sid.mem id m.Mlw_module.mod_local)
        false info.current_module
      then
        fprintf fmt "%s" s
      else
        let fname = if lp = [] then info.fname else None in
        let m = Strings.capitalize (modulename ?fname lp t) in
        fprintf fmt "%s.%s" m s
    with Not_found ->
      let s = id_unique ~sanitizer iprinter id in
      fprintf fmt "%s" s

  let print_lident = print_qident ~sanitizer:Strings.uncapitalize
  let print_uident = print_qident ~sanitizer:Strings.capitalize

  let print_path_id fmt = function
    | [], id -> print_ident fmt id
    | p , id -> fprintf fmt "%a.%a" print_path p print_ident id

  let print_theory_name fmt th = print_path_id fmt (th.th_path, th.th_name)
  let print_module_name fmt m  = print_theory_name fmt m.Mlw_module.mod_theory

  (** Types *)

  let protect_on x s = if x then "(" ^^ s ^^ ")" else s

  let star fmt () = fprintf fmt " *@ "

  let rec print_ty ?(paren=false) info fmt = function
    | Tvar v ->
        print_tv fmt v
    | Ttuple [] ->
        fprintf fmt "unit"
    | Ttuple tl ->
        fprintf fmt (protect_on paren "%a") (print_list star (print_ty info)) tl
    | Tapp (ts, []) ->
        print_lident info fmt ts
    | Tapp (ts, [ty]) ->
        fprintf fmt (protect_on paren "%a@ %a")
          (print_ty ~paren:true info) ty (print_lident info) ts
    | Tapp (ts, tl) ->
        fprintf fmt (protect_on paren "(%a)@ %a")
          (print_list comma (print_ty info)) tl
          (print_lident info) ts
    | Tsyntax (s, tl) ->
        syntax_arguments s (print_ty info) fmt tl

  let print_vsty info fmt (v, ty) =
    fprintf fmt "%a:@ %a" (print_lident info) v (print_ty info) ty

  let print_tv_arg = print_tv
  let print_tv_args fmt = function
    | [] -> ()
    | [tv] -> fprintf fmt "%a@ " print_tv_arg tv
    | tvl -> fprintf fmt "(%a)@ " (print_list comma print_tv_arg) tvl

  let print_ty_arg info fmt ty = fprintf fmt "%a" (print_ty ~paren:true info) ty
  let print_vs_arg info fmt vs = fprintf fmt "@[(%a)@]" (print_vsty info) vs

  let print_type_decl info fst fmt (ts, args, def) =
    let print_constr fmt (cs, args) = match args with
      | [] ->
          fprintf fmt "@[<hov 4>| %a@]" (print_uident info) cs
      | tl ->
          fprintf fmt "@[<hov 4>| %a of %a@]" (print_uident info) cs
            (print_list star (print_ty_arg info)) tl in
    let print_field fmt (mut, ls, ty) =
      fprintf fmt "%s%a: %a;"
        (if mut then "mutable " else "")
        (print_lident info) ls (print_ty info) ty in
    let print_defn fmt = function
      | Dabstract ->
          ()
      | Ddata csl ->
          fprintf fmt " =@\n%a" (print_list newline print_constr) csl
      | Drecord fl ->
          fprintf fmt " = {@\n%a@\n}" (print_list newline print_field) fl
      | Dalias ty ->
          fprintf fmt " =@ %a" (print_ty info) ty
    in
    fprintf fmt "@[<hov 2>%s %a%a%a@]"
      (if fst then "type" else "and")
      print_tv_args args (print_lident info) ts print_defn def

  let print_list_next sep print fmt = function
    | [] ->
        ()
    | [x] ->
        print true fmt x
    | x :: r ->
        print true fmt x; sep fmt ();
        print_list sep (print false) fmt r

  let rec print_pat ?(paren=false) info fmt = function
    | Pwild ->
        fprintf fmt "_"
    | Pident v ->
        print_lident info fmt v
    | Pas (p, v) ->
        fprintf fmt (protect_on paren "%a as %a")
          (print_pat ~paren:true info) p (print_lident info) v
    | Por (p, q) ->
        fprintf fmt (protect_on paren "%a | %a")
          (print_pat info) p (print_pat info) q
    | Ptuple pl ->
        fprintf fmt "(%a)"
          (print_list comma (print_pat info)) pl
    | Psyntax (s, pl) ->
        syntax_arguments s (print_pat ~paren:true info) fmt pl
    | Papp (cs, []) ->
        print_uident info fmt cs
    | Papp (cs, [p]) ->
        fprintf fmt (protect_on paren "%a@ %a")
          (print_uident info) cs (print_pat ~paren:true info) p
    | Papp (cs, pl) ->
        fprintf fmt (protect_on paren "%a@ (%a)")
          (print_uident info) cs (print_list comma (print_pat info)) pl
    | Precord fl ->
        let print_field fmt (ls, p) = fprintf fmt "%a = %a"
          (print_lident info) ls (print_pat info) p in
        fprintf fmt "{ %a }" (print_list semi print_field) fl

  let min_int31 = BigInt.of_int (- 0x40000000)
  let max_int31 = BigInt.of_int    0x3FFFFFFF

  let print_const ~paren fmt c =
    let n = Number.compute_int c in
    if BigInt.eq n BigInt.zero then
      fprintf fmt "Why3extract.Why3__BigInt.zero"
    else if BigInt.eq n BigInt.one then
      fprintf fmt "Why3extract.Why3__BigInt.one"
    else if BigInt.le min_int31 n && BigInt.le n max_int31 then
      let m = BigInt.to_int n in
      fprintf fmt (protect_on paren "Why3extract.Why3__BigInt.of_int %d") m
    else
      let s = BigInt.to_string n in
      fprintf fmt
        (protect_on paren "Why3extract.Why3__BigInt.of_string \"%s\"") s

  let print_binop fmt = function
    | Band -> fprintf fmt "&&"
    | Bor -> fprintf fmt "||"
    | Beq -> fprintf fmt "="

  let is_unit = function
    | Eblock [] -> true
    | _ -> false

  let rec print_expr ?(paren=false) info fmt = function
    | Eident v ->
        print_lident info fmt v
    | Ebool b ->
        fprintf fmt "%b" b
    | Econst c when info.unsafe_int ->
        fprintf fmt "%s" (BigInt.to_string (Number.compute_int c))
    | Econst c ->
        print_const ~paren fmt c
    | Etuple el ->
        fprintf fmt "(%a)" (print_list comma (print_expr info)) el
    | Esyntax (s, tl) ->
        syntax_arguments s (print_expr_p info) fmt tl
    | Ecast (e, ty) ->
        fprintf fmt "@[<hov 2>(%a:@ %a)@]"
          (print_expr info) e (print_ty info) ty
    | Eif (e1, e2, e3) when is_unit e3 ->
        fprintf fmt
          (protect_on paren "@[<hv>@[<hov 2>if@ %a@]@ then@;<1 2>@[%a@]@]")
          (print_expr info) e1 (print_expr ~paren:true info) e2
    | Eif (e1, e2, e3) ->
        fprintf fmt (protect_on paren
        "@[<hv>@[<hov 2>if@ %a@]@ then@;<1 2>@[%a@]@;<1 0>else@;<1 2>@[%a@]@]")
          (print_expr info) e1 (print_expr info) e2 (print_expr info) e3
    | Elet (v, e1, e2) ->
        fprintf fmt (protect_on paren "@[<hov 2>let @[%a@] =@ @[%a@]@] in@ %a")
          (print_lident info) v (print_expr info) e1 (print_expr info) e2;
        forget_id v
    | Ematch (e1, [p, b1]) ->
        fprintf fmt (protect_on paren "@[<hov 2>let @[%a@] =@ @[%a@]@] in@ %a")
          (print_pat info) p (print_expr info) e1 (print_expr info) b1
    | Ematch (e1, bl) ->
        fprintf fmt "@[begin match @[%a@] with@\n@[<hov>%a@] end@]"
          (print_expr info) e1 (print_list newline (print_branch info)) bl
    | Ebinop (e1, op, e2) ->
        fprintf fmt (protect_on paren "@[<hov 1>%a %a@ %a@]")
          (print_expr_p info) e1 print_binop op (print_expr_p info) e2
    | Enot e1 ->
        fprintf fmt (protect_on paren "not %a") (print_expr_p info) e1
    | Eapp (e, el) ->
        fprintf fmt (protect_on paren "@[<hov 2>%a@ %a@]")
          (print_expr info) e (print_list space (print_expr_p info)) el
    | Efun (vl, e1) ->
        fprintf fmt (protect_on paren "@[<hov 2>(fun %a ->@ %a)@]")
          (print_list space (print_vs_arg info)) vl (print_expr info) e1;
        forget_vars vl
    | Econstr (c, []) ->
        print_uident info fmt c
    | Econstr (c, [e1]) ->
        fprintf fmt (protect_on paren "%a %a")
          (print_uident info) c (print_expr_p info) e1
    | Econstr (c, el) ->
        fprintf fmt (protect_on paren "@[<hov 1>%a@ (%a)@]")
          (print_uident info) c (print_list comma (print_expr info)) el
    | Erecord fl ->
        let print_field fmt (f, e) =
          fprintf fmt "%a = %a" (print_lident info) f (print_expr info) e in
        fprintf fmt "@[<hov 1>{ %a }@]" (print_list semi print_field) fl
    | Egetfield (e, f) ->
        fprintf fmt "%a.%a" (print_expr_p info) e (print_lident info) f
    | Esetfield (e1, f, e2) ->
        fprintf fmt (protect_on paren "%a.%a <- %a")
        (print_expr_p info) e1 (print_lident info) f (print_expr info) e2
    | Eblock [] ->
        fprintf fmt "()"
    | Eblock [e] ->
        print_expr ~paren info fmt e
    | Eblock bl ->
        fprintf fmt "@[<hv>begin@;<1 2>@[%a@]@ end@]"
          (print_list semi (print_expr info)) bl
    | Ewhile (e1, e2) ->
        fprintf fmt "@[<hv>while %a do@;<1 2>@[%a@]@ done@]"
          (print_expr info) e1 (print_expr info) e2
    | Efor (x, vfrom, dir, vto, e1) when info.unsafe_int ->
        fprintf fmt
          "@[<hov 2>for %a = %a %s %a do@\n%a@\ndone@]"
          (print_lident info) x  (print_lident info) vfrom
          (if dir = To then "to" else "downto") (print_lident info) vto
          (print_expr info) e1
    | Efor (x, vfrom, dir, vto, e1) ->
        fprintf fmt
      "@[<hov 2>(Why3extract.Why3__IntAux.for_loop_%s %a %a@ (fun %a ->@ %a))@]"
          (if dir = To then "to" else "downto")
          (print_lident info) vfrom (print_lident info) vto
          (print_lident info) x (print_expr info) e1
    | Eraise (Xexit, a) ->
        assert (a = None);
        fprintf fmt (protect_on paren "raise Pervasives.Exit")
    | Eraise (Xsyntax s, None) ->
        fprintf fmt (protect_on paren "raise %a")
          (syntax_arguments s (print_expr info)) []
    | Eraise (Xsyntax s, Some e1) ->
        fprintf fmt (protect_on paren "raise %a")
          (syntax_arguments s (print_expr info)) [e1]
    | Eraise (Xident id, None) ->
        fprintf fmt (protect_on paren "raise %a") (print_uident info) id
    | Eraise (Xident id, Some e1) ->
        fprintf fmt (protect_on paren "raise (%a %a)")
              (print_uident info) id (print_expr ~paren:true info) e1
    | Etry (e1, bl) ->
        fprintf fmt
          "@[<v>@[<hv>@[<hov 2>begin@ try@ %a@]@ with@]@\n@[<hov>%a@]@\nend@]"
          (print_expr info) e1 (print_list newline (print_xbranch info)) bl
    | Eabsurd ->
        fprintf fmt (protect_on paren "assert false (* absurd *)")
    | Eletrec (is_rec, fdl, e1) ->
        fprintf fmt (protect_on paren "@[<v>%a@\nin@\n%a@]")
          (print_list_next newline (print_rec is_rec info)) fdl
          (print_expr info) e1

  and print_rec lr info fst fmt (id, args, e) =
    let print_arg fmt v = fprintf fmt "@[%a@]" (print_vs_arg info) v in
    fprintf fmt "@[<hov 2>%s %a %a =@\n@[%a@]@]"
      (if fst then if lr then "let rec" else "let" else "and")
      (print_lident info) id (print_list space print_arg) args
      (print_expr info) e;
    forget_vars args

  and print_expr_p info fmt t = print_expr ~paren:true info fmt t

  and print_branch info fmt (p, e) =
    fprintf fmt "@[<hov 4>| %a ->@ %a@]" (print_pat info) p (print_expr info) e;
    forget_pat p

  and print_xbranch info fmt (xs, v, e) =
    begin match xs, v with
    | Xsyntax s, _ ->
        let v = match v with None -> [] | Some v -> [v] in
        fprintf fmt "@[<hov 4>| %a ->@ %a@]"
          (syntax_arguments s (print_lident info)) v
          (print_expr info) e
    | Xexit, _ ->
        fprintf fmt "@[<hov 4>| Pervasives.Exit ->@ %a@]" (print_expr info) e
    | Xident xs, None ->
        fprintf fmt "@[<hov 4>| %a ->@ %a@]"
          (print_uident info) xs (print_expr info) e
    | Xident xs, Some v ->
        fprintf fmt "@[<hov 4>| %a %a ->@ %a@]"
          (print_uident info) xs (print_lident info) v (print_expr info) e
    end;
    Opt.iter forget_id v

  let print_decl info fmt = function
    | Dtype dl ->
       print_list_next newline (print_type_decl info) fmt dl;
       fprintf fmt "@\n@\n"
    | Dlet (isrec, dl) ->
       let print_one fst fmt (ls, vl, e) =
         fprintf fmt "@[<hov 2>%s %a@ %a@ =@ %a@]"
                 (if fst then if isrec then "let rec" else "let" else "and")
                 (print_lident info) ls
                 (print_list space (print_vs_arg info)) vl
                 (print_expr info) e;
         forget_vars vl;
         forget_tvs ()
       in
       print_list_next newline print_one fmt dl;
       fprintf fmt "@\n@\n"
    | Dexn (xs, None) ->
       fprintf fmt "exception %a@\n@\n" (print_uident info) xs
    | Dexn (xs, Some ty) ->
       fprintf fmt "@[<hov 2>exception %a of %a@]@\n@\n"
               (print_uident info) xs (print_ty ~paren:true info) ty

end

(** Exported functions *)

let extract_filename ?fname th =
  (modulename ?fname th.th_path th.th_name.Ident.id_string) ^ ".ml"

let unsafe_int drv =
  drv.Mlw_driver.drv_printer = Some "ocaml-unsafe-int"

let print_preludes used fmt pm =
  (* we do not print the same prelude twice *)
  let ht = Hstr.create 5 in
  let add l s = if Hstr.mem ht s then l else (Hstr.add ht s (); s :: l) in
  let l = Sid.fold
    (fun id l -> List.fold_left add l (Mid.find_def [] id pm)) used [] in
  print_prelude fmt l

let extract_theory drv ?old ?fname fmt th =
  ignore (old); ignore (fname);
  let info = {
    exec = Mlw_exec.create drv th.th_known Mid.empty;
    info_syn = drv.Mlw_driver.drv_syntax;
    converters = drv.Mlw_driver.drv_converter;
    current_theory = th;
    current_module = None;
    th_known_map = th.th_known;
    mo_known_map = Mid.empty;
    fname = Opt.map clean_fname fname;
    unsafe_int = unsafe_int drv; } in
  let decls = Translate.theory info th in
  fprintf fmt
    "(* This file has been generated from Why3 theory %a *)@\n@\n"
    Print.print_theory_name th;
  print_prelude fmt drv.Mlw_driver.drv_prelude;
  print_preludes th.th_used fmt drv.Mlw_driver.drv_thprelude;
  fprintf fmt "@\n";
  print_list nothing (Print.print_decl info) fmt decls;
  fprintf fmt "@."

open Mlw_module

let extract_module drv ?old ?fname fmt m =
  ignore (old); ignore (fname);
  let th = m.mod_theory in
  let info = {
    exec = Mlw_exec.create drv th.th_known m.mod_known;
    info_syn = drv.Mlw_driver.drv_syntax;
    converters = drv.Mlw_driver.drv_converter;
    current_theory = th;
    current_module = Some m;
    th_known_map = th.th_known;
    mo_known_map = m.mod_known;
    fname = Opt.map clean_fname fname;
    unsafe_int = unsafe_int drv; } in
  let decls = Translate.theory info th in
  let mdecls = Translate.module_ info m in
  fprintf fmt
    "(* This file has been generated from Why3 module %a *)@\n@\n"
    Print.print_module_name m;
  print_prelude fmt drv.Mlw_driver.drv_prelude;
  let used = Sid.union m.mod_used m.mod_theory.th_used in
  print_preludes used fmt drv.Mlw_driver.drv_thprelude;
  fprintf fmt "@\n";
  print_list nothing (Print.print_decl info) fmt decls;
  print_list nothing (Print.print_decl info) fmt mdecls;
  fprintf fmt "@."

(*
Local Variables:
compile-command: "unset LANG; make -C ../.."
End:
*)
