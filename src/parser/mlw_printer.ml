(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Ptree

let debug_print_ids = Debug.register_flag "mlw_printer_print_ids"
    ~desc:"Print@ IDs@ (the@ line@ number@ of@ locations@ when@ the@ filename@ is@ empty)"

type 'a printers = { marked: 'a Pp.pp; closed: 'a Pp.pp }

let marker = ref None

let pp_loc_id fmt loc =
  if Debug.test_flag debug_print_ids then
    let f,l,_,_ = Loc.get loc in
    if f = "" then fprintf fmt "(*%d*)" l

let with_marker ?(msg="XXX") loc pp fmt x =
  marker := Some (msg, loc);
  pp fmt x;
  marker := None

let marker loc =
  match !marker with
  | Some (msg, loc') when Loc.equal loc' loc ->
      Some msg
  | _ -> None

let pp_maybe_marker fmt loc =
  pp_loc_id fmt loc;
  match marker loc with
  | Some msg ->
      fprintf fmt "(*%s*)@ " msg
  | None -> ()

let pp_maybe_marked ?(parens=true) loc pp_raw fmt x =
  let loc = loc x in
  match marker loc with
  | Some msg ->
      if parens then
        fprintf fmt "%a(*%s*)@ (%a)" pp_loc_id loc msg pp_raw x
      else
        fprintf fmt "%a(*%s*)@ %a" pp_loc_id loc msg pp_raw x
  | None ->
      fprintf fmt "%a%a" pp_loc_id loc pp_raw x

let next_pos =
  let counter = ref 0 in
  fun () ->
    incr counter;
    Loc.user_position "" !counter 0 0

let todo fmt str =
  fprintf fmt "__TODO_MLW_PRINTER__ (* %s *)" str

let pp_sep f fmt () =
  fprintf fmt f

let pp_opt ?(prefix:(unit, formatter, unit) format="")
    ?(suffix:(unit, formatter, unit) format="")
    ?(def:(unit, formatter, unit) format="") pp fmt =
  function
  | None -> fprintf fmt def
  | Some x -> fprintf fmt prefix; pp fmt x; fprintf fmt suffix

let pp_print_opt_list ?(prefix:(unit, formatter, unit) format="")
    ?(every:(unit, formatter, unit) format="")
    ?(sep:(unit, formatter, unit) format=" ")
    ?(suffix:(unit, formatter, unit) format="")
    ?(def:(unit, formatter, unit) format="") pp fmt =
  function
  | [] -> fprintf fmt def
  | xs ->
    let pp fmt x = fprintf fmt every; pp fmt x in
    fprintf fmt prefix;
    pp_print_list ~pp_sep:(pp_sep sep) pp fmt xs;
    fprintf fmt suffix

let pp_bool ?true_ ?false_ fmt = function
  | true -> pp_opt (fun fmt f -> fprintf fmt f) fmt true_
  | false -> pp_opt (fun fmt f -> fprintf fmt f) fmt false_

(* let pp_scoped fmt begin_ (f: ('a, formatter, unit) format) end_ : 'a =
 *   pp_open_box fmt 0;
 *   pp_open_hvbox fmt 2;
 *   fprintf fmt begin_;
 *   kfprintf (fun fmt ->
 *       pp_close_box fmt ();
 *       fprintf fmt end_;
 *       pp_close_box fmt ())
 *     fmt f *)

let expr_closed e = match e.expr_desc with
  | Eref | Etrue | Efalse | Econst _ | Eident _ | Etuple _ | Erecord _ | Efor _ | Ewhile _
  | Eassert _ | Eabsurd | Escope _ | Eidapp (_, []) | Einnfix _ ->
      true
  | _ -> marker e.expr_loc <> None

let term_closed t = match t.term_desc with
  | Ttrue | Tfalse | Tconst _ | Tident _ | Tupdate _ | Trecord _ | Ttuple _ | Tscope _
  | Tidapp (_, []) | Tinnfix _ | Tbinnop _ ->
      true
  | _ -> marker t.term_loc <> None

let pattern_closed p = match p.pat_desc with
  | Pwild | Pvar _ | Ptuple _ | Pparen _ | Pscope _ | Papp (_, []) | Pcast _ ->
      true
  | _ -> marker p.pat_loc <> None

let pty_closed t = match t with
  | PTtyvar _ | PTtuple _ | PTscope _ | PTparen _ | PTpure _ | PTtyapp (_, []) ->
      true
  | _ -> false

let pp_closed is_closed pp fmt x =
  if is_closed x
  then pp fmt x
  else fprintf fmt "@[<hv 1>(%a)@]" pp x

let remove_id_attr s id =
  let p = function
    | ATstr a -> a.Ident.attr_string <> s
    | _ -> true in
  {id with id_ats= List.filter p id.id_ats}

let pp_attr fmt = function
  | ATstr att ->
     (* `%@` prints a single `@` *)
     fprintf fmt "[%@%s]" att.Ident.attr_string
  | ATpos loc ->
      let filename, line, bchar, echar = Loc.get loc in
      fprintf fmt "[#%S %d %d %d]%a" filename line bchar echar
        pp_maybe_marker loc

let pp_id fmt (id: ident) =
  let pp_decode fmt str =
    let open Ident in
    match sn_decode str with
    | SNword s -> pp_print_string fmt s
    | SNinfix s -> fprintf fmt "( %s )" s
    | SNprefix s -> fprintf fmt "( %s_ )" s
    | SNtight s -> fprintf fmt "( %s )" s
    | SNget s -> fprintf fmt "( []%s )" s
    | SNset s -> fprintf fmt "( []%s<- )" s
    | SNupdate s -> fprintf fmt "( [<-]%s )" s
    | SNcut s -> fprintf fmt "( [..]%s )" s
    | SNlcut s -> fprintf fmt "(  [.._]%s )" s
    | SNrcut s -> fprintf fmt "( [_..]%s )" s  in
  fprintf fmt "%a%a%a"
    pp_maybe_marker id.id_loc
    pp_decode id.id_str
    (pp_print_opt_list ~prefix:" " pp_attr) id.id_ats

let rec pp_qualid fmt = function
  | Qident id -> pp_id fmt id
  | Qdot (qid, id) -> fprintf fmt "@[<h>%a.%a@]" pp_qualid qid pp_id id

let pp_true fmt () =
  pp_print_string fmt "true"

let pp_false fmt () =
  pp_print_string fmt "false"

let pp_const fmt c =
  Constant.print_def fmt c

let pp_asref fmt qid =
  fprintf fmt "@[<h>&%a@]" pp_qualid qid

let pp_idapp pp fmt qid xs =
  match qid with
  | Qdot (_, id) -> (
      match Ident.sn_decode id.id_str, xs with
      | Ident.SNword s, [x] when 'a' <= s.[0] && s.[0] <= 'z' ->
          fprintf fmt "@[<hv2>%a%a.%a@]" pp_maybe_marker id.id_loc pp.closed x pp_qualid qid
      | _ ->
          let pp_args = pp_print_list ~pp_sep:pp_print_space pp.closed in
          fprintf fmt "@[<hv 3>%a@ %a@]" pp_qualid qid pp_args xs )
  | Qident id ->
      match Ident.sn_decode id.id_str, xs with
      | Ident.SNword s, [x] when 'a' <= s.[0] && s.[0] <= 'z' ->
          fprintf fmt "@[<hv2>%a%a.%s@]" pp_maybe_marker id.id_loc pp.closed x s
      | Ident.SNword s, xs ->
          let pp_args = pp_print_list ~pp_sep:(pp_sep "@ ") pp.closed in
          fprintf fmt "@[<hv 2>%a%s@ %a@]" pp_maybe_marker id.id_loc s pp_args xs
      | Ident.SNinfix s, [x1; x2] ->
          fprintf fmt "@[<hv 2>%a@ %a%s %a@]" pp.closed x1
            pp_maybe_marker id.id_loc s pp.closed x2
      | Ident.SNprefix s, [x] ->
          fprintf fmt "@[<h>%a%s@ %a@]" pp_maybe_marker id.id_loc s pp.closed x
      | Ident.SNtight s, [x] ->
          fprintf fmt "@[<h>%a%s@ %a@]" pp_maybe_marker id.id_loc s pp.closed x
      | Ident.SNget s, [x1; x2] ->
          fprintf fmt "@[<hv 1>%a[%a]%a%s@]" pp.closed x1 pp.marked x2
            pp_maybe_marker id.id_loc s
      | Ident.SNset s, [x1; x2; x3] ->
          fprintf fmt "@[<hv 1>%a[%a]%a%s <- %a@]" pp.closed x1 pp.marked x2
            pp_maybe_marker id.id_loc s pp.closed x3
      | Ident.SNupdate s, [x1; x2; x3] ->
          fprintf fmt "@[<h>%a[%a <- %a]%a%s@]" pp.closed x1 pp.marked x2
            pp.marked x3 pp_maybe_marker id.id_loc s
      | Ident.SNcut s, [x] ->
          fprintf fmt "@[<h>%a[..]%a%s@]" pp.closed x pp_maybe_marker id.id_loc s
      | Ident.SNcut s, [x1; x2; x3] ->
          fprintf fmt "@[<h>%a[%a .. %a]%a%s@]" pp.closed x1 pp.marked x2 pp.marked x3
            pp_maybe_marker id.id_loc s
      | Ident.SNlcut s, [x1; x2] ->
          fprintf fmt "@[<h>%a[.. %a]%a%s@]" pp.closed x1 pp.marked x2
            pp_maybe_marker id.id_loc s
      | Ident.SNrcut s, [x1; x2] ->
          fprintf fmt "@[<h>%a[%a ..]%a%s@]" pp.closed x1 pp.marked x2
            pp_maybe_marker id.id_loc s
      | _ -> failwith "pp_idapp"

let pp_apply pp fmt x1 x2 =
  fprintf fmt "@[<hv 2>%a@ %a@]" pp.closed x1 pp.closed x2

let pp_infix pp fmt x ops =
  let pp_op fmt (op, x) =
    let s = match Ident.sn_decode op.id_str with
      | Ident.SNinfix s -> s
      | _ -> failwith ("pp_infix: "^op.id_str) in
    fprintf fmt "%a%s@ %a" pp_maybe_marker op.id_loc s pp.closed x in
  fprintf fmt "%a@ %a" pp.closed x (pp_print_opt_list ~sep:"@ " pp_op) ops

let pp_innfix pp fmt x1 op x2 =
  let op =
    pp_maybe_marker fmt op.id_loc;
    let open Ident in
    match sn_decode op.id_str with
    | SNinfix s -> s
    | _ -> failwith ("pp_innfix: "^op.id_str) in
  fprintf fmt "@[<hv 3>(%a@ %s %a)@]" pp.closed x1 op pp.closed x2

let pp_not pp fmt x =
  fprintf fmt "@[<h>not@ %a@]" pp.closed x

let pp_scope pp fmt qid x =
  fprintf fmt "@[<hv 2>%a.(%a)@]" pp_qualid qid pp.marked x

let pp_tuple pp fmt xs =
  let pp_xs = pp_print_list ~pp_sep:(pp_sep ",@ ") pp.closed in
  fprintf fmt "@[<hv 1>(%a)@]" pp_xs xs

let pp_field pp fmt (qid, x) =
  fprintf fmt "@[<hv 2>%a =@ %a@]" pp_qualid qid pp.closed x

let pp_fields pp =
  pp_print_list ~pp_sep:(pp_sep " ;@ ") (pp_field pp)

let pp_record pp fmt fs =
  fprintf fmt "@[@[<hv 2>{ %a@] }@]" (pp_fields pp) fs

let pp_update pp fmt x fs =
  fprintf fmt "@[<hv 2>{ %a with@ %a }@]" pp.closed x (pp_fields pp) fs

let rec pp_pty =
  let raw fmt = function
    | PTtyvar id ->
        fprintf fmt "'%a" pp_id id
    | PTtyapp (qid, []) ->
        pp_qualid fmt qid
    | PTtyapp (qid, ptys) ->
        let pp_ptys = pp_print_list ~pp_sep:(pp_sep " ") pp_pty.closed in
        fprintf fmt "@[<hv 2>%a@ %a@]" pp_qualid qid pp_ptys ptys
    | PTtuple ptys ->
        pp_tuple pp_pty fmt ptys
    | PTref _ptys ->
        failwith "Mlw_printer.pp_pty: PTref (must be handled by caller of pp_pty)"
    | PTarrow (pty1, pty2) ->
        fprintf fmt "@[<hv 2>%a ->@ %a@]" pp_pty.closed pty1 pp_pty.closed pty2
    | PTscope (qid, pty) ->
        pp_scope pp_pty fmt qid pty
    | PTparen pty ->
        fprintf fmt "(%a)" pp_pty.marked pty
    | PTpure pty ->
        fprintf fmt "{%a}" pp_pty.marked pty in
  let closed pty = pp_closed pty_closed raw pty in
  {marked= raw; closed}

let pp_opt_pty = pp_opt ~prefix:" : " pp_pty.marked

let pp_ghost fmt ghost =
  if ghost then pp_print_string fmt "ghost "

let pp_mutable fmt mutable_ =
  if mutable_ then pp_print_string fmt "mutable "

let pp_kind fmt = function
  | Expr.RKnone -> ()
  | Expr.RKfunc -> pp_print_string fmt ((* if unary then "constant " else *) "function ")
  | Expr.RKpred -> pp_print_string fmt "predicate "
  | Expr.RKlemma -> pp_print_string fmt "lemma "
  | Expr.RKlocal -> todo fmt "RKLOCAL" (* assert false? does not occur in parser *)

let opt_ref_pty = function
  | PTref [pty] -> "ref ", pty
  | pty -> "", pty

let pp_binder fmt (loc, opt_id, ghost, opt_pty) =
  let opt_ref, opt_pty = match Opt.map opt_ref_pty opt_pty with Some (ref, pty) -> ref, Some pty | None -> "", None in
  let pp_opt_id fmt opt_id = match opt_id with
    | None -> pp_print_string fmt "_"
    | Some id -> pp_id fmt id in
  if ghost || opt_pty <> None then
    let opt_id = Opt.map (remove_id_attr "mlw:reference_var") opt_id in
    fprintf fmt "%a(%a%s%a%a)" pp_maybe_marker loc pp_ghost ghost
      opt_ref pp_opt_id opt_id pp_opt_pty opt_pty
  else
    fprintf fmt "%a%a" pp_maybe_marker loc pp_opt_id opt_id

let pp_binders fmt =
  pp_print_opt_list ~prefix:" " pp_binder fmt

let pp_comma_binder fmt (loc, opt_id, ghost, opt_pty) =
  let opt_ref, opt_pty = match Opt.map opt_ref_pty opt_pty with Some (ref, pty) -> ref, Some pty | None -> "", None in
  fprintf fmt "%a%a%s%a%a" pp_maybe_marker loc pp_ghost ghost opt_ref (pp_opt ~def:"_" pp_id) opt_id
    (pp_opt ~prefix:" : " pp_pty.marked) opt_pty

let pp_comma_binders fmt =
  pp_print_opt_list ~prefix:" " ~sep:", " pp_comma_binder fmt

let pp_param fmt (loc, opt_id, ghost, pty) =
  let opt_ref, pty, opt_id = match pty with
    | PTref [pty] -> "ref ", pty, Opt.map (remove_id_attr "mlw:reference_var") opt_id
    | _ -> "", pty, opt_id in
  if ghost || opt_id <> None || opt_ref <> "" then
    let pp_id fmt id = fprintf fmt "%a:" pp_id id in
    fprintf fmt "%a(%a%s%a %a)" pp_maybe_marker loc pp_ghost ghost
      opt_ref (Pp.print_option pp_id) opt_id pp_pty.marked pty
  else
    fprintf fmt "%a%a" pp_maybe_marker loc pp_pty.closed pty

let pp_params fmt =
  pp_print_opt_list ~prefix:" " pp_param fmt

let pp_if pp fmt x1 x2 x3 =
  fprintf fmt "@[<v>@[<hv 2>if %a then@ %a@]@ @[<hv 2>else@ %a@]@]"
    pp.closed x1 pp.closed x2 pp.closed x3

let pp_cast pp fmt x pty =
  fprintf fmt "@[<hv 2>%a :@ %a@]" pp.closed x pp_pty.closed pty

let pp_attr pp fmt attr x =
  fprintf fmt "@[%a@ %a@]" pp_attr attr pp x

let rec pp_pty_mask fmt = function
  | PTtuple [], Ity.MaskVisible -> ()
  | pty, Ity.MaskVisible ->
      let opt_ref, pty = opt_ref_pty pty in
      fprintf fmt "%s%a" opt_ref pp_pty.marked pty
  | pty, Ity.MaskGhost -> fprintf fmt "ghost %a" pp_pty.closed pty
  | PTtuple ptys, Ity.MaskTuple ms ->
      fprintf fmt "(%a)" Pp.(print_list comma pp_pty_mask) (List.combine ptys ms)
  | _, Ity.MaskTuple _ -> assert false

let rec pp_pty_pat_mask ~closed fmt =
  let pp_vis_ghost fmt = function
    | Ity.MaskVisible -> ()
    | Ity.MaskGhost -> fprintf fmt "ghost "
    | Ity.MaskTuple _ -> fprintf fmt "TUPLE??" in
  let pp_aux fmt = function
    | PTtuple ptys, ({pat_desc= Ptuple ps}, Ity.MaskTuple ms) ->
        fprintf fmt "(%a)"
          Pp.(print_list comma (pp_pty_pat_mask ~closed:false))
          List.(combine ptys (combine ps ms))
    | PTtuple ptys, ({pat_desc= Pwild}, Ity.MaskTuple ms) ->
        fprintf fmt "(%a)" Pp.(print_list comma pp_pty_mask) (List.combine ptys ms)
    | pty, ({pat_desc= Pwild}, m) ->
        let opt_ref, pty = opt_ref_pty pty in
        fprintf fmt "%a%s%a" pp_vis_ghost m opt_ref pp_pty.closed pty
    | pty, ({pat_desc= Pvar id}, m) ->
        (* (ghost) x: t *)
        let opt_ref, pty = opt_ref_pty pty in
        let pp fmt = fprintf fmt "%a%s%a : %a" pp_vis_ghost m opt_ref pp_id id pp_pty.marked pty in
        fprintf fmt (if closed then "(%t)" else "%t") pp
    | _ -> assert false in
  function (pty, (pat, m)) ->
    fprintf fmt "@[%a%a@]" pp_maybe_marker pat.pat_loc pp_aux (pty, (pat, m))

let pp_opt_result fmt (opt_pty, p, m) = match opt_pty with
  | None -> ()
  | Some pty ->
      fprintf fmt " : %a" (pp_pty_pat_mask ~closed:true) (pty, (p, m))

let pp_exn fmt (id, pty, m) =
  let pp_space fmt = if pty <> PTtuple [] then fprintf fmt " " in
  fprintf fmt "@[<h>exception %a%t%a@]" pp_id id pp_space pp_pty_mask (pty, m)

let remove_witness_existence pre =
  let not_witness_existence = function
    | {term_desc= Tattr (ATstr {Ident.attr_string= "expl:witness existence"}, _)} -> false
    | _ -> true in
  List.filter not_witness_existence pre

let pp_let pp is_ref fmt (id, ghost, kind, x) =
  match is_ref x with
  | Some (loc, x) when List.exists (function ATstr a -> a.Ident.attr_string = "mlw:reference_var" | _ -> false) id.id_ats ->
      fprintf fmt "@[<hv 2>let %aref %a%a =@ %a%a@]" pp_ghost ghost
        pp_kind kind pp_id (remove_id_attr "mlw:reference_var" id)
        pp_maybe_marker loc pp.marked x
  | _ ->
      fprintf fmt "@[<hv 2>let %a%a%a =@ %a@]" pp_ghost ghost
        pp_kind kind pp_id id pp.marked x

let is_ref_expr = function
  | {expr_loc; expr_desc= Eapply ({expr_desc= Eref}, e2)} -> Some (expr_loc, e2)
  | _ -> None

let is_ref_pattern _ = None

let remove_term_attr s t = match t.term_desc with
  | Tattr (ATstr attr, t) when attr.Ident.attr_string = s -> t
  | _ -> t

let pp_clone_subst fmt = function
  | CSaxiom qid ->
      fprintf fmt "axiom %a" pp_qualid qid
  | CStsym (qid, args, pty) ->
      let pp_args = pp_print_opt_list ~every:" '" pp_id in
      fprintf fmt "type %a%a = %a" pp_qualid qid pp_args args pp_pty.marked pty
  | CSfsym (qid, qid') ->
      fprintf fmt "function %a = %a" pp_qualid qid pp_qualid qid'
  | CSpsym (qid, qid') ->
      fprintf fmt "predicate %a = %a" pp_qualid qid pp_qualid qid'
  | CSvsym (qid, qid') ->
      fprintf fmt "val %a = %a" pp_qualid qid pp_qualid qid'
  | CSxsym (qid, qid') ->
      if qid = qid' then
        fprintf fmt "exception %a" pp_qualid qid
      else
        fprintf fmt "exception %a = %a" pp_qualid qid pp_qualid qid'
  | CSprop Decl.Paxiom ->
      fprintf fmt "axiom ."
  | CSprop Decl.Plemma ->
      fprintf fmt "lemma ."
  | CSprop Decl.Pgoal ->
      fprintf fmt "goal ."
  | CSlemma qid ->
      fprintf fmt "lemma %a" pp_qualid qid
  | CSgoal qid ->
      fprintf fmt "goal %a" pp_qualid qid

let pp_substs = pp_print_opt_list ~prefix:" with@ " ~sep:",@ " pp_clone_subst

let pp_import fmt import = if import then pp_print_string fmt " import"

let pp_match pp pp_pattern fmt x cases xcases =
  let pp_reg_branch fmt (p, x) =
    fprintf fmt "@[<hv 2>%a ->@ %a@]" pp_pattern.marked p pp.marked x in
  let pp_exn_branch fmt (qid, p_opt, x) =
    fprintf fmt "@[<hv 2>%a%a -> %a@]" pp_qualid qid
      (pp_opt ~prefix:" " pp_pattern.marked) p_opt pp.marked x in
  fprintf fmt "@[<v>@[<hv 2>match %a with@]%a%a@ end@]"
    pp.marked x
    (pp_print_opt_list ~prefix:"@ | " ~sep:"@ | " pp_reg_branch) cases
    (pp_print_opt_list ~prefix:"@ | exception " ~sep:"@ | exception " pp_exn_branch) xcases

let pp_partial = pp_bool ~true_:"partial " ~false_:""

let term_hyp_name = function
  | {term_loc= loc; term_desc= Tattr (ATstr {Ident.attr_string= attr}, t)}
    when Strings.has_prefix "hyp_name:" attr ->
      Some loc, " " ^ Strings.remove_prefix "hyp_name:" attr, t
  | t -> None, "", t

let attr_equals at1 at2 =
  match at1, at2 with
  | ATstr at1, ATstr at2 ->
      at1.Ident.attr_string = at2.Ident.attr_string
  | ATpos loc1, ATpos loc2 ->
      Loc.equal loc1 loc2
  | _ -> false

let ident_equals id1 id2 =
  id1.id_str = id2.id_str && Lists.equal attr_equals id1.id_ats id2.id_ats

let rec qualid_equals qid1 qid2 =
  match qid1, qid2 with
  | Qident id1, Qident id2 ->
      ident_equals id1 id2
  | Qdot (qid1, id1), Qdot (qid2, id2) ->
      qualid_equals qid1 qid2 && ident_equals id1 id2
  | _ -> false

let pty_equals _ _ = true (* TODO *)

let rec pat_equals p1 p2 =
  match p1.pat_desc, p2.pat_desc with
  | Pwild, Pwild -> true
  | Pvar id1, Pvar id2 -> ident_equals id1 id2
  | Papp (qid1, pats1), Papp (qid2, pats2) ->
      qualid_equals qid1 qid2 && Lists.equal pat_equals pats1 pats2
  | Prec l1, Prec l2 ->
      let equals (qid1, pat1) (qid2, pat2) =
        qualid_equals qid1 qid2 && pat_equals pat1 pat2 in
      Lists.equal equals l1 l2
  | Ptuple pats1, Ptuple pats2 ->
      Lists.equal pat_equals pats1 pats2
  | Pas (p1, id1, g1), Pas (p2, id2, g2) ->
      pat_equals p1 p2 && ident_equals id1 id2 && g1 = g2
  | Por (p1, p1'), Por (p2, p2') ->
      pat_equals p1 p2 && pat_equals p1' p2'
  | Pcast (p1, pty1), Pcast (p2, pty2) ->
      pat_equals p1 p2 && pty_equals pty1 pty2
  | Pscope (qid1, p1), Pscope (qid2, p2) ->
      qualid_equals qid1 qid2 && pat_equals p1 p2
  | Pparen p1, Pparen p2 ->
      pat_equals p1 p2
  | Pghost p1, Pghost p2 ->
      pat_equals p1 p2
  | _ -> false

let rec pp_fun pp fmt = function
  | [], None, pat, Ity.MaskVisible, spec, e when pat.pat_desc = Pwild->
      fprintf fmt "@[<hv>@[<v2>%abegin@ %a%a@]@ end@]" pp_maybe_marker pat.pat_loc
        (pp_spec pat) spec pp.marked e
  | binders, opt_pty, pat, mask, spec, e ->
    fprintf fmt "@[<hv 2>fun %a%a%a ->@ @[%a@]@]" pp_binders binders
      pp_opt_result (opt_pty, pat, mask) (pp_spec pat) spec pp.marked e

and pp_let_fun pp fmt (loc, id, ghost, kind, (binders, opt_pty, pat, mask, spec, x)) =
  match binders, opt_pty, mask, pat with
  | [], None, Ity.MaskVisible, {pat_desc= Pwild} ->
      fprintf fmt "@[<hv>@[<v2>let %a%a%a%a = %a%abegin@ %a@ %a@]@ end@]"
        pp_ghost ghost pp_partial spec.sp_partial pp_kind kind pp_id id
        pp_maybe_marker loc pp_maybe_marker pat.pat_loc
        (pp_spec pat) {spec with sp_partial= false} pp.marked x
  | _ ->
      fprintf fmt "@[@[<v2>let %a%a%a%a%a%a%a%a@]@\n@[<v2>= %a@]@]"
        pp_ghost ghost pp_partial spec.sp_partial pp_kind kind pp_id id
        pp_binders binders pp_opt_result (opt_pty, pat, mask)
        pp_maybe_marker loc (pp_spec pat) {spec with sp_partial= false} pp.marked x

and pp_let_any fmt (loc, id, ghost, kind, (params, kind', opt_pty, pat, mask, spec)) =
  if kind' <> Expr.RKnone then
    todo fmt "LET-ANY kind<>RKnone" (* Concrete syntax? *)
  else
    match opt_pty, pat.pat_desc, mask, List.rev spec.sp_pre with
    | Some pty, Pwild, Ity.MaskVisible, {term_desc= Tattr (ATstr {Ident.attr_string= "expl:witness existence"}, _)} :: pre ->
        fprintf fmt "@[<hv>@[<hv2>let %a%a%a%a%a%a@ @]=@ @[<hv2>any %a %a@]@]"
          pp_maybe_marker loc pp_ghost ghost pp_partial spec.sp_partial pp_kind kind
          pp_id id pp_params params pp_pty.closed pty (pp_spec pat) {spec with sp_pre= List.rev pre}
    | _ ->
        fprintf fmt "@[<v2>val %a%a%a%a%a%a%a%a@]"
          pp_maybe_marker loc pp_ghost ghost pp_partial spec.sp_partial pp_kind kind pp_id id
          pp_params params pp_opt_result (opt_pty, pat, mask)
          (pp_spec pat) {spec with sp_partial= false}

and pp_fundef fmt (id, ghost, kind, binders, pty_opt, pat, mask, spec, e) =
  fprintf fmt "%a%a%a%a%a%a =@ %a"
    pp_ghost ghost pp_kind kind
    pp_id id pp_binders binders
    pp_opt_result (pty_opt, pat, mask)
    (pp_spec pat) spec pp_expr.marked e

and pp_expr =
  let raw fmt e =
    match e.expr_desc with
    | Eref ->
        pp_print_string fmt "ref"
    | Etrue ->
        pp_true fmt ()
    | Efalse ->
        pp_false fmt ()
    | Econst c ->
        pp_const fmt c
    | Eident qid ->
        pp_qualid fmt qid
    | Easref qid ->
        pp_qualid fmt qid
    | Eidapp (qid, es) ->
        pp_idapp pp_expr fmt qid es
    | Eapply (e1, e2) ->
        pp_apply pp_expr fmt e1 e2
    | Einfix (e, op, e') ->
        let rec collect op e = match e.expr_desc with
          | Einfix (e, op', e') -> (op, e) :: collect op' e'
          | _ -> [op, e] in
        pp_infix pp_expr fmt e (collect op e')
    | Einnfix (e1, op, e2) ->
        pp_innfix pp_expr fmt e1 op e2;
    | Elet (id, ghost, kind, e1, e2) -> (
        match e1.expr_desc with
        | Efun (binders, pty_opt, pat, mask, spec, e1') ->
            fprintf fmt "@[<v>%a in@ %a@]"
              (pp_let_fun pp_expr) (e1.expr_loc, id, ghost, kind, (binders, pty_opt, pat, mask, spec, e1'))
              pp_expr.marked e2
        | Eany (params, kind', pty_opt, pat, mask, spec) ->
            fprintf fmt "@[<v>%a in@ %a@]"
              pp_let_any (e1.expr_loc, id, ghost, kind, (params, kind', pty_opt, pat, mask, spec))
              pp_expr.marked e2
        | _ ->
            fprintf fmt "@[<hv>@[<v 2>%a@] in@ %a@]" (pp_let pp_expr is_ref_expr)
              (id, ghost, kind, e1) pp_expr.marked e2)
    | Erec (defs, e) ->
        let pp_fundefs = pp_print_list ~pp_sep:(pp_sep "@]@ @[<hv 2>with ") pp_fundef in
        fprintf fmt "@[<v>@[<v 2>let rec %a in@]@ %a@]" pp_fundefs defs pp_expr.marked e
    | Efun ([], None, ({pat_desc= Pwild} as pat), Ity.MaskVisible, spec,
            {expr_loc= loc; expr_desc=Etuple []}) ->
        fprintf fmt "@[<v>@[<v 2>%abegin@ %a%a@]@ end@]"
          pp_maybe_marker pat.pat_loc pp_maybe_marker loc (pp_spec pat) spec
    | Efun ([], None, ({pat_desc= Pwild} as pat), Ity.MaskVisible, spec, e) ->
        fprintf fmt "@[<v>@[<v 2>%abegin%a@ %a@]@ end@]" pp_maybe_marker pat.pat_loc
          (pp_spec pat) spec pp_expr.marked e
    | Efun (binders, opt_pty, pat, mask, spec, e) ->
        pp_fun pp_expr fmt (binders, opt_pty, pat, mask, spec, e)
    | Eany ([], _kind, Some pty, pat, mask, spec) -> (* TODO kind? *)
        let pat = if pat.pat_desc <> Pwild then pat else
            match spec.sp_post with
            | (_, (pat, _) :: _) :: _ -> pat
            | _ -> pat in
        let spec = {spec with sp_pre= remove_witness_existence spec.sp_pre} in
        fprintf fmt "@[<hv 2>any %a%a@]" (pp_pty_pat_mask ~closed:true) (pty, (pat, mask)) (pp_spec pat) spec
    | Eany _ ->
        todo fmt "EANY" (* assert false? *)
    | Etuple es ->
        pp_tuple pp_expr fmt es
    | Erecord fs ->
        pp_record pp_expr fmt fs
    | Eupdate (e, fs) ->
        pp_update pp_expr fmt e fs
    | Eassign [e1, oqid, e2] ->
        let pp_qid fmt = fprintf fmt ".%a" pp_qualid in
        fprintf fmt "@[<hv 2>%a%a <-@ %a@]" pp_expr.closed e1
          (Pp.print_option pp_qid) oqid pp_expr.closed e2
    | Eassign l ->
        let pp_lhs fmt = function
          | e, None, _ -> pp_expr.closed fmt e
          | e, Some qid, _ -> fprintf fmt "%a.%a" pp_expr.closed e pp_qualid qid in
        let pp_rhs fmt = function
          | _, _, e -> pp_expr.closed fmt e in
        fprintf fmt "@[<hv 2>(%a) <-@ (%a)@]" Pp.(print_list comma pp_lhs) l Pp.(print_list comma pp_rhs) l
    | Esequence _ ->
        let rec flatten e = match e.expr_desc with
          | Esequence (e1, e2) -> e1 :: flatten e2
          | _ -> [e] in
        pp_print_list ~pp_sep:(pp_sep ";@ ") pp_expr.closed fmt
          (flatten e)
    | Eif (e1, e2, e3) ->
        pp_if pp_expr fmt e1 e2 e3
    | Ewhile (e1, invs, vars, e2) ->
        fprintf fmt "@[<v>@[<v 2>while %a do%a%a@ %a@]@ done@]"
          pp_expr.marked e1 pp_variants vars pp_invariants invs pp_expr.marked e2
    | Eand (e1, e2) ->
        fprintf fmt "@[@[<hv 2>%a@]@ @[<hv 2> &&@ %a@]@]" pp_expr.closed e1 pp_expr.closed e2
    | Eor (e1, e2) ->
        fprintf fmt "@[@[<hv 2>%a@]@ @[<hv 2> ||@ %a@]@]" pp_expr.closed e1 pp_expr.closed e2
    | Enot e ->
        pp_not pp_expr fmt e
    | Ematch (e, [], xcases) ->
        let pp_xcase fmt (qid, opt_pat, e) =
          fprintf fmt "%a%a ->@ %a" pp_qualid qid
            (pp_opt ~prefix:" " pp_pattern.marked) opt_pat pp_expr.marked e in
        let pp_xcases = pp_print_list ~pp_sep:(pp_sep "@ | ") pp_xcase in
        fprintf fmt "@[<hv>@[<hv 2>try@ %a@]@ @[<hv 2>with@ %a@]@ end@]"
          pp_expr.marked e pp_xcases xcases
    | Ematch (e, cases, xcases) ->
        pp_match pp_expr pp_pattern fmt e cases xcases
    | Eabsurd ->
        pp_print_string fmt "absurd"
    | Epure t ->
        fprintf fmt "@[@[<hv 2>pure {@ %a@] }@]" pp_term.marked t
    | Eidpur qid ->
        fprintf fmt "@[<h>{ %a }@]" pp_qualid qid
    | Eraise (Qident {id_str="'Return"|"'Break"|"'Continue" as str; id_loc}, opt_arg) ->
        let keyword = match str with
          | "'Return" -> "return"
          | "'Break" -> "break"
          | "'Continue" -> "continue"
          | _ -> assert false in
        fprintf fmt "@[<hv 2>%a%s%a@]" pp_maybe_marker id_loc keyword
          (pp_opt ~prefix:" " pp_expr.closed) opt_arg
    | Eraise (qid, opt_arg) ->
        fprintf fmt "raise %a%a" pp_qualid qid (pp_opt ~prefix:" " pp_expr.closed) opt_arg
    | Eexn (id, pty, mask, e) ->
        fprintf fmt "@[%a in@ %a@]" pp_exn (id, pty, mask) pp_expr.marked e
    | Eoptexn (id, _mask, e)
      when List.exists (fun s -> Strings.ends_with id.id_str s) ["'Return"; "'Break"; "'Continue"]
        && marker id.id_loc = None -> (* Syntactic sugar *)
        (* TODO mask? *)
        pp_expr.marked fmt e
    | Eoptexn (id, mask, e) ->
        if mask <> Ity.MaskVisible then
          todo fmt "OPTEXN mask<>visible" (* concrete syntax? *)
        else
          fprintf fmt "@[<v>exception %a in@ %a@]" pp_id id pp_expr.marked e
    | Efor (id, start, dir, end_, invs, body) ->
        let dir = match dir with Expr.To -> "to" | Expr.DownTo -> "downto" in
        fprintf fmt "@[<v>@[<v 2>for %a = %a %s %a do%a@ %a@]@ done@]"
          pp_id id pp_expr.marked start dir pp_expr.marked end_
          pp_invariants invs pp_expr.marked body
    | Eassert (Expr.Assert, {term_loc= loc; term_desc=
          Tattr (ATstr {Ident.attr_string="hyp_name:Assert"}, t)}) ->
        fprintf fmt "@[<hv 2>assert {@ %a%a }@]" pp_maybe_marker loc pp_term.marked t
    | Eassert (Expr.Assume, {term_loc= loc; term_desc=
          Tattr (ATstr {Ident.attr_string="hyp_name:Assume"}, t)}) ->
        fprintf fmt "@[<hv 2>assume {@ %a%a }@]" pp_maybe_marker loc pp_term.marked t
    | Eassert (Expr.Check, {term_loc= loc; term_desc=
          Tattr (ATstr {Ident.attr_string="hyp_name:Check"}, t)}) ->
        fprintf fmt "@[<hv 2>check {@ %a%a }@]" pp_maybe_marker loc pp_term.marked t
    | Eassert (kind, t) ->
        let kind = match kind with
          | Expr.Assert -> "assert"
          | Expr.Assume -> "assume"
          | Expr.Check -> "check" in
        let oloc, s, t = term_hyp_name t in
        fprintf fmt "@[<hv 2>%s%s {@ %a%a }@]" kind s
          (Pp.print_option pp_maybe_marker) oloc pp_term.marked t
    | Escope (qid, e) ->
        pp_scope pp_expr fmt qid e
    | Elabel (id, e) ->
        fprintf fmt "@[<hv 2>label %a in@ %a@]" pp_id id pp_expr.marked e
    | Ecast (e, pty) ->
        pp_cast pp_expr fmt e pty
    | Eghost e ->
        fprintf fmt "ghost %a" pp_expr.closed e
    | Eattr (ATstr attr,e) when attr = Ident.funlit ->
        pp_e_funlit fmt e
    | Eattr (attr, e) ->
        let expr_closed = function
          | {expr_desc=Eattr _} -> true
          | e -> expr_closed e in
        pp_attr (pp_closed expr_closed pp_expr.marked) fmt attr e in
  let marked fmt e = pp_maybe_marked (fun e -> e.expr_loc) raw fmt e in
  let closed fmt = pp_closed expr_closed marked fmt in
  { marked; closed }

and pp_term =
  let raw fmt t =
    let pp_binop fmt op =
      let op_str = match op with
        | Dterm.DTand -> "/\\"
        | Dterm.DTand_asym -> "&&"
        | Dterm.DTor -> "\\/"
        | Dterm.DTor_asym -> "||"
        | Dterm.DTimplies -> "->"
        | Dterm.DTiff -> "<->"
        | Dterm.DTby -> "by"
        | Dterm.DTso -> "so" in
      pp_print_string fmt op_str in
    match t.term_desc with
    | Ttrue ->
        pp_true fmt ()
    | Tfalse ->
        pp_false fmt ()
    | Tconst c ->
        pp_const fmt c
    | Tident qid ->
        pp_qualid fmt qid
    | Tasref qid ->
        pp_asref fmt qid
    | Tidapp (qid, ts) ->
        pp_idapp pp_term fmt qid ts
    | Tapply (t1, t2) ->
        pp_apply pp_term fmt t1 t2
    | Tinfix (t, op, t') ->
        let rec collect op t = match t.term_desc with
          | Tinfix (t, op', t') -> (op, t) :: collect op' t'
          | _ -> [op, t] in
        pp_infix pp_term fmt t (collect op t')
    | Tinnfix (t1, op, t2) ->
        pp_innfix pp_term fmt t1 op t2;
    | Tbinop (t, op, t') ->
        let rec collect op t = match t.term_desc with
          | Tbinop (t, op', t') -> (op, t) :: collect op' t'
          | _ -> [op, t] in
        let pp_op fmt (op, t) = fprintf fmt "%a@ %a" pp_binop op pp_term.closed t in
        fprintf fmt "@[<hv2>%a@ %a@]" pp_term.closed t (pp_print_opt_list ~sep:"@ " pp_op) (collect op t')
    | Tbinnop (t1, op, t2) ->
        fprintf fmt "@[<hv 3>(%a %a@ %a)@]" pp_term.closed t1 pp_binop op pp_term.closed t2
    | Tnot t ->
        pp_not pp_term fmt t
    | Tif (t1, t2, t3) ->
        pp_if pp_term fmt t1 t2 t3
    | Tquant (quant, binders, triggers, t) ->
        let quant, sep, pp_binders = match quant with
          | Dterm.DTforall -> "forall", ".", pp_comma_binders
          | Dterm.DTexists -> "exists", ".", pp_comma_binders
          | Dterm.DTlambda -> "fun", "->", pp_binders in
        let pp_terms = pp_print_list ~pp_sep:(pp_sep ", ") pp_term.marked in
        let pp_triggers = pp_print_opt_list ~prefix:" [" ~sep:" | " ~suffix:"]" pp_terms in
        fprintf fmt "@[<hv 2>%s%a%a%s@ %a@]" quant pp_binders binders pp_triggers triggers sep pp_term.marked t
    | Tattr (ATstr attr, t) when attr = Ident.funlit ->
        pp_t_funlit fmt t
    | Tattr (attr, t) ->
        let term_closed t = match t.term_desc with
          | Tattr _ -> true
          | _ -> term_closed t in
        pp_attr (pp_closed term_closed pp_term.marked) fmt attr t
    | Tlet (id, t1, t2) ->
        fprintf fmt "@[<v>%a in@ %a@]" (pp_let pp_term is_ref_pattern)
          (id, false, Expr.RKnone, t1) pp_term.marked t2
    | Tcase (t, cases) ->
        pp_match pp_term pp_pattern fmt t cases []
    | Tcast (t, pty) ->
        pp_cast pp_term fmt t pty
    | Ttuple ts ->
        pp_tuple pp_term fmt ts
    | Trecord fs ->
        pp_record pp_term fmt fs
    | Tupdate (t, fs) ->
        pp_update pp_term fmt t fs
    | Tscope (qid, t) ->
        pp_scope pp_term fmt qid t
    | Tat (t, {id_str="'Old"; id_loc}) ->
        fprintf fmt "%aold %a" pp_maybe_marker id_loc pp_term.marked t
    | Tat (t, id) ->
        fprintf fmt "%a at %a" pp_term.marked t pp_id id in
  let marked fmt t = pp_maybe_marked (fun t -> t.term_loc) raw fmt t in
  let closed fmt = pp_closed term_closed marked fmt in
  { closed; marked }

and pp_t_funlit fmt t =
  let rec print_elems var fmt t = match t.term_desc with
    | Tif ({term_desc = Tinfix ({term_desc = Tident (Qident v)},_,t)},t2,t3)
         when var = v ->
       fprintf fmt "%a => %a;%a" pp_term.marked t
         pp_term.marked t2 (print_elems var) t3
    | Tidapp (Qident {id_str = "any function"},_) -> ()
    | _ -> fprintf fmt "_ => %a" pp_term.marked t in
  match t.term_desc with
  | Tquant (Dterm.DTlambda, [(_, Some var,_,_)], _, t) ->
     fprintf fmt "[|%a|]" (print_elems var) t
  | _ -> assert false (* should not happen *)

and pp_e_funlit fmt e =
  let rec substitute_and_print var e fmt l =
    match e.expr_desc, l with
    | Eif ({expr_desc = Einfix ({expr_desc = Eident (Qident v)},
                                _,
                                {expr_desc = Eident (Qident id1)})},
           {expr_desc = Eident (Qident id2)},
           e3),
      (id3,e4) :: (id4,e5) :: tl when var = v && id1 = id4 && id2 = id3 ->
       fprintf fmt "%a => %a;%a" pp_expr.marked e5
         pp_expr.marked e4 (substitute_and_print var e3) tl
    | Eident (Qident id1), [(id2,e)] when id1 = id2 ->
       fprintf fmt "_ => %a" pp_expr.marked e
    | Eident (Qident _), [] -> ()
    | _ -> assert false (* should not happen *) in
  let rec unfold_let acc fmt e = match e.expr_desc with
    | Elet (id,false,Expr.RKnone,e1,e2) ->
       unfold_let ((id,e1) :: acc) fmt e2
    | Efun ([(_,Some var,_,_)],_,_,_,_,e) ->
       substitute_and_print var e fmt acc
    | _ -> assert false (* should not happen *) in
  fprintf fmt "[|%a|]" (unfold_let []) e

and pp_variants fmt vs =
  let pp = match vs with [] | [_] -> pp_term.marked | _ -> pp_term.closed in
  let pp_variant fmt (t, qid_opt) =
    fprintf fmt "%a%a" pp t
      (pp_opt ~prefix:" with " pp_qualid) qid_opt in
  pp_print_opt_list ~prefix:"@ @[<hv2>variant {@ " ~sep:",@ " ~suffix:"@] }"
    pp_variant fmt vs

and pp_invariants fmt =
  let pp_invariant fmt t =
    let oloc, s, t = term_hyp_name t in
    let t = remove_term_attr "hyp_name:LoopInvariant"
        (remove_term_attr "hyp_name:TypeInvariant" t) in
    fprintf fmt "@[<hv 2>invariant%s {@ %a%a@] }" s
      (Pp.print_option pp_maybe_marker) oloc pp_term.marked t in
  pp_print_opt_list ~prefix:"@ " ~sep:"@ " pp_invariant fmt

(* result_pat is not printed, only used to print the post-conditions *)
and pp_spec result_pat fmt s =
  let pp_requires fmt t =
    let t = remove_term_attr "hyp_name:Requires" t in
    let oloc, s, t = term_hyp_name t in
    fprintf fmt "@[<hv>@[<hv2>requires%s { %a%a@]@ }@]" s
      (Pp.print_option pp_maybe_marker) oloc pp_term.marked t in
  let is_ensures pat = (* let f x : (p: ty) returns { p -> t }*)
    match result_pat.pat_desc, pat.pat_desc with
    | Pwild, Pvar id ->  id.id_str = "result"
    | _ -> pat_equals result_pat pat in
  let is_marked_id id = marker id.id_loc <> None in
  let rec is_marked_qid = function
    | Qident id -> is_marked_id id
    | Qdot (qid, id) -> is_marked_qid qid || is_marked_id id in
  let rec is_marked pat = marker pat.pat_loc <> None ||
    match pat.pat_desc with
    | Pwild -> false
    | Pvar id -> is_marked_id id
    | Papp (qid, ps) -> is_marked_qid qid || List.exists is_marked ps
    | Prec fs -> List.exists (fun (qid, p) -> is_marked_qid qid || is_marked p) fs
    | Ptuple ps -> List.exists is_marked ps
    | Pas (p1, id, _) -> is_marked p1 || is_marked_id id
    | Por (p1, p2) -> is_marked p1 || is_marked p2
    | Pcast (p, _) -> is_marked p
    | Pscope (qid, p) -> is_marked_qid qid || is_marked p
    | Pparen p -> is_marked p
    | Pghost p -> is_marked p in
  let pp_post fmt = function
    | loc, [pat, t] when is_ensures pat && not (is_marked pat) ->
        let t = remove_term_attr "hyp_name:Ensures" t in
        let oloc, s, t = term_hyp_name t in
        fprintf fmt "@ @[<hv 2>%aensures%s { %a%a@] }" pp_maybe_marker loc s
          (Pp.print_option pp_maybe_marker) oloc
          pp_term.marked t
    | loc, cases ->
        let pp_case fmt (p, t) =
          fprintf fmt "%a -> %a" pp_pattern.marked p pp_term.marked t in
        fprintf fmt "@ %areturns { %a }" pp_maybe_marker loc
          (pp_print_list ~pp_sep:(pp_sep "|") pp_case) cases in
  let pp_xpost fmt (loc, exn_cases) =
    let pp_exn_case fmt (qid, opt_pat_term) =
      let pp_opt_t fmt = function
        | Some (p, t) -> fprintf fmt " %a -> %a" pp_pattern.marked p pp_term.marked t
        | None -> () in
      fprintf fmt "@[<hv2>%a%a@]" pp_qualid qid pp_opt_t opt_pat_term in
    fprintf fmt "@[<hv2>%araises { %a }@]" pp_maybe_marker loc
      (pp_print_list ~pp_sep:(pp_sep "@ | ") pp_exn_case) exn_cases in
  let pp_alias fmt (t1, t2) =
    fprintf fmt "%a with %a" pp_term.marked t1 pp_term.marked t2 in
  pp_print_opt_list ~prefix:"@ @[<hv 2>reads { " ~suffix:"@] }" ~sep:",@ " pp_qualid fmt s.sp_reads;
  pp_print_opt_list ~prefix:"@ " ~sep:"@ " pp_requires fmt s.sp_pre;
  if s.sp_checkrw then
    fprintf fmt "@ @[<h>writes { %a }@]" (pp_print_opt_list ~sep:",@ " pp_term.marked) s.sp_writes
  else
    pp_print_opt_list ~prefix:"@ @[<hv 2>writes { " ~sep:",@ " ~suffix:"@] }" pp_term.marked fmt s.sp_writes;
  pp_print_list pp_post fmt s.sp_post;
  pp_print_opt_list ~prefix:"@ " ~sep:"@ " pp_xpost fmt s.sp_xpost;
  pp_print_opt_list ~prefix:"@ @[<hv 2>alias { " ~sep:",@ " ~suffix:"@] }" pp_alias fmt s.sp_alias;
  pp_variants fmt s.sp_variant;
  pp_bool ~true_:"@ diverges" fmt s.sp_diverge;
  pp_bool ~true_:"@ partial" fmt s.sp_partial

and pp_pattern =
  let pp_pattern_raw fmt p =
    match p.pat_desc with
    | Pwild ->
        pp_print_string fmt "_"
    | Pvar id ->
        pp_id fmt id
    | Papp (qid, args) ->
        pp_idapp pp_pattern fmt qid args
    | Prec fields ->
        let pp_field fmt (qid, pat) =
          fprintf fmt "%a = %a" pp_qualid qid pp_pattern.closed pat in
        fprintf fmt "{ %a }" (pp_print_list ~pp_sep:(pp_sep ";@ ") pp_field) fields
    | Ptuple ps ->
        pp_tuple pp_pattern fmt ps
    | Pas (p, id, ghost) ->
        fprintf fmt "@[<hv 2>%a@] as@ %a%a" pp_pattern.marked p pp_ghost ghost pp_id id
    | Por (p1, p2) ->
        fprintf fmt "%a | %a" pp_pattern.marked p1 pp_pattern.marked p2
    | Pcast (p, pty) ->
        pp_cast pp_pattern fmt p pty
    | Pscope (qid, p) ->
        pp_scope pp_pattern fmt qid p
    | Pparen p ->
        fprintf fmt "(%a)" pp_pattern.marked p
    | Pghost p ->
        fprintf fmt "@[<h>ghost@ %a@]" pp_pattern.marked p in
  let marked fmt p = pp_maybe_marked (fun p -> p.pat_loc) pp_pattern_raw fmt p in
  let closed fmt = pp_closed pattern_closed marked fmt in
  {marked; closed}

and pp_type_decl fmt d =
  let pp_def fmt = function
    | TDalias pty ->
        fprintf fmt " = %a" pp_pty.marked pty
    | TDrecord [] when d.td_vis = Abstract && d.td_mut = false ->
        ()
    | TDrecord fs ->
        let vis = match d.td_vis with
          | Public -> ""
          | Private -> "private "
          | Abstract -> "abstract " in
        let pp_field fmt f =
          fprintf fmt "@[<hv 2>%a%a%a%a :@ %a@]" pp_maybe_marker f.f_loc
            pp_mutable f.f_mutable pp_ghost f.f_ghost
            pp_id f.f_ident pp_pty.marked f.f_pty in
        let pp_fields = pp_print_list ~pp_sep:(pp_sep ";@ ") pp_field in
        fprintf fmt "@[<hv 2> = %s%a{@ %a@ }@]%a" vis
          pp_mutable d.td_mut pp_fields fs pp_invariants d.td_inv
    | TDalgebraic variants ->
        let pp_variant fmt (loc, id, params) =
          fprintf fmt "%a%a%a" pp_maybe_marker loc pp_id id
            pp_params params in
        fprintf fmt " = @,@[<v 2>  | %a@]"
          (pp_print_list ~pp_sep:(pp_sep "@,| ") pp_variant) variants
    | TDrange (i1, i2) ->
        fprintf fmt " = <range %s %s>" (BigInt.to_string i1) (BigInt.to_string i2)
    | TDfloat (i1, i2) ->
        fprintf fmt " = <float %d %d>" i1 i2 in
  fprintf fmt "%a%a%a%a%a"
    pp_maybe_marker d.td_loc pp_id d.td_ident
    (pp_print_opt_list ~every:" '" pp_id) d.td_params pp_def d.td_def
    (pp_print_opt_list ~prefix:"@ @[<hv 2>by {@ " ~sep:";@ " ~suffix:"@] }"
       (pp_field pp_expr)) d.td_wit

and pp_ind_decl fmt d =
  let pp_ind_decl_case fmt (loc, id, t) =
    fprintf fmt "%a%a : %a" pp_maybe_marker loc pp_id id pp_term.marked t in
  let pp_ind_decl_def =
    pp_print_list ~pp_sep:(pp_sep " | ") pp_ind_decl_case in
  fprintf fmt "%a%a%a = %a" pp_maybe_marker d.in_loc pp_id d.in_ident
    (pp_print_opt_list ~prefix:" " pp_param) d.in_params pp_ind_decl_def d.in_def

and pp_logic_decl fmt d =
    fprintf fmt "%a%a%a%a%a"
      pp_maybe_marker d.ld_loc pp_id d.ld_ident
      (pp_print_opt_list ~prefix:" " ~sep:" " pp_param) d.ld_params
      (pp_opt ~prefix:" : " pp_pty.marked) d.ld_type
      (pp_opt ~prefix:" =@ " pp_term.marked) d.ld_def

and pp_decl fmt = function
  | Dtype decls ->
      let pp_type_decls = pp_print_list ~pp_sep:(pp_sep "@]@ @[<v 2>with ") pp_type_decl in
      fprintf fmt "@[<v 2>type %a@]" pp_type_decls decls
  | Dlogic decls when List.for_all (fun d -> d.ld_type = None) decls -> (* predicates don't have an ld_type *)
      let pp_logic_decls =
        pp_print_list ~pp_sep:(pp_sep "@]@ @[<hv 2>with ") pp_logic_decl in
      fprintf fmt "@[<hv 2>predicate %a@]" pp_logic_decls decls
  | Dlogic decls when List.for_all (fun d -> d.ld_type <> None) decls -> (* functions have an ld_type *)
      let pp_logic_decls = pp_print_list ~pp_sep:(pp_sep "@]@ @[<hv 2>with ") pp_logic_decl in
      fprintf fmt "@[<hv 2>function %a@]" pp_logic_decls decls
  | Dlogic _ -> (* Mixed predicate/function declarations?? *)
      assert false
  | Dind (sign, decls) ->
      let keyword = match sign with
        | Decl.Ind -> "inductive"
        | Decl.Coind -> "coinductive" in
      let pp_ind_decls = pp_print_list ~pp_sep:(pp_sep "@]@ @[<hv 2>with ") pp_ind_decl in
      fprintf fmt "@[<hv 2>%s %a@]" keyword pp_ind_decls decls
  | Dprop (kind, id, t) ->
      let keyword = match kind with
        | Decl.Plemma -> "lemma"
        | Decl.Paxiom -> "axiom"
        | Decl.Pgoal -> "goal" in
      let id = remove_id_attr "useraxiom" id in
      fprintf fmt "@[<hv 2>%s %a:@ %a@]" keyword pp_id id pp_term.marked t
  | Dlet (id, ghost, kind, e) -> (
      match e.expr_desc with
      | Efun (binders, pty_opt, pat, mask, spec, e') ->
          pp_let_fun pp_expr fmt (e.expr_loc, id, ghost, kind, (binders, pty_opt, pat, mask, spec, e'))
      | Eany (params, kind', pty_opt, pat, mask, spec) ->
          pp_let_any fmt (e.expr_loc, id, ghost, kind, (params, kind', pty_opt, pat, mask, spec))
      | _ ->
          pp_let pp_expr is_ref_expr fmt (id, ghost, kind, e) )
  | Drec defs ->
      let pp_fundefs = pp_print_list ~pp_sep:(pp_sep "@]@ @[<hv 2>with ") pp_fundef in
      fprintf fmt "@[<v>@[<v 2>let rec %a@]@]" pp_fundefs defs
  | Dexn (id, pty, mask) ->
      fprintf fmt "%a" pp_exn (id, pty, mask)
  | Dmeta (ident, args) ->
      let pp_metarg fmt = function
        | Mty ty -> fprintf fmt "type %a" pp_pty.marked ty
        | Mfs qid -> fprintf fmt "function %a" pp_qualid qid
        | Mps qid -> fprintf fmt "predicate %a" pp_qualid qid
        | Max qid -> fprintf fmt "axiom %a" pp_qualid qid
        | Mlm qid -> fprintf fmt "lemma %a" pp_qualid qid
        | Mgl qid -> fprintf fmt "goal %a" pp_qualid qid
        | Mval qid -> fprintf fmt "val %a" pp_qualid qid
        | Mstr s -> fprintf fmt "%S" s
        | Mint i -> fprintf fmt "%d" i in
      let pp_args = pp_print_list ~pp_sep:(pp_sep ", ") pp_metarg in
      fprintf fmt "meta \"%a\" %a" pp_id ident pp_args args
  | Dcloneexport (qid, substs) ->
      fprintf fmt "@[<hv2>clone export %a%a@]" pp_qualid qid pp_substs substs
  | Duseexport qid ->
      fprintf fmt "@[<hv2>use export %a@]" pp_qualid qid
  | Dcloneimport (loc, import, qid, as_id, substs) ->
      fprintf fmt "@[<hv2>%aclone%a %a%a%a@]" pp_maybe_marker loc
        pp_import import pp_qualid qid (pp_opt ~prefix:" as " pp_id)
        as_id pp_substs substs
  | Duseimport (loc, import, binds) ->
      let pp_opt_id = pp_opt ~prefix:" as " pp_id in
      let pp_bind fmt (qid, opt_id) =
        fprintf fmt "%a%a" pp_qualid qid pp_opt_id opt_id in
      let pp_binds = pp_print_opt_list ~prefix:" " ~sep:", " pp_bind in
      fprintf fmt "@[<hv2>%ause%a %a@]" pp_maybe_marker loc pp_import import pp_binds binds
  | Dimport qid ->
      fprintf fmt "@[<hv2>import %a@]" pp_qualid qid
  | Dscope (loc, export, id, decls) ->
      let pp_export fmt = if export then pp_print_string fmt " export" in
      fprintf fmt "@[<v2>@[<v2>%ascope%t %a@ %a@]@,end@]"
        pp_maybe_marker loc pp_export pp_id id pp_decls decls

and pp_decls fmt decls =
  let rec aux ~is_first ~previous_was_module = function
    | [] -> []
    | decl :: decls ->
        let this_is_module = match decl with
          | Duseimport _ | Duseexport _ | Dcloneimport _
          | Dcloneexport _ | Dimport _ -> true
          | _ -> false in
        let prefix =
          if is_first || (previous_was_module && this_is_module)
          then []
          else [None] in
        prefix @ [Some decl] @ aux ~is_first:false
          ~previous_was_module:this_is_module decls in
  pp_print_list ~pp_sep:(pp_sep "@\n") (pp_opt pp_decl) fmt
    (aux ~is_first:true ~previous_was_module:false decls)

let pp_mlw_file fmt = function
  | Decls decls ->
      pp_decls fmt decls
  | Modules modules ->
      let pp_module fmt (id, decls) =
        fprintf fmt "@[<v0>@[<v2>module %a@ %a@]@ end@]" pp_id id pp_decls decls in
      let pp_modules = pp_print_list ~pp_sep:(pp_sep "@\n@\n") pp_module in
      fprintf fmt "@[<v>%a@]" pp_modules modules
