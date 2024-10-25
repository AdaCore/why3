(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Ptree

let debug_print_ids = Debug.register_flag "mlw_printer_print_ids"
    ~desc:"Print@ IDs@ of@ unique@ dummy@ locations"

type 'a printers = { marked: 'a Pp.pp; closed: 'a Pp.pp }

let marker = ref None

let dummy_filename = ""

let id_loc_counter = ref 0

let id_loc () =
  incr id_loc_counter;
  Loc.user_position dummy_filename !id_loc_counter 0 !id_loc_counter 0

let is_id_loc loc =
  let f,_,_,_,_ = Loc.get loc in
  f = dummy_filename

let only_ids =
  try Some (
      Wstdlib.Sint.of_list (List.map int_of_string
         (String.split_on_char ',' (Sys.getenv "WHY3MLWPRINTERIDS"))))
  with Not_found | Failure _ -> None

let print_only_id loc =
  let f,l,_,_,_ = Loc.get loc in
  f = dummy_filename && only_ids <> None && Wstdlib.Sint.mem l (Option.get only_ids)

let pp_loc_id fmt loc =
  if Debug.test_flag debug_print_ids || print_only_id loc then
    let f,bl,bc,_el,ec = Loc.get loc in
    if f = dummy_filename && bc = 0 && ec = 0 then fprintf fmt "(*%d*)" bl

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
    Loc.user_position "" !counter 0 !counter 0

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
      let filename, bline, bchar, eline, echar = Loc.get loc in
      fprintf fmt "[#%S %d %d %d %d]%a" filename bline bchar eline echar
        pp_maybe_marker loc

let pp_id ~attr fmt (id: ident) =
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
    | SNlcut s -> fprintf fmt "( [.._]%s )" s
    | SNrcut s -> fprintf fmt "( [_..]%s )" s  in
  if attr
  then
    fprintf fmt "%a%a%a"
      pp_maybe_marker id.id_loc
      pp_decode id.id_str
      (pp_print_opt_list ~prefix:" " pp_attr) id.id_ats
  else
    fprintf fmt "%a%a"
      pp_maybe_marker id.id_loc
      pp_decode id.id_str

let rec pp_qualid ~attr fmt = function
  | Qident id -> pp_id ~attr fmt id
  | Qdot (qid, id) ->
     fprintf fmt "@[<h>%a.%a@]" (pp_qualid ~attr) qid (pp_id ~attr) id

let pp_true fmt () =
  pp_print_string fmt "true"

let pp_false fmt () =
  pp_print_string fmt "false"

let pp_const fmt c =
  Constant.print_def fmt c

let pp_asref ~attr fmt qid =
  fprintf fmt "@[<h>&%a@]" (pp_qualid ~attr) qid

let pp_idapp ~attr pp fmt qid xs =
  match qid with
  | Qdot (_, id) -> (
      match Ident.sn_decode id.id_str, xs with
      | Ident.SNword s, [x] when 'a' <= s.[0] && s.[0] <= 'z' ->
         fprintf fmt "@[<hv2>%a%a.%a@]"
           pp_maybe_marker id.id_loc pp.closed x (pp_qualid ~attr) qid
      | _ ->
         let pp_args = pp_print_list ~pp_sep:pp_print_space pp.closed in
         fprintf fmt "@[<hv 3>%a@ %a@]" (pp_qualid ~attr) qid pp_args xs )
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

let pp_apply split_apply pp fmt x1 x2 =
  let rec flatten_applies sofar x =
    match split_apply x with
    | None -> x :: sofar
    | Some (x1, x2) -> flatten_applies (x2 :: sofar) x1 in
  fprintf fmt "@[<hv 2>%a@]"
    (pp_print_opt_list ~sep:"@ " pp.closed) (flatten_applies [x2] x1)

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

let pp_scope ~attr pp fmt qid x =
  fprintf fmt "@[<hv 2>%a.(%a)@]" (pp_qualid ~attr) qid pp.marked x

let pp_tuple pp fmt xs =
  let pp_xs = pp_print_list ~pp_sep:(pp_sep ",@ ") pp.closed in
  fprintf fmt "@[<hv 1>(%a)@]" pp_xs xs

let pp_field ~attr pp fmt (qid, x) =
  fprintf fmt "@[<hv 2>%a =@ %a@]" (pp_qualid ~attr) qid pp.closed x

let pp_fields ~attr pp =
  pp_print_list ~pp_sep:(pp_sep " ;@ ") (pp_field ~attr pp)

let pp_record ~attr pp fmt fs =
  fprintf fmt "@[@[<hv 2>{ %a@] }@]" (pp_fields ~attr pp) fs

let pp_update ~attr pp fmt x fs =
  fprintf fmt "@[<hv 2>{ %a with@ %a }@]"
    pp.closed x (pp_fields ~attr pp) fs

let rec pp_pty ~attr =
  let raw ~attr fmt = function
    | PTtyvar id ->
        fprintf fmt "'%a" (pp_id ~attr) id
    | PTtyapp (qid, []) ->
        pp_qualid ~attr fmt qid
    | PTtyapp (qid, ptys) ->
        let pp_ptys =
          pp_print_list ~pp_sep:(pp_sep " ")
            (pp_pty ~attr).closed
        in
        fprintf fmt "@[<hv 2>%a@ %a@]" (pp_qualid ~attr) qid pp_ptys ptys
    | PTtuple ptys ->
        pp_tuple (pp_pty ~attr) fmt ptys
    | PTref _ptys ->
        failwith "Mlw_printer.pp_pty: PTref (must be handled by caller of pp_pty)"
    | PTarrow (pty1, pty2) ->
        fprintf fmt "@[<hv 2>%a ->@ %a@]" (pp_pty ~attr).closed pty1
          (pp_pty ~attr).closed pty2
    | PTscope (qid, pty) ->
        pp_scope ~attr (pp_pty ~attr) fmt qid pty
    | PTparen pty ->
        fprintf fmt "(%a)" (pp_pty ~attr).marked pty
    | PTpure pty ->
        fprintf fmt "{%a}" (pp_pty ~attr).marked pty in
  let closed ~attr pty = pp_closed pty_closed (raw ~attr) pty in
  {marked= raw ~attr; closed = closed ~attr }

let pp_opt_pty ~attr = pp_opt ~prefix:" : " (pp_pty ~attr).marked

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

let pp_binder ~attr fmt (loc, opt_id, ghost, opt_pty) =
  let opt_ref, opt_pty = match Option.map opt_ref_pty opt_pty with Some (ref, pty) -> ref, Some pty | None -> "", None in
  let pp_opt_id fmt opt_id = match opt_id with
    | None -> pp_print_string fmt "_"
    | Some id -> pp_id ~attr fmt id in
  if ghost || opt_pty <> None then
    let opt_id = Option.map (remove_id_attr "mlw:reference_var") opt_id in
    fprintf fmt "%a(%a%s%a%a)" pp_maybe_marker loc pp_ghost ghost
      opt_ref pp_opt_id opt_id (pp_opt_pty ~attr) opt_pty
  else
    fprintf fmt "%a%a" pp_maybe_marker loc pp_opt_id opt_id

let pp_binders ~attr fmt =
  pp_print_opt_list ~prefix:" " (pp_binder ~attr) fmt

let pp_comma_binder ~attr fmt (loc, opt_id, ghost, opt_pty) =
  let opt_ref, opt_pty = match Option.map opt_ref_pty opt_pty with Some (ref, pty) -> ref, Some pty | None -> "", None in
  fprintf fmt "%a%a%s%a%a" pp_maybe_marker loc pp_ghost ghost opt_ref (pp_opt ~def:"_" (pp_id ~attr)) opt_id
    (pp_opt ~prefix:" : " (pp_pty ~attr).marked) opt_pty

let pp_comma_binders ~attr fmt =
  pp_print_opt_list ~prefix:" " ~sep:", " (pp_comma_binder ~attr) fmt

let pp_param ~attr fmt (loc, opt_id, ghost, pty) =
  let opt_ref, pty, opt_id = match pty with
    | PTref [pty] -> "ref ", pty, Option.map (remove_id_attr "mlw:reference_var") opt_id
    | _ -> "", pty, opt_id in
  if ghost || opt_id <> None || opt_ref <> "" then
    let pp_id fmt id = fprintf fmt "%a:" (pp_id ~attr) id in
    fprintf fmt "%a(%a%s%a %a)" pp_maybe_marker loc pp_ghost ghost
      opt_ref (Pp.print_option pp_id) opt_id (pp_pty ~attr).marked pty
  else
    fprintf fmt "%a%a" pp_maybe_marker loc (pp_pty ~attr).closed pty

let pp_params ~attr fmt =
  pp_print_opt_list ~prefix:" " (pp_param ~attr) fmt

let pp_if pp fmt x1 x2 x3 =
  fprintf fmt "@[<v>@[<hv 2>if %a then@ %a@]@ @[<hv 2>else@ %a@]@]"
    pp.closed x1 pp.closed x2 pp.closed x3

let pp_cast ~attr pp fmt x pty =
  fprintf fmt "@[<hv 2>%a :@ %a@]" pp.closed x (pp_pty ~attr).closed pty

let pp_attr pp fmt attr x =
  fprintf fmt "@[%a@ %a@]" pp_attr attr pp x

let rec pp_pty_mask ~attr fmt = function
  | PTtuple [], Ity.MaskVisible -> ()
  | pty, Ity.MaskVisible ->
      let opt_ref, pty = opt_ref_pty pty in
      fprintf fmt "%s%a" opt_ref (pp_pty ~attr).marked pty
  | pty, Ity.MaskGhost -> fprintf fmt "ghost %a" (pp_pty ~attr).closed pty
  | PTtuple ptys, Ity.MaskTuple ms ->
      fprintf fmt "(%a)" Pp.(print_list comma (pp_pty_mask ~attr)) (List.combine ptys ms)
  | _, Ity.MaskTuple _ -> assert false

let rec pp_pty_pat_mask ~attr ~closed fmt =
  let pp_vis_ghost fmt = function
    | Ity.MaskVisible -> ()
    | Ity.MaskGhost -> pp_print_string fmt "ghost "
    | Ity.MaskTuple _ -> fprintf fmt "TUPLE??" in
  let pp_aux fmt = function
    | PTtuple ptys, ({pat_desc = Ptuple ps; _}, Ity.MaskTuple ms) ->
        fprintf fmt "(%a)"
          Pp.(print_list comma (pp_pty_pat_mask ~attr ~closed:false))
          List.(combine ptys (combine ps ms))
    | PTtuple ptys, ({pat_desc= Pwild; _}, Ity.MaskTuple ms) ->
        fprintf fmt "(%a)" Pp.(print_list comma (pp_pty_mask ~attr)) (List.combine ptys ms)
    | pty, ({pat_desc= Pwild; _}, m) ->
        let opt_ref, pty = opt_ref_pty pty in
        fprintf fmt "%a%s%a" pp_vis_ghost m opt_ref (pp_pty ~attr).closed pty
    | pty, ({pat_desc= Pvar id; _}, m) ->
        (* (ghost) x: t *)
        let opt_ref, pty = opt_ref_pty pty in
        let pp fmt = fprintf fmt "%a%s%a : %a"
                       pp_vis_ghost m opt_ref
                       (pp_id ~attr) id (pp_pty ~attr).marked pty in
        fprintf fmt (if closed then "(%t)" else "%t") pp
    | _ -> assert false in
  function (pty, (pat, m)) ->
    fprintf fmt "@[%a%a@]" pp_maybe_marker pat.pat_loc pp_aux (pty, (pat, m))

let pp_opt_result ~attr fmt (opt_pty, p, m) = match opt_pty with
  | None -> ()
  | Some pty ->
      fprintf fmt " : %a" (pp_pty_pat_mask ~attr ~closed:true) (pty, (p, m))

let pp_exn ~attr fmt (id, pty, m) =
  let pp_space fmt = if pty <> PTtuple [] then pp_print_string fmt " " in
  fprintf fmt "@[<h>exception %a%t%a@]"
    (pp_id ~attr) id pp_space (pp_pty_mask ~attr) (pty, m)

let remove_witness_existence pre =
  let not_witness_existence = function
    | {term_desc= Tattr (ATstr {Ident.attr_string= "expl:witness existence"; _}, _); _}
      -> false
    | _ -> true in
  List.filter not_witness_existence pre

let pp_let ~attr pp is_ref fmt (id, ghost, kind, x) =
  match is_ref x with
  | Some (loc, x) when List.exists (function ATstr a -> a.Ident.attr_string = "mlw:reference_var" | _ -> false) id.id_ats ->
      fprintf fmt "@[<hv 2>let %aref %a%a =@ %a%a@]" pp_ghost ghost
        pp_kind kind (pp_id ~attr) (remove_id_attr "mlw:reference_var" id)
        pp_maybe_marker loc pp.marked x
  | _ ->
      fprintf fmt "@[<hv 2>let %a%a%a =@ %a@]" pp_ghost ghost
        pp_kind kind (pp_id ~attr) id pp.marked x

let is_ref_expr = function
  | {expr_loc; expr_desc= Eapply ({expr_desc= Eref;_}, e2)}
    -> Some (expr_loc, e2)
  | _ -> None

let is_ref_pattern _ = None

let remove_term_attr s t = match t.term_desc with
  | Tattr (ATstr attr, t) when attr.Ident.attr_string = s -> t
  | _ -> t

let pp_clone_subst ~attr fmt = function
  | CSaxiom qid ->
      fprintf fmt "axiom %a" (pp_qualid ~attr) qid
  | CStsym (qid, args, pty) ->
      let pp_args = pp_print_opt_list ~every:" '" (pp_id ~attr) in
      fprintf fmt "type %a%a = %a"
        (pp_qualid ~attr) qid pp_args args (pp_pty ~attr).marked pty
  | CSfsym (qid, qid') ->
      fprintf fmt "function %a = %a"
        (pp_qualid ~attr) qid (pp_qualid ~attr) qid'
  | CSpsym (qid, qid') ->
      fprintf fmt "predicate %a = %a"
        (pp_qualid ~attr) qid (pp_qualid ~attr) qid'
  | CSvsym (qid, qid') ->
      fprintf fmt "val %a = %a" (pp_qualid ~attr) qid (pp_qualid ~attr) qid'
  | CSxsym (qid, qid') ->
      if qid = qid' then
        fprintf fmt "exception %a" (pp_qualid ~attr) qid
      else
        fprintf fmt "exception %a = %a"
          (pp_qualid ~attr) qid (pp_qualid ~attr) qid'
  | CSprop Decl.Paxiom ->
      pp_print_string fmt "axiom ."
  | CSprop Decl.Plemma ->
      pp_print_string fmt "lemma ."
  | CSprop Decl.Pgoal ->
      pp_print_string fmt "goal ."
  | CSlemma qid ->
      fprintf fmt "lemma %a" (pp_qualid ~attr) qid
  | CSgoal qid ->
      fprintf fmt "goal %a" (pp_qualid ~attr) qid

let pp_substs ~attr =
  pp_print_opt_list ~prefix:" with@ " ~sep:",@ " (pp_clone_subst ~attr)

let pp_import fmt import = if import then pp_print_string fmt " import"

let pp_match ~attr pp pp_pattern fmt x cases xcases =
  let pp_reg_branch fmt (p, x) =
    fprintf fmt "@[<hv 2>%a ->@ %a@]" pp_pattern.marked p pp.marked x in
  let pp_exn_branch fmt (qid, p_opt, x) =
    fprintf fmt "@[<hv 2>%a%a -> %a@]" (pp_qualid ~attr) qid
      (pp_opt ~prefix:" " pp_pattern.marked) p_opt pp.marked x in
  fprintf fmt "@[<v>@[<hv 2>match %a with@]%a%a@ end@]"
    pp.marked x
    (pp_print_opt_list ~prefix:"@ | " ~sep:"@ | " pp_reg_branch) cases
    (pp_print_opt_list ~prefix:"@ | exception " ~sep:"@ | exception " pp_exn_branch) xcases

let pp_partial = pp_bool ~true_:"partial " ~false_:""

let term_hyp_name = function
  | {term_loc= loc; term_desc= Tattr (ATstr {Ident.attr_string= attr; _}, t)}
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

let rec pp_fun ~attr pp fmt = function
  | [], None, pat, Ity.MaskVisible, spec, e when pat.pat_desc = Pwild->
      fprintf fmt "@[<hv>@[<v2>%abegin@ %a%a@]@ end@]"
        pp_maybe_marker pat.pat_loc
        (pp_spec ~attr pat) spec pp.marked e
  | binders, opt_pty, pat, mask, spec, e ->
      fprintf fmt "@[<hv 2>fun %a%a%a ->@ @[%a@]@]" (pp_binders ~attr) binders
        (pp_opt_result ~attr) (opt_pty, pat, mask)
        (pp_spec ~attr pat) spec pp.marked e

and pp_let_fun ~attr pp fmt
    (loc, id, ghost, kind, (binders, opt_pty, pat, mask, spec, x)) =
  match binders, opt_pty, mask, pat with
  | [], None, Ity.MaskVisible, {pat_desc= Pwild; _} ->
      fprintf fmt "@[<hv>@[<v2>let %a%a%a%a = %a%abegin@ %a@ %a@]@ end@]"
        pp_ghost ghost pp_partial spec.sp_partial pp_kind kind (pp_id ~attr) id
        pp_maybe_marker loc pp_maybe_marker pat.pat_loc
        (pp_spec ~attr pat) {spec with sp_partial= false} pp.marked x
  | _ ->
      fprintf fmt "@[@[<v2>let %a%a%a%a%a%a%a%a@]@\n@[<v2>= %a@]@]"
        pp_ghost ghost pp_partial spec.sp_partial pp_kind kind (pp_id ~attr) id
        (pp_binders ~attr) binders (pp_opt_result ~attr) (opt_pty, pat, mask)
        pp_maybe_marker loc (pp_spec ~attr pat) {spec with sp_partial= false}
        pp.marked x

and pp_let_any ~attr fmt (loc, id, ghost, kind, (params, kind', opt_pty, pat, mask, spec)) =
  if kind' <> Expr.RKnone then
    todo fmt "LET-ANY kind<>RKnone" (* Concrete syntax? *)
  else
    match opt_pty, pat.pat_desc, mask, List.rev spec.sp_pre with
    | Some pty, Pwild, Ity.MaskVisible, {term_desc= Tattr (ATstr {Ident.attr_string= "expl:witness existence"; _}, _); _} :: pre ->
        fprintf fmt "@[<hv>@[<hv2>let %a%a%a%a%a%a@ @]=@ @[<hv2>any %a %a@]@]"
          pp_maybe_marker loc pp_ghost ghost pp_partial spec.sp_partial pp_kind kind
          (pp_id ~attr) id (pp_params ~attr) params (pp_pty ~attr).closed pty (pp_spec ~attr pat) {spec with sp_pre= List.rev pre}
    | _ ->
        fprintf fmt "@[<v2>val %a%a%a%a%a%a%a%a@]"
          pp_maybe_marker loc pp_ghost ghost pp_partial spec.sp_partial
          pp_kind kind (pp_id ~attr) id
          (pp_params ~attr) params (pp_opt_result ~attr) (opt_pty, pat, mask)
          (pp_spec ~attr pat) {spec with sp_partial= false}

and pp_fundef ~attr fmt
    (id, ghost, kind, binders, pty_opt, pat, mask, spec, e) =
  fprintf fmt "%a%a%a%a%a%a =@ %a"
    pp_ghost ghost pp_kind kind
    (pp_id ~attr) id (pp_binders ~attr) binders
    (pp_opt_result ~attr) (pty_opt, pat, mask)
    (pp_spec ~attr pat) spec (pp_expr ~attr).marked e

and pp_expr ~attr =
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
        pp_qualid ~attr fmt qid
    | Easref qid ->
        pp_qualid ~attr fmt qid
    | Eidapp (qid, es) ->
        pp_idapp ~attr (pp_expr ~attr) fmt qid es
    | Eapply (e1, e2) ->
        let split_apply e = match e.expr_desc with
            Eapply (e1, e2) -> Some (e1, e2) | _ -> None in
        pp_apply split_apply (pp_expr ~attr) fmt e1 e2
    | Einfix (e, op, e') ->
        let rec collect op e = match e.expr_desc with
          | Einfix (e, op', e') -> (op, e) :: collect op' e'
          | _ -> [op, e] in
        pp_infix (pp_expr ~attr) fmt e (collect op e')
    | Einnfix (e1, op, e2) ->
        pp_innfix (pp_expr ~attr) fmt e1 op e2;
    | Elet (id, ghost, kind, e1, e2) -> (
        match e1.expr_desc with
        | Efun (binders, pty_opt, pat, mask, spec, e1') ->
            fprintf fmt "@[<v>%a in@ %a@]"
              (pp_let_fun ~attr (pp_expr ~attr))
              (e1.expr_loc, id, ghost, kind,
               (binders, pty_opt, pat, mask, spec, e1'))
              (pp_expr ~attr).marked e2
        | Eany (params, kind', pty_opt, pat, mask, spec) ->
            fprintf fmt "@[<v>%a in@ %a@]"
              (pp_let_any ~attr) (e1.expr_loc, id, ghost, kind,
                                  (params, kind', pty_opt, pat, mask, spec))
              (pp_expr ~attr).marked e2
        | _ ->
            fprintf fmt "@[<hv>@[<v 2>%a@] in@ %a@]"
              (pp_let ~attr (pp_expr ~attr) is_ref_expr)
              (id, ghost, kind, e1) (pp_expr ~attr).marked e2)
    | Erec (defs, e) ->
        let pp_fundefs =
          pp_print_list ~pp_sep:(pp_sep "@]@ @[<hv 2>with ") (pp_fundef ~attr)
        in
        fprintf fmt "@[<v>@[<v 2>let rec %a in@]@ %a@]"
          pp_fundefs defs (pp_expr ~attr).marked e
    | Efun ([], None, ({pat_desc= Pwild; _} as pat), Ity.MaskVisible, spec,
            {expr_loc= loc; expr_desc=Etuple []}) ->
        fprintf fmt "@[<v>@[<v 2>%abegin@ %a%a@]@ end@]"
          pp_maybe_marker pat.pat_loc pp_maybe_marker loc
          (pp_spec ~attr pat) spec
    | Efun ([], None, ({pat_desc= Pwild; _} as pat), Ity.MaskVisible, spec, e) ->
        fprintf fmt "@[<v>@[<v 2>%abegin%a@ %a@]@ end@]" pp_maybe_marker pat.pat_loc
          (pp_spec ~attr pat) spec (pp_expr ~attr).marked e
    | Efun (binders, opt_pty, pat, mask, spec, e) ->
        pp_fun ~attr (pp_expr ~attr) fmt (binders, opt_pty, pat, mask, spec, e)
    | Eany ([], _kind, Some pty, pat, mask, spec) -> (* TODO kind? *)
        let pat = if pat.pat_desc <> Pwild then pat else
            match spec.sp_post with
            | (_, (pat, _) :: _) :: _ -> pat
            | _ -> pat in
        let spec = {spec with sp_pre= remove_witness_existence spec.sp_pre} in
        fprintf fmt "@[<hv 2>any %a%a@]" (pp_pty_pat_mask ~attr ~closed:true)
          (pty, (pat, mask)) (pp_spec ~attr pat) spec
    | Eany _ ->
        todo fmt "EANY" (* assert false? *)
    | Etuple es ->
        pp_tuple (pp_expr ~attr) fmt es
    | Erecord fs ->
        pp_record ~attr (pp_expr ~attr) fmt fs
    | Eupdate (e, fs) ->
        pp_update ~attr (pp_expr ~attr) fmt e fs
    | Eassign [e1, oqid, e2] ->
        let pp_qid fmt = fprintf fmt ".%a" (pp_qualid ~attr) in
        fprintf fmt "@[<hv 2>%a%a <-@ %a@]" (pp_expr ~attr).closed e1
          (Pp.print_option pp_qid) oqid (pp_expr ~attr).closed e2
    | Eassign l ->
        let pp_lhs fmt = function
          | e, None, _ -> (pp_expr ~attr).closed fmt e
          | e, Some qid, _ ->
              fprintf fmt "%a.%a" (pp_expr ~attr).closed e (pp_qualid ~attr) qid
        in
        let pp_rhs fmt = function
          | _, _, e -> (pp_expr ~attr).closed fmt e in
        fprintf fmt "@[<hv 2>(%a) <-@ (%a)@]" Pp.(print_list comma pp_lhs) l Pp.(print_list comma pp_rhs) l
    | Esequence _ ->
        let rec flatten e = match e.expr_desc with
          | Esequence (e1, e2) -> e1 :: flatten e2
          | _ -> [e] in
        pp_print_list ~pp_sep:(pp_sep ";@ ") (pp_expr ~attr).closed fmt
          (flatten e)
    | Eif (e1, e2, e3) ->
        pp_if (pp_expr ~attr) fmt e1 e2 e3
    | Ewhile (e1, invs, vars, e2) ->
        fprintf fmt "@[<v>@[<v 2>while %a do%a%a@ %a@]@ done@]"
          (pp_expr ~attr).marked e1 (pp_variants ~attr) vars
          (pp_invariants ~attr) invs (pp_expr ~attr).marked e2
    | Eand (e1, e2) ->
        fprintf fmt "@[@[<hv 2>%a@]@ @[<hv 2> &&@ %a@]@]"
          (pp_expr ~attr).closed e1 (pp_expr ~attr).closed e2
    | Eor (e1, e2) ->
        fprintf fmt "@[@[<hv 2>%a@]@ @[<hv 2> ||@ %a@]@]"
          (pp_expr ~attr).closed e1 (pp_expr ~attr).closed e2
    | Enot e ->
        pp_not (pp_expr ~attr) fmt e
    | Ematch (e, [], xcases) ->
        let pp_xcase fmt (qid, opt_pat, e) =
          fprintf fmt "%a%a ->@ %a" (pp_qualid ~attr) qid
            (pp_opt ~prefix:" " (pp_pattern ~attr).marked) opt_pat
            (pp_expr ~attr).marked e in
        let pp_xcases = pp_print_list ~pp_sep:(pp_sep "@ | ") pp_xcase in
        fprintf fmt "@[<hv>@[<hv 2>try@ %a@]@ @[<hv 2>with@ %a@]@ end@]"
          (pp_expr ~attr).marked e pp_xcases xcases
    | Ematch (e, cases, xcases) ->
        pp_match ~attr (pp_expr ~attr) (pp_pattern ~attr) fmt e cases xcases
    | Eabsurd ->
        pp_print_string fmt "absurd"
    | Epure t ->
        fprintf fmt "@[@[<hv 2>pure {@ %a@] }@]" (pp_term ~attr).marked t
    | Eidpur qid ->
        fprintf fmt "@[<h>{ %a }@]" (pp_qualid ~attr) qid
    | Eraise (qid, opt_arg) ->
        begin
          try
            match qid with
            | Qident id ->
                let keyword =
                  if id.id_str = Ptree_helpers.return_id then "return" else
                  if id.id_str = Ptree_helpers.break_id then "break" else
                  if id.id_str = Ptree_helpers.continue_id then "continue" else
                    raise Exit
                in
                fprintf fmt "@[<hv 2>%a%s%a@]" pp_maybe_marker id.id_loc keyword
                  (pp_opt ~prefix:" " (pp_expr ~attr).closed) opt_arg
            | _ -> raise Exit
          with Exit ->
            fprintf fmt "raise %a%a" (pp_qualid ~attr) qid
              (pp_opt ~prefix:" " (pp_expr ~attr).closed) opt_arg
        end
    | Eexn (id, pty, mask, e) ->
        fprintf fmt "@[%a in@ %a@]" (pp_exn ~attr) (id, pty, mask)
          (pp_expr ~attr).marked e
    | Eoptexn (id, _mask, e) when
        List.exists (fun s -> Strings.ends_with id.id_str s)
          Ptree_helpers.[return_id; break_id; continue_id]
        && marker id.id_loc = None ->
        (* Syntactic sugar *)
        (pp_expr ~attr).marked fmt e
    | Eoptexn (id, mask, e) ->
        if mask <> Ity.MaskVisible then
          todo fmt "OPTEXN mask<>visible" (* no possible concrete syntax *)
        else
          fprintf fmt "@[<v>exception %a in@ %a@]"
            (pp_id ~attr) id (pp_expr ~attr).marked e
    | Efor (id, start, dir, end_, invs, body) ->
        let dir = match dir with Expr.To -> "to" | Expr.DownTo -> "downto" in
        fprintf fmt "@[<v>@[<v 2>for %a = %a %s %a do%a@ %a@]@ done@]"
          (pp_id ~attr) id (pp_expr ~attr).marked start dir
          (pp_expr ~attr).marked end_
          (pp_invariants ~attr) invs (pp_expr ~attr).marked body
    | Eassert (Expr.Assert, {term_loc= loc; term_desc=
                                              Tattr (ATstr {Ident.attr_string="hyp_name:Assert";_}, t)}) ->
        fprintf fmt "@[<hv 2>assert {@ %a%a }@]"
          pp_maybe_marker loc (pp_term ~attr).marked t
    | Eassert (Expr.Assume, {term_loc= loc; term_desc=
                                              Tattr (ATstr {Ident.attr_string="hyp_name:Assume";_}, t)}) ->
        fprintf fmt "@[<hv 2>assume {@ %a%a }@]"
          pp_maybe_marker loc (pp_term ~attr).marked t
    | Eassert (Expr.Check, {term_loc= loc; term_desc=
                                             Tattr (ATstr {Ident.attr_string="hyp_name:Check";_}, t)}) ->
        fprintf fmt "@[<hv 2>check {@ %a%a }@]"
          pp_maybe_marker loc (pp_term ~attr).marked t
    | Eassert (kind, t) ->
        let kind = match kind with
          | Expr.Assert -> "assert"
          | Expr.Assume -> "assume"
          | Expr.Check -> "check" in
        let oloc, s, t = term_hyp_name t in
        fprintf fmt "@[<hv 2>%s%s {@ %a%a }@]" kind s
          (Pp.print_option pp_maybe_marker) oloc (pp_term ~attr).marked t
    | Escope (qid, e) ->
        pp_scope ~attr (pp_expr ~attr) fmt qid e
    | Elabel (id, e) ->
        fprintf fmt "@[<hv 2>label %a in@ %a@]"
          (pp_id ~attr) id (pp_expr ~attr).marked e
    | Ecast (e, pty) ->
        pp_cast ~attr (pp_expr ~attr) fmt e pty
    | Eghost e ->
        fprintf fmt "ghost %a" (pp_expr ~attr).closed e
    | Eattr (ATstr att,e) when att = Ident.funlit ->
        pp_e_funlit ~attr fmt e
    | Eattr (att, e) ->
        let expr_closed = function
          | {expr_desc=Eattr _;_} -> true
          | e -> expr_closed e in
        pp_attr (pp_closed expr_closed (pp_expr ~attr).marked) fmt att e in
  let marked fmt e = pp_maybe_marked (fun e -> e.expr_loc) raw fmt e in
  let closed fmt = pp_closed expr_closed marked fmt in
  { marked; closed }

and pp_term ~attr =
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
        pp_qualid ~attr fmt qid
    | Tasref qid ->
        pp_asref ~attr fmt qid
    | Tidapp (qid, ts) ->
        pp_idapp ~attr (pp_term ~attr) fmt qid ts
    | Tapply (t1, t2) ->
        let split_apply t = match t.term_desc with
            Tapply (t1, t2) -> Some (t1, t2) | _ -> None in
        pp_apply split_apply (pp_term ~attr) fmt t1 t2
    | Tinfix (t, op, t') ->
        let rec collect op t = match t.term_desc with
          | Tinfix (t, op', t') -> (op, t) :: collect op' t'
          | _ -> [op, t] in
        pp_infix (pp_term ~attr) fmt t (collect op t')
    | Tinnfix (t1, op, t2) ->
        pp_innfix (pp_term ~attr) fmt t1 op t2;
    | Tbinop (t, op, t') ->
        let rec collect op t = match t.term_desc with
          | Tbinop (t, op', t') -> (op, t) :: collect op' t'
          | _ -> [op, t] in
        let pp_op fmt (op, t) =
          fprintf fmt "%a@ %a" pp_binop op (pp_term ~attr).closed t in
        fprintf fmt "@[<hv2>%a@ %a@]" (pp_term ~attr).closed t
          (pp_print_opt_list ~sep:"@ " pp_op) (collect op t')
    | Tbinnop (t1, op, t2) ->
        fprintf fmt "@[<hv 3>(%a %a@ %a)@]"
          (pp_term ~attr).closed t1 pp_binop op (pp_term ~attr).closed t2
    | Tnot t ->
        pp_not (pp_term ~attr) fmt t
    | Tif (t1, t2, t3) ->
        pp_if (pp_term ~attr) fmt t1 t2 t3
    | Tquant (quant, binders, triggers, t) ->
        let quant, sep, pp_binders = match quant with
          | Dterm.DTforall -> "forall", ".", pp_comma_binders
          | Dterm.DTexists -> "exists", ".", pp_comma_binders
          | Dterm.DTlambda -> "fun", "->", pp_binders in
        let pp_terms =
          pp_print_list ~pp_sep:(pp_sep ", ")
            (pp_term ~attr).marked
        in
        let pp_triggers =
          pp_print_opt_list ~prefix:"@ [" ~sep:" | " ~suffix:"]"
            pp_terms
        in
        fprintf fmt "@[<hv 2>%s@[<hv>%a%a@]%s@ %a@]" quant (pp_binders ~attr)
          binders pp_triggers triggers sep (pp_term ~attr).marked t
    | Teps(id,ty,f) ->
        fprintf fmt "@[<hv 2>epsilon %a:%a.@ %a@]"
          (pp_id ~attr) id (pp_pty ~attr).marked ty (pp_term ~attr).marked f
    | Tattr (ATstr att, t) when att = Ident.funlit ->
        pp_t_funlit ~attr fmt t
    | Tattr (att, t) ->
        let term_closed t = match t.term_desc with
          | Tattr _ -> true
          | _ -> term_closed t in
        pp_attr (pp_closed term_closed (pp_term ~attr).marked) fmt att t
    | Tlet (id, t1, t2) ->
        fprintf fmt "@[<v>%a in@ %a@]"
          (pp_let ~attr (pp_term ~attr) is_ref_pattern)
          (id, false, Expr.RKnone, t1) (pp_term ~attr).marked t2
    | Tcase (t, cases) ->
        pp_match ~attr (pp_term ~attr) (pp_pattern ~attr) fmt t cases []
    | Tcast (t, pty) ->
        pp_cast ~attr (pp_term ~attr) fmt t pty
    | Ttuple ts ->
        pp_tuple (pp_term ~attr) fmt ts
    | Trecord fs ->
        pp_record ~attr (pp_term ~attr) fmt fs
    | Tupdate (t, fs) ->
        pp_update ~attr (pp_term ~attr) fmt t fs
    | Tscope (qid, t) ->
        pp_scope ~attr (pp_term ~attr) fmt qid t
    | Tat (t, {id_str="'Old"; id_loc;_}) ->
        fprintf fmt "%aold %a" pp_maybe_marker id_loc (pp_term ~attr).closed t
    | Tat (t, id) ->
        fprintf fmt "%a at %a" (pp_term ~attr).closed t (pp_id ~attr) id
  in
  let marked fmt t = pp_maybe_marked (fun t -> t.term_loc) raw fmt t in
  let closed fmt = pp_closed term_closed marked fmt in
  { closed; marked }

and pp_t_funlit ~attr fmt t =
  let rec print_elems var fmt t = match t.term_desc with
    | Tif ({term_desc = Tinfix ({term_desc = Tident (Qident v); _},_,t); _},
           t2,t3)
      when var = v ->
        fprintf fmt "%a => %a;%a" (pp_term ~attr).marked t
          (pp_term ~attr).marked t2 (print_elems var) t3
    | Tidapp (Qident {id_str = "any function"; _},_) -> ()
    | _ -> fprintf fmt "_ => %a" (pp_term ~attr).marked t in
  match t.term_desc with
  | Tquant (Dterm.DTlambda, [(_, Some var,_,_)], _, t) ->
      fprintf fmt "[|%a|]" (print_elems var) t
  | _ -> assert false (* should not happen *)

and pp_e_funlit ~attr fmt e =
  let rec substitute_and_print var e fmt l =
    match e.expr_desc, l with
    | Eif ({expr_desc = Einfix ({expr_desc = Eident (Qident v);_},
                                _,
                                {expr_desc = Eident (Qident id1);_})
           ;_},
           {expr_desc = Eident (Qident id2); _},
           e3),
      (id3,e4) :: (id4,e5) :: tl when var = v && id1 = id4 && id2 = id3 ->
        fprintf fmt "%a => %a;%a" (pp_expr ~attr).marked e5
          (pp_expr ~attr).marked e4 (substitute_and_print var e3) tl
    | Eident (Qident id1), [(id2,e)] when id1 = id2 ->
        fprintf fmt "_ => %a" (pp_expr ~attr).marked e
    | Eident (Qident _), [] -> ()
    | _ -> assert false (* should not happen *) in
  let rec unfold_let acc fmt e = match e.expr_desc with
    | Elet (id,false,Expr.RKnone,e1,e2) ->
        unfold_let ((id,e1) :: acc) fmt e2
    | Efun ([(_,Some var,_,_)],_,_,_,_,e) ->
        substitute_and_print var e fmt acc
    | _ -> assert false (* should not happen *) in
  fprintf fmt "[|%a|]" (unfold_let []) e

and pp_variants ~attr fmt vs =
  let pp = match vs with
      [] | [_] -> (pp_term ~attr).marked
    | _ -> (pp_term ~attr).closed in
  let pp_variant fmt (t, qid_opt) =
    fprintf fmt "%a%a" pp t
      (pp_opt ~prefix:" with " (pp_qualid ~attr)) qid_opt in
  pp_print_opt_list ~prefix:"@ @[<hv2>variant {@ " ~sep:",@ " ~suffix:"@] }"
    pp_variant fmt vs

and pp_invariants ~attr fmt =
  let pp_invariant fmt t =
    let oloc, s, t = term_hyp_name t in
    let t = remove_term_attr "hyp_name:LoopInvariant"
        (remove_term_attr "hyp_name:TypeInvariant" t) in
    fprintf fmt "@[<hv 2>invariant%s {@ %a%a@] }" s
      (Pp.print_option pp_maybe_marker) oloc (pp_term ~attr).marked t in
  pp_print_opt_list ~prefix:"@ " ~sep:"@ " pp_invariant fmt

(* result_pat is not printed, only used to print the post-conditions *)
and pp_spec ~attr result_pat fmt s =
  let pp_requires fmt t =
    let t = remove_term_attr "hyp_name:Requires" t in
    let oloc, s, t = term_hyp_name t in
    fprintf fmt "@[<hv>@[<hv2>requires%s { %a%a@]@ }@]" s
      (Pp.print_option pp_maybe_marker) oloc (pp_term ~attr).marked t in
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
          (pp_term ~attr).marked t
    | loc, cases ->
        let pp_case fmt (p, t) =
          fprintf fmt "%a -> %a"
            (pp_pattern ~attr).marked p (pp_term ~attr).marked t in
        fprintf fmt "@ %areturns { %a }" pp_maybe_marker loc
          (pp_print_list ~pp_sep:(pp_sep "|") pp_case) cases in
  let pp_xpost fmt (loc, exn_cases) =
    let pp_exn_case fmt (qid, opt_pat_term) =
      let pp_opt_t fmt = function
        | Some (p, t) ->
            fprintf fmt " %a -> %a" (pp_pattern ~attr).marked p
              (pp_term ~attr).marked t
        | None -> () in
      fprintf fmt "@[<hv2>%a%a@]" (pp_qualid ~attr) qid pp_opt_t opt_pat_term in
    fprintf fmt "@[<hv2>%araises { %a }@]" pp_maybe_marker loc
      (pp_print_list ~pp_sep:(pp_sep "@ | ") pp_exn_case) exn_cases in
  let pp_alias fmt (t1, t2) =
    fprintf fmt "%a with %a"
      (pp_term ~attr).marked t1
      (pp_term ~attr).marked t2 in
  pp_print_opt_list ~prefix:"@ @[<hv 2>reads { " ~suffix:"@] }" ~sep:",@ "
    (pp_qualid ~attr) fmt s.sp_reads;
  pp_print_opt_list ~prefix:"@ " ~sep:"@ " pp_requires fmt s.sp_pre;
  if s.sp_checkrw then
    fprintf fmt "@ @[<h>writes { %a }@]"
      (pp_print_opt_list ~sep:",@ " (pp_term ~attr).marked) s.sp_writes
  else
    pp_print_opt_list ~prefix:"@ @[<hv 2>writes { " ~sep:",@ " ~suffix:"@] }"
      (pp_term ~attr).marked fmt s.sp_writes;
  pp_print_list pp_post fmt s.sp_post;
  pp_print_opt_list ~prefix:"@ " ~sep:"@ " pp_xpost fmt s.sp_xpost;
  pp_print_opt_list ~prefix:"@ @[<hv 2>alias { " ~sep:",@ " ~suffix:"@] }" pp_alias fmt s.sp_alias;
  pp_variants ~attr fmt s.sp_variant;
  pp_bool ~true_:"@ diverges" fmt s.sp_diverge;
  pp_bool ~true_:"@ partial" fmt s.sp_partial

and pp_pattern ~attr =
  let pp_pattern_raw fmt p =
    match p.pat_desc with
    | Pwild ->
        pp_print_string fmt "_"
    | Pvar id ->
        pp_id ~attr fmt id
    | Papp (qid, args) ->
        pp_idapp ~attr (pp_pattern ~attr) fmt qid args
    | Prec fields ->
        let pp_field fmt (qid, pat) =
          fprintf fmt "%a = %a"
            (pp_qualid ~attr) qid (pp_pattern ~attr).closed pat in
        fprintf fmt "{ %a }" (pp_print_list ~pp_sep:(pp_sep ";@ ") pp_field) fields
    | Ptuple ps ->
        pp_tuple (pp_pattern ~attr) fmt ps
    | Pas (p, id, ghost) ->
        fprintf fmt "@[<hv 2>%a@] as@ %a%a"
          (pp_pattern ~attr).marked p pp_ghost ghost (pp_id ~attr) id
    | Por (p1, p2) ->
        fprintf fmt "%a | %a"
          (pp_pattern ~attr).marked p1 (pp_pattern ~attr).marked p2
    | Pcast (p, pty) ->
        pp_cast ~attr (pp_pattern ~attr) fmt p pty
    | Pscope (qid, p) ->
        pp_scope ~attr (pp_pattern ~attr) fmt qid p
    | Pparen p ->
        fprintf fmt "(%a)" (pp_pattern ~attr).marked p
    | Pghost p ->
        fprintf fmt "@[<h>ghost@ %a@]" (pp_pattern ~attr).marked p in
  let marked fmt p = pp_maybe_marked (fun p -> p.pat_loc) pp_pattern_raw fmt p in
  let closed fmt = pp_closed pattern_closed marked fmt in
  {marked; closed}

and pp_type_decl ~attr fmt d =
  let pp_def fmt = function
    | TDalias pty ->
        fprintf fmt " = %a" (pp_pty ~attr).marked pty
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
            (pp_id ~attr) f.f_ident (pp_pty ~attr).marked f.f_pty in
        let pp_fields = pp_print_list ~pp_sep:(pp_sep ";@ ") pp_field in
        fprintf fmt "@[<hv 2> = %s%a{@ %a@ }@]%a" vis
          pp_mutable d.td_mut pp_fields fs (pp_invariants ~attr) d.td_inv
    | TDalgebraic variants ->
        let pp_variant fmt (loc, id, params) =
          fprintf fmt "%a%a%a" pp_maybe_marker loc (pp_id ~attr) id
            (pp_params ~attr) params in
        fprintf fmt " = @,@[<v 2>  | %a@]"
          (pp_print_list ~pp_sep:(pp_sep "@,| ") pp_variant) variants
    | TDrange (i1, i2) ->
        fprintf fmt " = <range %s %s>" (BigInt.to_string i1) (BigInt.to_string i2)
    | TDfloat (i1, i2) ->
        fprintf fmt " = <float %d %d>" i1 i2 in
  fprintf fmt "%a%a%a%a%a"
    pp_maybe_marker d.td_loc (pp_id ~attr) d.td_ident
    (pp_print_opt_list ~every:" '" (pp_id ~attr)) d.td_params pp_def d.td_def
    (pp_opt ~prefix:"@ @[<hv 2>by@ " ~suffix:"@]" (pp_expr ~attr).closed) d.td_wit

and pp_ind_decl ~attr fmt d =
  let pp_ind_decl_case fmt (loc, id, t) =
    fprintf fmt "%a%a : %a"
      pp_maybe_marker loc (pp_id ~attr) id (pp_term ~attr).marked t in
  let pp_ind_decl_def =
    pp_print_list ~pp_sep:(pp_sep " | ") pp_ind_decl_case in
  fprintf fmt "%a%a%a = %a" pp_maybe_marker d.in_loc (pp_id ~attr) d.in_ident
    (pp_print_opt_list ~prefix:" " (pp_param ~attr)) d.in_params
    pp_ind_decl_def d.in_def

and pp_logic_decl ~attr fmt d =
  fprintf fmt "%a%a%a%a%a"
    pp_maybe_marker d.ld_loc (pp_id ~attr) d.ld_ident
    (pp_print_opt_list ~prefix:" " ~sep:" " (pp_param ~attr)) d.ld_params
    (pp_opt ~prefix:" : " (pp_pty ~attr).marked) d.ld_type
    (pp_opt ~prefix:" =@ " (pp_term ~attr).marked) d.ld_def

and pp_decl ?(attr=true) fmt = function
  | Dtype decls ->
      let pp_type_decls =
        pp_print_list ~pp_sep:(pp_sep "@]@ @[<v 2>with ") (pp_type_decl ~attr) in
      fprintf fmt "@[<v 2>type %a@]" pp_type_decls decls
  | Dlogic decls when List.for_all (fun d -> d.ld_type = None) decls ->
      (* predicates don't have an ld_type *)
      let pp_logic_decls =
        pp_print_list ~pp_sep:(pp_sep "@]@ @[<hv 2>with ")
          (pp_logic_decl ~attr) in
      fprintf fmt "@[<hv 2>predicate %a@]" pp_logic_decls decls
  | Dlogic decls when List.for_all (fun d -> d.ld_type <> None) decls ->
      (* functions have an ld_type *)
      let pp_logic_decls =
        pp_print_list ~pp_sep:(pp_sep "@]@ @[<hv 2>with ")
          (pp_logic_decl ~attr) in
      fprintf fmt "@[<hv 2>function %a@]" pp_logic_decls decls
  | Dlogic _ -> (* Mixed predicate/function declarations?? *)
      assert false
  | Dind (sign, decls) ->
      let keyword = match sign with
        | Decl.Ind -> "inductive"
        | Decl.Coind -> "coinductive" in
      let pp_ind_decls =
        pp_print_list ~pp_sep:(pp_sep "@]@ @[<hv 2>with ")
          (pp_ind_decl ~attr)
      in
      fprintf fmt "@[<hv 2>%s %a@]" keyword pp_ind_decls decls
  | Dprop (kind, id, t) ->
      let keyword = match kind with
        | Decl.Plemma -> "lemma"
        | Decl.Paxiom -> "axiom"
        | Decl.Pgoal -> "goal" in
      let id = remove_id_attr "useraxiom" id in
      fprintf fmt "@[<hv 2>%s %a:@ %a@]" keyword
        (pp_id ~attr) id (pp_term ~attr).marked t
  | Dlet (id, ghost, kind, e) -> (
      match e.expr_desc with
      | Efun (binders, pty_opt, pat, mask, spec, e') ->
          pp_let_fun ~attr (pp_expr ~attr) fmt
            (e.expr_loc, id, ghost, kind,
             (binders, pty_opt, pat, mask, spec, e'))
      | Eany (params, kind', pty_opt, pat, mask, spec) ->
          pp_let_any ~attr fmt
            (e.expr_loc, id, ghost, kind,
             (params, kind', pty_opt, pat, mask, spec))
      | _ ->
          pp_let ~attr (pp_expr ~attr) is_ref_expr fmt (id, ghost, kind, e) )
  | Drec defs ->
      let pp_fundefs =
        pp_print_list ~pp_sep:(pp_sep "@]@ @[<hv 2>with ")
          (pp_fundef ~attr) in
      fprintf fmt "@[<v>@[<v 2>let rec %a@]@]" pp_fundefs defs
  | Dexn (id, pty, mask) ->
      pp_exn ~attr fmt (id, pty, mask)
  | Dmeta (ident, args) ->
      let pp_metarg fmt = function
        | Mty ty -> fprintf fmt "type %a" (pp_pty ~attr).marked ty
        | Mfs qid -> fprintf fmt "function %a" (pp_qualid ~attr) qid
        | Mps qid -> fprintf fmt "predicate %a" (pp_qualid ~attr) qid
        | Max qid -> fprintf fmt "axiom %a" (pp_qualid ~attr) qid
        | Mlm qid -> fprintf fmt "lemma %a" (pp_qualid ~attr) qid
        | Mgl qid -> fprintf fmt "goal %a" (pp_qualid ~attr) qid
        | Mval qid -> fprintf fmt "val %a" (pp_qualid ~attr) qid
        | Mstr s -> fprintf fmt "%S" s
        | Mint i -> pp_print_int fmt i in
      let pp_args = pp_print_list ~pp_sep:(pp_sep ", ") pp_metarg in
      fprintf fmt "meta \"%a\" %a" (pp_id ~attr) ident pp_args args
  | Dcloneexport (_, qid, substs) ->
      fprintf fmt "@[<hv2>clone export %a%a@]"
        (pp_qualid ~attr) qid (pp_substs ~attr) substs
  | Duseexport (loc, qid) ->
      fprintf fmt "@[<hv2>%ause export %a@]" pp_maybe_marker loc
        (pp_qualid ~attr) qid
  | Dcloneimport (loc, import, qid, as_id, substs) ->
      fprintf fmt "@[<hv2>%aclone%a %a%a%a@]" pp_maybe_marker loc
        pp_import import (pp_qualid ~attr) qid
        (pp_opt ~prefix:" as " (pp_id ~attr)) as_id
        (pp_substs ~attr) substs
  | Duseimport (loc, import, binds) ->
      let pp_opt_id = pp_opt ~prefix:" as " (pp_id ~attr) in
      let pp_bind fmt (qid, opt_id) =
        fprintf fmt "%a%a" (pp_qualid ~attr) qid pp_opt_id opt_id in
      let pp_binds = pp_print_opt_list ~prefix:" " ~sep:", " pp_bind in
      fprintf fmt "@[<hv2>%ause%a%a@]" pp_maybe_marker loc pp_import import pp_binds binds
  | Dimport qid ->
      fprintf fmt "@[<hv2>import %a@]" (pp_qualid ~attr) qid
  | Dscope (loc, export, id, decls) ->
      let pp_export fmt = if export then pp_print_string fmt " export" in
      fprintf fmt "@[<v2>@[<v2>%ascope%t %a@ %a@]@,end@]"
        pp_maybe_marker loc pp_export (pp_id ~attr) id (pp_decls ~attr) decls

and pp_decls ~attr fmt decls =
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
  pp_print_list ~pp_sep:(pp_sep "@\n") (pp_opt (pp_decl ~attr)) fmt
    (aux ~is_first:true ~previous_was_module:false decls)

let pp_mlw_file ?(attr=true) fmt = function
  | Decls decls ->
      pp_decls ~attr fmt decls
  | Modules modules ->
      let pp_module fmt (id, decls) =
        fprintf fmt "@[<v0>@[<v2>module %a@ %a@]@ end@]"
          (pp_id ~attr) id (pp_decls ~attr) decls in
      let pp_modules = pp_print_list ~pp_sep:(pp_sep "@\n@\n") pp_module in
      fprintf fmt "@[<v>%a@]" pp_modules modules
