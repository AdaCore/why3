(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* TODO Use less parenthesis to deal with precedence and associativity *)

(* Test with
   $ why3 pp --output=mlw test.mlw > test1.mlw
   $ why3 pp --output=mlw test1.mlw > test2.mlw
   $ diff test1.mlw test2.mlw *)

open Format
open Ptree
open Ident

let pp_sep f fmt () =
  fprintf fmt f

let pp_opt ?(prefix:(unit, formatter, unit) format="") ?(suffix:(unit, formatter, unit) format="") pp fmt = function
  | None -> ()
  | Some x ->
    fprintf fmt prefix;
    pp fmt x;
    fprintf fmt suffix

let todo fmt str =
  fprintf fmt "<NOT IMPLEMENTED: %s>" str

let pp_print_opt_list ?(prefix:(unit, formatter, unit) format="") ?(sep:(unit, formatter, unit) format=" ") ?(suffix:(unit, formatter, unit) format="") pp fmt = function
  | [] -> ()
  | xs ->
    fprintf fmt prefix;
    pp_print_list ~pp_sep:(pp_sep sep) pp fmt xs;
    fprintf fmt suffix

let sanitize =
  let aux = function
    | c -> String.make 1 c in
  sanitizer aux aux

let pp_closed is_closed pp fmt x =
  if is_closed x then
    pp fmt x
  else
    fprintf fmt "(%a)" pp x

let expr_closed e = match e.expr_desc with
  | Eref | Etrue | Efalse | Econst _ | Eident _ | Etuple _ | Erecord _ | Eabsurd | Escope _ | Eidapp (_, []) | Ecast _ ->
      true
  | _ -> false

let term_closed t = match t.term_desc with
  | Ttrue | Tfalse | Tconst _ | Tident _ | Tupdate _ | Trecord _ | Ttuple _ | Tscope _ | Tidapp (_, []) | Tcast _ ->
      true
  | _ -> false

let pattern_closed p = match p.pat_desc with
  | Pwild | Pvar _ | Ptuple _ | Pparen _ | Pscope _ | Papp (_, []) | Pcast _ ->
      true
  | _ -> false

let pty_closed t = match t with
  | PTtyvar _ | PTtuple _ | PTscope _ | PTparen _ | PTpure _ | PTtyapp (_, []) ->
      true
  | _ -> false

let pp_id fmt id =
  pp_print_string fmt (sanitize id.id_str)

let pp_id' fmt id =
  match sn_decode id.id_str with
  | SNword s ->
    pp_print_string fmt (sanitize s)
  | SNinfix s ->
    fprintf fmt "(%s)" s
  | SNprefix s ->
    fprintf fmt "(%s)" s
  | SNtight s ->
    fprintf fmt "(%s)" s
  | SNget s ->
    fprintf fmt "([]%s)" s
  | SNset s ->
    fprintf fmt "([]%s<-)" s
  | SNupdate s ->
    fprintf fmt "([<-]%s)" s
  | SNcut s ->
    fprintf fmt "([..]%s)" s
  | SNlcut s ->
    fprintf fmt "([.._]%s)" s
  | SNrcut s ->
    fprintf fmt "([_..]%s)" s

let rec pp_qualid fmt = function
  | Qident id ->
      pp_id' fmt id
  | Qdot (qid, id) ->
      fprintf fmt "@[<h>%a.%a@]" pp_qualid qid pp_id' id

let pp_true fmt () =
  pp_print_string fmt "true"

let pp_false fmt () =
  pp_print_string fmt "false"

let pp_const fmt c =
  Constant.print_def fmt c

let pp_ident fmt id =
  pp_qualid fmt id

let pp_asref fmt qid =
  fprintf fmt "@[<h>&%a@]" pp_qualid qid

let pp_idapp pp closed fmt qid xs =
  let pp' = pp_closed closed pp in
  match qid with
  | Qident id ->
      (match sn_decode id.id_str, xs with
       | SNword s, _ ->
           let pp_args = pp_print_list ~pp_sep:(pp_sep "@ ") pp' in
           fprintf fmt "@[<hv 2>%s@ %a@]" s pp_args xs
       | SNinfix s, [x1; x2] ->
           fprintf fmt "@[<hv 2>%a@ %s %a@]" pp' x1 s pp' x2
       | SNprefix s, [x] -> (* TODO ??? *)
           fprintf fmt "@[<h>%s@ %a@]" s pp' x
       | SNtight s, [x] ->
           fprintf fmt "@[<h>%s@ %a@]" s pp' x
       | SNget s, [x1; x2] ->
           fprintf fmt "@[<hv 1>%a[%a]%s@]" pp' x1 pp x2 s
       | SNset s, [x1; x2; x3] ->
           fprintf fmt "@[<hv 1>%a[%a]%s <- %a@]" pp' x1 pp x2 s pp' x3
       | SNupdate s, [x1; x2; x3] ->
           fprintf fmt "@[<h>%a[%a <- %a]%s@]" pp' x1 pp x2 pp x3 s
       | SNcut s, [x] ->
           fprintf fmt "@[<h>%a[..]%s@]" pp' x s
       | SNlcut s, [x1; x2] ->
           fprintf fmt "@[<h>%a[.. %a]%s@]" pp' x1 pp x2 s
       | SNrcut s, [x1; x2] ->
           fprintf fmt "@[<h>%a[%a ..]%s@]" pp' x1 pp x2 s
       | _ -> failwith "pp_expr")
  | _ ->
      let pp_args = pp_print_list ~pp_sep:pp_print_space pp' in
      fprintf fmt "@[<hv 3>%a@ %a@]" pp_qualid qid pp_args xs

let pp_apply pp closed fmt x1 x2 =
  let pp = pp_closed closed pp in
  fprintf fmt "@[<hv 2>%a@ %a@]" pp x1 pp x2

let pp_infix pp closed fmt x1 op x2 =
  let pp' = pp_closed closed pp in
  let op =
    match sn_decode op.id_str with
    | SNinfix s -> s
    | _ -> failwith ("pp_infix: "^op.id_str) in
  fprintf fmt "@[<hv 3>%a@ %s %a@]" pp' x1 op pp' x2

let pp_not pp closed fmt x =
  let pp = pp_closed closed pp in
  fprintf fmt "@[<h>not@ %a@]" pp x

let pp_scope pp fmt qid x =
  fprintf fmt "@[<hv 2>%a.(%a)@]" pp_qualid qid pp x

let pp_tuple pp fmt xs =
  let pp_xs = pp_print_list ~pp_sep:(pp_sep ",@ ") pp in
  fprintf fmt "@[<hv 1>(%a)@]" pp_xs xs

let pp_field pp closed fmt (qid, x) =
  let pp = pp_closed closed pp in
  fprintf fmt "@[<hv 2>%a =@ %a@]" pp_qualid qid pp x

let pp_fields pp closed =
  pp_print_list ~pp_sep:(pp_sep " ;@ ") (pp_field pp closed)

let pp_record pp closed fmt fs =
  fprintf fmt "@[@[<hv 2>{ %a@] }@]" (pp_fields pp closed) fs

let pp_update pp closed fmt x fs =
  fprintf fmt "@[<hv 2>{ %a with@ %a }@]" pp x (pp_fields pp closed) fs

let rec pp_pty fmt =
  let pp_pty' = pp_closed pty_closed pp_pty in
  function
  | PTtyvar id ->
      pp_id fmt id
  | PTtyapp (qid, []) ->
      pp_qualid fmt qid
  | PTtyapp (qid, ptys) ->
      let pp_ptys = pp_print_list ~pp_sep:(pp_sep " ") pp_pty' in
      fprintf fmt "@[<hv 2>%a@ %a@]" pp_qualid qid pp_ptys ptys
  | PTtuple ptys ->
      pp_tuple pp_pty fmt ptys
  | PTref _ptys ->
      todo fmt "PTref _"
  | PTarrow (pty1, pty2) ->
      fprintf fmt "@[<hv 2>%a ->@ %a@]" pp_pty' pty1 pp_pty' pty2
  | PTscope (qid, pty) ->
      pp_scope pp_pty fmt qid pty
  | PTparen pty ->
      fprintf fmt "(%a)" pp_pty pty
  | PTpure pty ->
      fprintf fmt "{%a}" pp_pty pty

let pp_binder fmt (_, opt_id, ghost, opt_pty) =
  let pp_opt_id fmt = function
    | None ->
        pp_print_string fmt "_"
    | Some id ->
        pp_id fmt id in
  let ghost = if ghost then "ghost " else "" in
  match opt_pty with
  | Some pty ->
      fprintf fmt "(%s%a: %a)" ghost pp_opt_id opt_id pp_pty pty
  | None ->
      fprintf fmt "%s%a" ghost pp_opt_id opt_id

let pp_binders fmt =
  pp_print_opt_list ~prefix:" " pp_binder fmt

let pp_comma_binder fmt (_, opt_id, ghost, opt_pty) =
  let pp_opt_id fmt = function
    | None ->
        pp_print_string fmt "_"
    | Some id ->
        pp_id fmt id in
  let ghost = if ghost then "ghost " else "" in
  match opt_pty with
  | Some pty ->
      fprintf fmt "%s%a: %a" ghost pp_opt_id opt_id pp_pty pty
  | None ->
      fprintf fmt "%s%a" ghost pp_opt_id opt_id

let pp_comma_binders fmt =
  pp_print_opt_list ~prefix:" " ~sep:", " pp_comma_binder fmt

let pp_opt_pty fmt = function
  | None -> ()
  | Some pty -> fprintf fmt " : %a" pp_pty pty

let pp_param fmt (loc, opt_id, ghost, pty) =
  pp_binder fmt (loc, opt_id, ghost, Some pty)

let pp_params fmt =
  pp_print_opt_list ~prefix:" " pp_param fmt

let pp_if pp closed fmt x1 x2 x3 =
  let pp' = pp_closed closed pp in
  fprintf fmt "@[@[<hv 2>if %a@]@ @[<hv 2>then %a@]@ @[<hv 2>else %a@]@]" pp' x1 pp' x2 pp' x3

let pp_cast pp fmt x pty =
  fprintf fmt "(%a : %a)" pp x pp_pty pty

let pp_attr pp closed fmt attr x =
  let _pp' = pp_closed closed pp in
  match attr with
  | ATstr a ->
      fprintf fmt "@[[@%s]@ %a@]" a.attr_string pp x
  | ATpos loc ->
      let filename, line, bchar, echar = Loc.get loc in
      fprintf fmt "[# %S %d %d %d]" filename line bchar echar

let pp_exn fmt (id, pty, _mask) =
  (* TODO _mask *)
  let pp_pty fmt = function
    | PTtuple [] -> ()
    | pty -> fprintf fmt " %a" pp_pty pty in
  fprintf fmt "@[<h>exception %a%a@]" pp_id id pp_pty pty

let pp_match pp closed pp_pattern fmt x cases xcases =
  let pp' = pp_closed closed pp in
  let pp_pattern' = pp_closed pattern_closed pp_pattern in
  let pp_reg_branch fmt (p, x) =
    fprintf fmt "@[<hv 2>%a ->@ %a@]" pp_pattern' p pp' x in
  let pp_exn_branch fmt (qid, p_opt, x) =
    let pp_p_opt fmt = function
      | None -> ()
      | Some p -> fprintf fmt " %a" pp_pattern' p in
    fprintf fmt "@[<hv 2>%a%a -> %a@]" pp_qualid qid pp_p_opt p_opt pp' x in
  fprintf fmt "@[@[<hv 2>match@ %a@]@ @[<hv 2>with@ | %a%a@]@ end@]"
    pp x
    (pp_print_list ~pp_sep:(pp_sep "@ | ") pp_reg_branch) cases
    (pp_print_list ~pp_sep:(pp_sep "@ | exception ") pp_exn_branch) xcases

let pp_let pp fmt (id, ghost, _kind, x) =
  (* TODO kind *)
  let ghost = if ghost then " ghost" else "" in
  fprintf fmt "@[<hv 2>let%s %a =@ %a@]" ghost pp_id id pp x

let kind_suffix = function
  | Expr.RKnone
  | Expr.RKlocal -> ""
  | Expr.RKfunc -> " function"
  | Expr.RKpred -> " predicate"
  | Expr.RKlemma -> " lemma"

let ghost_suffix = function
  | true -> " ghost"
  | false -> ""

let pp_clone_subst fmt = function
  | CSaxiom qid ->
      fprintf fmt "axiom %a" pp_qualid qid
  | CStsym (qid, args, pty) ->
      let pp_args = pp_print_list ~pp_sep:(pp_sep " ") pp_id in
      fprintf fmt "type %a = %a%a" pp_qualid qid pp_pty pty pp_args args
  | CSfsym (qid, qid') ->
      fprintf fmt "function %a = %a" pp_qualid qid pp_qualid qid'
  | CSpsym (qid, qid') ->
      fprintf fmt "predicate %a = %a" pp_qualid qid pp_qualid qid'
  | CSvsym (qid, qid') ->
      fprintf fmt "val %a = %a" pp_qualid qid pp_qualid qid'
  | CSxsym _ -> todo fmt "CSxsym"
  | CSprop Decl.Paxiom -> fprintf fmt "axiom ."
  | CSprop _ -> todo fmt "CSprop"
  | CSlemma _ -> todo fmt "CSlemma"
  | CSgoal _ -> todo fmt "CSgoal"

let rec pp_fun pp fmt (binders, opt_pty, _pat, _mask, spec, e) =
  (* TODO _pat, _mask *)
  fprintf fmt "@[<hv 2>fun %a%a%a ->@ @[%a@]@]" pp_binders binders pp_opt_pty opt_pty pp_spec spec pp e

and pp_let_fun pp fmt (id, ghost, kind, (binders, opt_pty, _pat, _mask, spec, x)) =
  (* TODO _pat, _mask *)
  fprintf fmt "@[<hv 2>let%s%s %a%a%a%a =@ %a@]"
    (ghost_suffix ghost) (kind_suffix kind)
    pp_id id pp_binders binders pp_opt_pty opt_pty pp_spec spec pp x

and pp_let_any fmt (id, ghost, kind, (params, _kind', opt_pty, _pat, _mask, spec)) =
  (* TODO kind', mask, pat *)
  let pp_opt_pty fmt = function
    | None -> ()
    | Some pty -> fprintf fmt " : %a" pp_pty pty in
  fprintf fmt "@[<hv 2>val%s%s %a%a%a%a@]" (ghost_suffix ghost) (kind_suffix kind)
    pp_id id pp_params params pp_opt_pty opt_pty pp_spec spec

and pp_fundef fmt (id, ghost, kind, binders, pty_opt, _pat, _mask, spec, e) =
  (* TODO mask, pat *)
  fprintf fmt "@[<hv 2>";
  pp_print_string fmt (ghost_suffix ghost);
  pp_print_string fmt (kind_suffix kind);
  pp_id fmt id;
  pp_print_opt_list ~prefix:" " pp_binder fmt binders;
  (match pty_opt with
   | None -> ()
   | Some pty -> fprintf fmt " : %a" pp_pty pty);
  pp_spec fmt spec;
  fprintf fmt " =@ %a@]" pp_expr e;

and pp_variant fmt (t, qid_opt) =
  let pp_optwith fmt = function
    | None -> ()
    | Some qid -> fprintf fmt " with %a" pp_qualid qid in
  fprintf fmt "@[<hv 2>variant {@ %a%a }@]" pp_term t pp_optwith qid_opt

and pp_variants fmt =
  pp_print_opt_list ~prefix:"" ~sep:("@ ") ~suffix:"@ " pp_variant fmt

and pp_invariant fmt =
  fprintf fmt "@[<hv 2>invariant {@ %a }@]" pp_term

and pp_invariants fmt =
  pp_print_opt_list ~prefix:"" ~sep:"@ " ~suffix:"@ " pp_invariant fmt

and pp_expr' fmt =
  pp_closed expr_closed pp_expr fmt

and pp_expr fmt e =
  match e.expr_desc with
  | Eref ->
      pp_print_string fmt "ref"
  | Etrue ->
      pp_true fmt ()
  | Efalse ->
      pp_false fmt ()
  | Econst c ->
      pp_const fmt c
  (** lambda-calculus *)
  | Eident id ->
      pp_ident fmt id
  | Easref qid ->
      pp_asref fmt qid
  | Eidapp (qid, es) ->
      pp_idapp pp_expr expr_closed fmt qid es
  | Eapply (e1, e2) ->
      pp_apply pp_expr expr_closed fmt e1 e2
  | Einfix (e1, op, e2) ->
      pp_infix pp_expr expr_closed fmt e1 op e2
  | Einnfix _ ->
      todo fmt "Einnfix _"
  | Elet (id, ghost, kind, {expr_desc=Efun (binders, pty_opt, pat, mask, spec, e1)}, e2) ->
      (* TODO _pat *)
      fprintf fmt "@[<v>%a in@ %a@]"
        (pp_let_fun pp_expr) (id, ghost, kind, (binders, pty_opt, pat, mask, spec, e1))
        pp_expr' e2
  | Elet (id, ghost, kind, {expr_desc=Eany (params, kind', pty_opt, pat, mask, spec)}, e2) ->
      (* TODO _pat *)
      fprintf fmt "@[<v>%a in@ %a@]"
        pp_let_any (id, ghost, kind, (params, kind', pty_opt, pat, mask, spec))
        pp_expr' e2
  | Elet (id, ghost, kind, e1, e2) ->
      fprintf fmt "@[<v>%a in@ %a@]" (pp_let pp_expr) (id, ghost, kind, e1) pp_expr' e2
  | Erec (defs, e) ->
      let pp_fundefs =
        pp_print_list ~pp_sep:(pp_sep "@ and ") pp_fundef in
      fprintf fmt "@[<v>let rec %a in@ %a@]" pp_fundefs defs pp_expr' e
  | Efun (binders, opt_pty, pat, mask, spec, e) ->
      pp_fun pp_expr fmt (binders, opt_pty, pat, mask, spec, e)
  | Eany (_params, _kind, Some pty, _pat, _mask, spec) ->
      (* TODO _params *)
      fprintf fmt "@[<hv 2>any %a%a@]" pp_pty pty pp_spec spec
  | Eany _ ->
      todo fmt "Eany _"
  | Etuple es ->
      pp_tuple pp_expr fmt es
  | Erecord fs ->
      pp_record pp_expr expr_closed fmt fs
  | Eupdate (e, fs) ->
      pp_update pp_expr expr_closed fmt e fs
  | Eassign [e1, None, e2] ->
      fprintf fmt "@[<hv 2>%a <-@ %a@]" pp_expr' e1 pp_expr' e2
  | Eassign [e1, Some qid, e2] ->
      fprintf fmt "@[<hv 2>%a.%a <-@ %a@]" pp_expr' e1 pp_qualid qid pp_expr' e2
  | Eassign _ ->
      todo fmt "Eassign _"
  (** control *)
  | Esequence _ ->
      let rec flatten_sequence e = match e.expr_desc with
        | Esequence (e1, e2) ->
            e1 :: flatten_sequence e2
        | _ -> [e] in
      let es = flatten_sequence e in
      let pp = pp_print_list ~pp_sep:(pp_sep ";@ ") pp_expr' in
      fprintf fmt "@[<v 1>(%a)@]" pp es
  | Eif (e1, e2, e3) ->
      pp_if pp_expr expr_closed fmt e1 e2 e3
  | Ewhile (e1, invs, vars, e2) ->
    fprintf fmt "@[<v>@[<hv 2>while@ %a@] do@,  @[<hv>%a%a%a@]@,done@]"
      pp_expr e1 pp_variants vars pp_invariants invs pp_expr e2
  | Eand (e1, e2) ->
      fprintf fmt "@[@[<hv 2>%a@]@ @[<hv 2> &&@ %a@]@]" pp_expr' e1 pp_expr' e2
  | Eor (e1, e2) ->
      fprintf fmt "@[@[<hv 2>%a@]@ @[<hv 2> ||@ %a@]@]" pp_expr' e1 pp_expr' e2
  | Enot e ->
      pp_not pp_expr expr_closed fmt e
  | Ematch (e, [], xcases) ->
      let pp_xcase fmt (qid, opt_pat, e) =
        let pp_opt_pat =
          pp_opt ~prefix:" " pp_pattern in
        fprintf fmt "%a%a ->@ %a"
          pp_qualid qid pp_opt_pat opt_pat pp_expr' e in
      let pp_xcases =
        pp_print_list ~pp_sep:(pp_sep "@ | ") pp_xcase in
      fprintf fmt "@[<hv>@[<hv 2>try@ %a@]@ @[<hv 2>with@ %a@]@ end@]"
        pp_expr e pp_xcases xcases
  | Ematch (e, cases, xcases) ->
      pp_match pp_expr expr_closed pp_pattern fmt e cases xcases
  | Eabsurd ->
      pp_print_string fmt "absurd"
  | Epure t ->
      fprintf fmt "@[@[<hv 2>pure {@ %a@] }@]" pp_term t
  | Eidpur qid ->
      fprintf fmt "@[<h>{ %a }@]" pp_qualid qid
  | Eraise (Qident {id_str="'Return"|"'Break"|"'Continue" as str}, opt_arg) ->
      let pp_opt_arg fmt = function
        | None -> ()
        | Some e -> fprintf fmt " %a" pp_expr' e in
      let keyword =
        match str with
        | "'Return" -> "return"
        | "'Break" -> "break"
        | "'Continue" -> "continue"
        | _ -> assert false in
      fprintf fmt "@[hv 2%s%a@]" keyword pp_opt_arg opt_arg
  | Eoptexn ({id_str="'Return"|"'Break"|"'Continue"}, _mask, e) ->
      (* Syntactic sugar *)
      pp_expr fmt e
  | Eraise (qid, opt_arg) ->
      let pp_opt_arg fmt = function
        | None -> ()
        | Some e -> fprintf fmt " %a" pp_expr' e in
      fprintf fmt "raise %a%a" pp_qualid qid pp_opt_arg opt_arg
  | Eexn (id, pty, mask, e) ->
      fprintf fmt "@[%a in@ %a@]" pp_exn (id, pty, mask) pp_expr e
  | Eoptexn (id, _mask, e) ->
      (* TODO mask *)
      fprintf fmt "@[<v>exception %a in@ %a@]" pp_id id pp_expr e
  | Efor (id, start, dir, end_, invs, body) ->
      let dir = match dir with Expr.To -> "to" | Expr.DownTo -> "downto" in
      let pp_invs =
        let pp_inv fmt =
          fprintf fmt "@[<hv 2>invariant { %a }@]" pp_term in
        pp_print_list ~pp_sep:(pp_sep "@ ") pp_inv in
      fprintf fmt "@[@[<v 2>for %a = %a %s %a do@ %a%a@]@ done@]"
        pp_id id pp_expr start dir pp_expr end_ pp_invs invs pp_expr body
  (** annotations *)
  | Eassert (Expr.Assert, {term_desc=Tattr (ATstr {attr_string="hyp_name:Assert"}, t)}) ->
      fprintf fmt "@[<hv 2>assert {@ %a }@]" pp_term t
  | Eassert (Expr.Assume, {term_desc=Tattr (ATstr {attr_string="hyp_name:Assume"}, t)}) ->
      fprintf fmt "@[<hv 2>assume {@ %a }@]" pp_term t
  | Eassert (Expr.Check, {term_desc=Tattr (ATstr {attr_string="hyp_name:Check"}, t)}) ->
      fprintf fmt "@[<hv 2>check {@ %a }@]" pp_term t
  | Eassert (kind, t) ->
      let pp_assert_kind fmt kind =
        pp_print_string fmt
          (match kind with
           | Expr.Assert -> "assert"
           | Expr.Assume -> "assume"
           | Expr.Check -> "check") in
      fprintf fmt "@[<hv 2>%a {@ %a }@]" pp_assert_kind kind pp_term t
  | Escope (qid, e) ->
      pp_scope pp_expr fmt qid e
  | Elabel (id, e) ->
      fprintf fmt "@[<hv 2>label %a in@ %a@]" pp_id id pp_expr e
  | Ecast (e, pty) ->
      pp_cast pp_expr fmt e pty
  | Eghost e ->
      fprintf fmt "ghost %a" pp_expr e
  | Eattr (attr, e) ->
      pp_attr pp_expr expr_closed fmt attr e

and pp_term' fmt =
  pp_closed term_closed pp_term fmt

and pp_term fmt t =
  let pp_binop fmt op =
    pp_print_string fmt
      (match op with
       | Dterm.DTand -> "/\\"
       | Dterm.DTand_asym -> "&&"
       | Dterm.DTor -> "\\/"
       | Dterm.DTor_asym -> "||"
       | Dterm.DTimplies -> "->"
       | Dterm.DTiff -> "<->"
       | Dterm.DTby -> "by"
       | Dterm.DTso -> "so") in
  match t.term_desc with
  | Ttrue ->
      pp_true fmt ()
  | Tfalse ->
      pp_false fmt ()
  | Tconst c ->
      pp_const fmt c
  | Tident id ->
      pp_ident fmt id
  | Tasref qid ->
      pp_asref fmt qid
  | Tidapp (qid, ts) ->
      pp_idapp pp_term term_closed fmt qid ts
  | Tapply (t1, t2) ->
      pp_apply pp_term term_closed fmt t1 t2
  | Tinfix (t1, op, t2) ->
      pp_infix pp_term term_closed fmt t1 op t2
  | Tinnfix _ ->
      todo fmt "Tinnfix _"
  | Tbinop (t1, op, t2)
  | Tbinnop (t1, op, t2) ->
      fprintf fmt "@[<hv 2>%a %a@ %a@]" pp_term' t1 pp_binop op pp_term' t2
  | Tnot t ->
      pp_not pp_term term_closed fmt t
  | Tif (t1, t2, t3) ->
      pp_if pp_term term_closed fmt t1 t2 t3
  | Tquant (quant, binders, [], t) ->
      let quant = match quant with Dterm.DTforall -> "forall" | Dterm.DTexists -> "exists" | Dterm.DTlambda -> "lambda" in
      fprintf fmt "@[<hv 2>%s%a.@ %a@]" quant pp_comma_binders binders pp_term t
  | Tquant (_, _, _::_, _) ->
      todo fmt "Tquant (_, _, _::_, _)"
  | Tattr (attr, t) ->
      pp_attr pp_term term_closed fmt attr t
  | Tlet (id, t1, t2) ->
      fprintf fmt "@[<v>%a in@ %a@]" (pp_let pp_term) (id, false, ((**)), t1) pp_term t2
  | Tcase (t, cases) ->
      pp_match pp_term term_closed pp_pattern fmt t cases []
  | Tcast (t, pty) ->
      pp_cast pp_term fmt t pty
  | Ttuple ts ->
      pp_tuple pp_term fmt ts
  | Trecord fs ->
      pp_record pp_term term_closed fmt fs
  | Tupdate (t, fs) ->
      pp_update pp_term term_closed fmt t fs
  | Tscope (qid, t) ->
      pp_scope pp_term fmt qid t
  | Tat (t, {id_str="'Old"}) ->
      fprintf fmt "old %a" pp_term' t
  | Tat (t, id) ->
      fprintf fmt "%a at %a" pp_term' t pp_id id

and pp_spec fmt s =
  if s.sp_reads <> [] then
    fprintf fmt "@ reads { %a }" (pp_print_list ~pp_sep:(pp_sep ", ") pp_qualid) s.sp_reads;
  let pp_aux keyword t =
    fprintf fmt "@ %s { %a }" keyword pp_term t in
  List.iter (pp_aux "requires") s.sp_pre;
  List.iter (pp_aux "writes") s.sp_writes;
  let pp_post = function
    | _, [{pat_desc=Pvar {id_str="result"}}, t] ->
        fprintf fmt "@ ensures { %a }" pp_term t
    | _, cases ->
        let pp_case fmt (p, t) =
          fprintf fmt "%a -> %a" pp_pattern' p pp_term' t in
        fprintf fmt "@ returns { %a }"
          (pp_print_list ~pp_sep:(pp_sep "|") pp_case) cases in
  List.iter pp_post s.sp_post;
  let pp_xpost fmt _ =
    todo fmt "sp_xpost" in
  List.iter (fun x -> fprintf fmt "@ %a" pp_xpost x) s.sp_xpost;
  let pp_alias _ =
    todo fmt "sp_alias" in
  List.iter pp_alias s.sp_alias;
  List.iter (fun v -> fprintf fmt "@ %a" pp_variant v) s.sp_variant;
  (* TODO s.sp_checkrw *)
  if s.sp_diverge then
    pp_print_string fmt "@ diverge";
  if s.sp_partial then
    pp_print_string fmt "@ partial";

and pp_pattern' fmt =
  pp_closed pattern_closed pp_pattern fmt

and pp_pattern fmt p =
  match p.pat_desc with
  | Pwild ->
      pp_print_string fmt "_"
  | Pvar id ->
      pp_id fmt id
  | Papp (qid, args) ->
      pp_idapp pp_pattern pattern_closed fmt qid args
  | Prec _ ->
      todo fmt "Prec _"
  | Ptuple ps ->
      pp_tuple pp_pattern fmt ps
  | Pas (p, id, ghost) ->
      let pp_ghost fmt = function
        | false -> ()
        | true -> pp_print_string fmt " ghost" in
      fprintf fmt "@[<hv 2>%a@] as@ %a%a" pp_pattern' p pp_id id pp_ghost ghost
  | Por (p1, p2) ->
      fprintf fmt "%a | %a" pp_pattern' p1 pp_pattern' p2
  | Pcast (p, pty) ->
      pp_cast pp_pattern fmt p pty
  | Pscope (qid, p) ->
      pp_scope pp_pattern fmt qid p
  | Pparen p ->
      fprintf fmt "(%a)" pp_pattern p
  | Pghost p ->
      fprintf fmt "[@<h>ghost@ %a@]" pp_pattern' p

and pp_type_decl fmt d =
  let pp_def fmt = function
    | TDalias pty ->
        pp_pty fmt pty
    | TDrecord [] when d.td_vis = Abstract && d.td_mut = false ->
        ()
    | TDrecord fs ->
        let pp_vis fmt vis =
          pp_print_string fmt
            (match vis with
             | Public -> ""
             | Private -> "private "
             | Abstract -> "abstract ") in
        let pp_mut fmt mut =
          pp_print_string fmt
            (if mut then "mutable " else "") in
        let pp_field fmt f =
          let mutable_ = if f.f_mutable then "mutable " else "" in
          let ghost = if f.f_ghost then "ghost " else "" in
          fprintf fmt "%s%s%a : %a" mutable_ ghost pp_id f.f_ident pp_pty f.f_pty in
        let pp_fields = pp_print_list ~pp_sep:(pp_sep " ;@,") pp_field in
        fprintf fmt " = %a%a{@,@[<v 2>  %a@]@,}%a" pp_vis d.td_vis pp_mut d.td_mut pp_fields fs pp_invariants d.td_inv
    | TDalgebraic variants ->
        let pp_param fmt (_, id_opt, ghost, pty) =
          let ghost = if ghost then "ghost " else "" in
          match id_opt with
          | None -> fprintf fmt "%s%a" ghost pp_pty pty
          | Some id -> fprintf fmt "(%s%a : %a)" ghost pp_id id pp_pty pty in
        let pp_variant fmt (_, id, params) =
          fprintf fmt "%a%a" pp_id id (pp_print_opt_list ~prefix:" " pp_param) params in
        let pp_variants = pp_print_list ~pp_sep:(pp_sep "@,| ") pp_variant in
        fprintf fmt " = @,@[<v 2>  | %a@]" pp_variants variants
    | TDrange (i1, i2) ->
        fprintf fmt " = < range %s..%s >" (BigInt.to_string i1) (BigInt.to_string i2)
    | TDfloat (i1, i2) ->
        fprintf fmt " = < float %d..%d >" i1 i2 in
  let pp_wit fmt = function
    | [] -> ()
    | wits ->
        fprintf fmt " by { %a }" (pp_fields pp_expr expr_closed) wits in
  fprintf fmt "%a%a%a%a"
    pp_id d.td_ident
    (pp_print_opt_list ~prefix:" " pp_id) d.td_params
    pp_def d.td_def
    pp_wit d.td_wit

and pp_ind_decl fmt d =
  let pp_ind_decl_case fmt (_, id, t) =
    fprintf fmt "%a : %a" pp_id id pp_term t in
  let pp_ind_decl_def =
    pp_print_list ~pp_sep:(pp_sep " | ") pp_ind_decl_case in
  fprintf fmt "%a%a = %a" pp_id d.in_ident (pp_print_opt_list ~prefix:" " pp_param) d.in_params pp_ind_decl_def d.in_def

and pp_logic_decl fmt d =
  fprintf fmt "%a%a%a%a"
    pp_id d.ld_ident
    (pp_print_opt_list ~prefix:" " ~sep:" " pp_param) d.ld_params
    (pp_opt ~prefix:" : " pp_pty) d.ld_type
    (pp_opt ~prefix:" =@ " pp_term) d.ld_def

and pp_decl fmt = function
  | Dtype decls ->
      let pp_type_decls = pp_print_list ~pp_sep:(pp_sep "@,with ") pp_type_decl in
      fprintf fmt "@[<v>type %a@]" pp_type_decls decls
  | Dlogic decls when List.for_all (fun d -> d.ld_type = None) decls ->
      let pp_logic_decls = pp_print_list ~pp_sep:(pp_sep "@]@,@[<hv 2>with ") pp_logic_decl in
      fprintf fmt "@[<v>@[<hv 2>predicate %a@]@]" pp_logic_decls decls
  | Dlogic decls when List.for_all (fun d -> d.ld_type <> None) decls ->
      let pp_logic_decls = pp_print_list ~pp_sep:(pp_sep "@,with ") pp_logic_decl in
      fprintf fmt "@[<v>function %a@]" pp_logic_decls decls
  | Dlogic _ ->
      todo fmt "Dlogic _"
  | Dind (sign, decls) ->
      let keyword = match sign with Decl.Ind -> "inductive" | Decl.Coind -> "coinductive" in
      let pp_ind_decls = pp_print_list ~pp_sep:(pp_sep " with ") pp_ind_decl in
      fprintf fmt "%s %a" keyword pp_ind_decls decls
  | Dprop (kind, id, t) ->
      let keyword =
        match kind with
        | Decl.Plemma -> "lemma"
        | Decl.Paxiom -> "axiom"
        | Decl.Pgoal -> "goal" in
      fprintf fmt "%s %a = %a" keyword pp_id id pp_term t
  | Dlet (id, ghost, kind, {expr_desc=Efun (binders, pty_opt, pat, mask, spec, e)}) ->
      pp_let_fun pp_expr fmt (id, ghost, kind, (binders, pty_opt, pat, mask, spec, e))
  | Dlet (id, ghost, kind, {expr_desc=Eany (params, kind', pty_opt, pat, mask, spec)}) ->
    pp_let_any fmt (id, ghost, kind, (params, kind', pty_opt, pat, mask, spec))
  | Dlet (id, ghost, kind, e) ->
      pp_let pp_expr fmt (id, ghost, kind, e)
  | Drec defs ->
      let pp_fundefs =
        pp_print_list ~pp_sep:(pp_sep " and ") pp_fundef in
      fprintf fmt "let rec %a" pp_fundefs defs
  | Dexn (id, pty, mask) ->
      fprintf fmt "%a" pp_exn (id, pty, mask)
  | Dmeta (ident, args) ->
      let pp_metarg fmt = function
        | Mty _ -> todo fmt "Mty"
        | Mfs qid -> fprintf fmt "function %a" pp_qualid qid
        | Mps _ -> todo fmt "Mps"
        | Max _ -> todo fmt "Max"
        | Mlm _ -> todo fmt "Mlm"
        | Mgl _ -> todo fmt "Mgl"
        | Mval _ -> todo fmt "Mval"
        | Mstr _ -> todo fmt "Mstr"
        | Mint _ -> todo fmt "Mint" in
      let pp_args = pp_print_list ~pp_sep:(pp_sep " ") pp_metarg in
      fprintf fmt "meta %a %a" pp_id ident pp_args args
  | Dcloneexport (qid, []) ->
      fprintf fmt "@[<h>clone export %a@]" pp_qualid qid
  | Dcloneexport (qid, substs) ->
      let pp_substs = pp_print_list ~pp_sep:(pp_sep ",@ ") pp_clone_subst in
      fprintf fmt "@[<hv2>clone export %a with@ %a@]" pp_qualid qid pp_substs substs
  | Duseexport qid ->
      fprintf fmt "use export %a" pp_qualid qid
  | Dcloneimport (_, import, qid, None, []) ->
      let import = if import then " import" else "" in
      fprintf fmt "clone%s %a" import pp_qualid qid
  | Dcloneimport _ ->
      todo fmt "Dcloneimport _"
  | Duseimport (_, import, binds) ->
      let import = if import then " import" else "" in
      let pp_opt_id = pp_opt ~prefix:" as " pp_id in
      let pp_bind fmt (qid, opt_id) =
        fprintf fmt "%a%a" pp_qualid qid pp_opt_id opt_id in
      let pp_binds = pp_print_list ~pp_sep:(pp_sep ", ") pp_bind in
      fprintf fmt "use%s %a" import pp_binds binds
  | Dimport qid ->
      fprintf fmt "import %a" pp_qualid qid
  | Dscope _ ->
      todo fmt "Dscope _"

let pp_decls =
  let previous_was_use_import_export =
    ref false in
  let pp_decl' fmt decl =
    let this_is_use_import_export = match decl with
      | Duseimport _ | Duseexport _
      | Dcloneimport _ | Dcloneexport _
      | Dimport _ ->
          true
      | _ -> false in
    if not (!previous_was_use_import_export && this_is_use_import_export) then
      fprintf fmt "@,";
    previous_was_use_import_export := this_is_use_import_export;
    pp_decl fmt decl in
  pp_print_list ~pp_sep:(pp_sep "@,") pp_decl'

let pp_mlw_file fmt = function
  | Decls decls ->
      pp_decls fmt decls
  | Modules modules ->
      let pp_module fmt (id, decls) =
        fprintf fmt "@[<v 2>module %a@ %a@]@ end" pp_id id pp_decls decls in
      let pp_modules =
        pp_print_list ~pp_sep:(pp_sep "@,@,") pp_module in
      fprintf fmt "@[<v>%a@]" pp_modules modules
