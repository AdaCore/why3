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

module Mlw_printer = struct

  (* TODO move to src/mlw/mlw_printer.ml ? *)
  (* TODO parenthesis and associativity *)

  (* Test with
    $ why3 pp --output=mlw test.mlw > test1.mlw
    $ why3 pp --output=mlw test1.mlw > test2.mlw
    $ diff test1.mlw test2.mlw *)

  open Format
  open Why3
  open Ptree
  open Ident

  let pp_sep f fmt () =
    fprintf fmt f

  let pp_opt ?(prefix="") ?(suffix="") pp fmt = function
    | None -> ()
    | Some x ->
        fprintf fmt "%s%a%s" prefix pp x suffix

  let todo fmt str =
    fprintf fmt "<%s>" str

  let pp_print_opt_list ?(prefix:('a, formatter, unit) format="") ?(sep:('a, formatter, unit) format=" ") ?(suffix:('a, formatter, unit) format="") pp fmt = function
    | [] -> ()
    | xs ->
      fprintf fmt prefix;
      pp_print_list ~pp_sep:(pp_sep sep) pp fmt xs;
      fprintf fmt suffix

  let pp_id fmt id =
    pp_print_string fmt id.id_str

  let rec pp_qualid fmt = function
    | Qident id ->
        pp_id fmt id
    | Qdot (qid, id) ->
        fprintf fmt "@[<h>%a.%a@]" pp_qualid qid pp_id id

  let pp_true fmt () =
    pp_print_string fmt "true"

  let pp_false fmt () =
    pp_print_string fmt "false"

  let pp_const fmt c =
    Number.print_constant fmt c

  let pp_ident fmt id =
    pp_qualid fmt id

  let pp_asref fmt qid =
    fprintf fmt "@[<h>&%a@]" pp_qualid qid

  let pp_idapp pp fmt qid xs =
    match qid with
    | Qident id ->
        (match sn_decode id.id_str, xs with
        | SNword s, _ ->
            let pp_args = pp_print_list ~pp_sep:(pp_sep "@ ") pp in
            fprintf fmt "@[<hv 2>%s@ %a@]" s pp_args xs
        | SNinfix s, [x1; x2] ->
            fprintf fmt "@[<hv 2>%a@ %s %a@]" pp x1 s pp x2
        | SNprefix s, [x] -> (* TODO ??? *)
            fprintf fmt "@[<h>(%s) %a@]" s pp x
        | SNtight s, [x] ->
            fprintf fmt "@[<h>%s %a@]" s pp x
        | SNget s, [x1; x2] ->
            fprintf fmt "@[<h>%a[%a]%s@]" pp x1 pp x2 s
        | SNset s, [x1; x2; x3] ->
            fprintf fmt "@[<h>%a[%a]%s <- %a@]" pp x1 pp x2 s pp x3
        | SNupdate s, [x1; x2; x3] ->
            fprintf fmt "@[<h>%a[%a <- %a]%s@]" pp x1 pp x2 pp x3 s
        | SNcut s, [x] ->
            fprintf fmt "@[<h>%a[..]%s@]" pp x s
        | SNlcut s, [x1; x2] ->
            fprintf fmt "@[<h>%a[.. %a]%s@]" pp x1 pp x2 s
        | SNrcut s, [x1; x2] ->
            fprintf fmt "@[<h>%a[%a ..]%s@]" pp x1 pp x2 s
        | _ -> failwith "pp_expr")
    | _ ->
        let pp_args = pp_print_list ~pp_sep:pp_print_space pp in
        fprintf fmt "%a %a" pp_qualid qid pp_args xs

  let pp_apply pp fmt x1 x2 =
    fprintf fmt "@[<hv 2>%a@ %a@]" pp x1 pp x2

  let pp_infix pp fmt x1 op x2 =
    fprintf fmt "@[<hv 2>%a@ %a %a@]" pp x1 pp_id op pp x2

  let pp_not pp fmt x =
    fprintf fmt "@[<h>not@ %a@]" pp x

  let pp_scope pp fmt qid x =
    fprintf fmt "@[<hv 2>%a.(%a)@]" pp_qualid qid pp x

  let pp_tuple pp fmt xs =
    let pp_xs = pp_print_list ~pp_sep:(pp_sep ", ") pp in
    fprintf fmt "@[<hv 2>(%a)@]" pp_xs xs

  let pp_field pp fmt (qid, x) =
    fprintf fmt "@[<hv 2>%a =@ %a@]" pp_qualid qid pp x

  let pp_fields pp =
    pp_print_list ~pp_sep:(pp_sep " ;@ ") (pp_field pp)

  let pp_record pp fmt fs =
    fprintf fmt "@[@[<hv 2>{ %a@] }@]" (pp_fields pp) fs

  let pp_update pp fmt x fs =
    fprintf fmt "@[<hv 2>{ %a with@ %a }@]" pp x (pp_fields pp) fs

  let rec pp_pty fmt = function
    | PTtyvar id ->
        pp_id fmt id
    | PTtyapp (qid, []) ->
        pp_qualid fmt qid
    | PTtyapp (qid, ptys) ->
        let pp_ptys = pp_print_list ~pp_sep:(pp_sep " ") pp_pty in
        fprintf fmt "@[<hv 2>%a@ %a@]" pp_qualid qid pp_ptys ptys
    | PTtuple ptys ->
        pp_tuple pp_pty fmt ptys
    | PTref _ ->
        todo fmt "PTref"
    | PTarrow (pty1, pty2) ->
        fprintf fmt "%a -> %a" pp_pty pty1 pp_pty pty2
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

  let pp_param fmt (loc, opt_id, ghost, pty) =
    pp_binder fmt (loc, opt_id, ghost, Some pty)

  let pp_if pp fmt x1 x2 x3 =
    fprintf fmt "@[@[<hv 2>if %a@]@ @[<hv 2>then %a@]@ @[<hv 2>else %a@]@]" pp x1 pp x2 pp x3

  let pp_cast pp fmt x pty =
    fprintf fmt "(%a : %a)" pp x pp_pty pty

  let pp_attr pp fmt attr x =
    match attr with
    | ATstr a ->
        fprintf fmt "@[[@%s]@ %a@]" a.attr_string pp x
    | ATpos loc ->
        (* fprintf fmt "[# %a] %a" Loc.pp loc pp x *)
        todo fmt "attr-loc"

  let pp_exn fmt (id, pty, _mask) =
    (* TODO _mask *)
    let pp_pty fmt = function
      | PTtuple [] -> ()
      | pty -> fprintf fmt " %a" pp_pty pty in
    fprintf fmt "@[<h>exception %a%a@]" pp_id id pp_pty pty

  let pp_match pp pp_pattern fmt x cases xcases =
    let pp_reg_branch fmt (p, x) =
      fprintf fmt " | %a -> %a" pp_pattern p pp x in
    let pp_exn_branch fmt (qid, p_opt, x) =
      let pp_p_opt fmt = function
        | None -> ()
        | Some p -> fprintf fmt " %a" pp_pattern p in
      fprintf fmt " | exception %a%a -> %a" pp_qualid qid pp_p_opt p_opt pp x in
    fprintf fmt "@[@[<hv 2>match@ %a@]@ @[<hv 2>with@ %a%a@]@]"
      pp x
      (pp_print_opt_list ~prefix:" " pp_reg_branch) cases
      (pp_print_opt_list ~prefix:" " pp_exn_branch) xcases

  let pp_let pp fmt (id, ghost, kind, x) =
    (* TODO kind *)
    let pp_ghost fmt = function
      | false -> ()
      | true -> pp_print_string fmt " ghost" in
    fprintf fmt "@[<hv 2>let%a %a =@ %a@]" pp_ghost ghost pp_id id pp x

  let rec pp_let_fun pp fmt (id, ghost, kind, (binders, opt_pty, mask, spec, x)) =
    (* TODO mask *)
    let pp_ghost fmt = function
      | false -> ()
      | true -> pp_print_string fmt " ghost" in
    let pp_opt_pty fmt = function
      | None -> ()
      | Some pty -> fprintf fmt " : %a" pp_pty pty in
    let pp_binders = pp_print_opt_list ~prefix:" " pp_binder in
    fprintf fmt "@[<hv 2>let%a %a%a%a%a =@ %a@]" pp_ghost ghost pp_id id pp_binders binders pp_opt_pty opt_pty pp_spec spec pp x

  and pp_fundef fmt (id, ghost, kind, binders, pty_opt, mask, spec, e) =
    (* TODO mask *)
    if ghost then
      pp_print_string fmt " ghost";
    pp_id fmt id;
    pp_print_opt_list ~prefix:" " pp_binder fmt binders;
    (match pty_opt with
    | None -> ()
    | Some pty -> fprintf fmt " : %a" pp_pty pty);
    pp_spec fmt spec;
    fprintf fmt " = %a" pp_expr e

  and pp_variant fmt (t, qid_opt) =
    let pp_optwith fmt = function
      | None -> ()
      | Some qid -> fprintf fmt " with %a" pp_qualid qid in
    fprintf fmt "@[@[<hv 2>variant {@ %a%a@]@ }@]" pp_term t pp_optwith qid_opt

  and pp_variants fmt =
    pp_print_opt_list ~prefix:"@ " ~sep:("@ ") pp_variant fmt

  and pp_invariant fmt =
    fprintf fmt "@[@[<hv 2>invariant {@ %a@]@ }@]" pp_term

  and pp_invariants fmt =
    pp_print_opt_list ~prefix:"@ " ~sep:"@ " pp_invariant fmt

  and pp_expr fmt e = match e.expr_desc with
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
        pp_idapp pp_expr fmt qid es
    | Eapply (e1, e2) ->
        pp_apply pp_expr fmt e1 e2
    | Einfix (e1, op, e2) ->
        pp_infix pp_expr fmt e1 op e2
    | Einnfix (e1, op, e2) ->
        fprintf fmt "innfix (%a, %a, %a)" pp_expr e1 pp_id op pp_expr e2
    | Elet (id, ghost, kind, {expr_desc=Efun (binders, pty_opt, mask, spec, e1)}, e2) ->
        fprintf fmt "@[%a in %a@]"
          (pp_let_fun pp_expr) (id, ghost, kind, (binders, pty_opt, mask, spec, e1))
          pp_expr e2
    | Elet (id, ghost, kind, e1, e2) ->
        fprintf fmt "@[%a in@ %a@]" (pp_let pp_expr) (id, ghost, kind, e1) pp_expr e2
    | Erec (defs, e) ->
        let pp_fundefs =
          pp_print_list ~pp_sep:(pp_sep " and ") pp_fundef in
        fprintf fmt "let rec %a in %a" pp_fundefs defs pp_expr e
    | Efun _ -> fprintf fmt "fun _"
    | Eany _ -> fprintf fmt "any _"
    | Etuple es ->
        pp_tuple pp_expr fmt es
    | Erecord fs ->
        pp_record pp_expr fmt fs
    | Eupdate (e, fs) ->
        pp_update pp_expr fmt e fs
    | Eassign [e1, None, e2] ->
        fprintf fmt "%a <- %a" pp_expr e1 pp_expr e2
    | Eassign [e1, Some qid, e2] ->
        fprintf fmt "%a.%a <- %a" pp_expr e1 pp_qualid qid pp_expr e2
    | Eassign _ ->
        todo fmt "Eassign"
    (** control *)
    | Esequence (e1, e2) ->
        fprintf fmt "@[<v>%a;@ %a@]" pp_expr e1 pp_expr e2
    | Eif (e1, e2, e3) ->
        pp_if pp_expr fmt e1 e2 e3
    | Ewhile (e1, invs, vars, e2) ->
        fprintf fmt "@[<v>@[<hv 2>while %a@] do%a%a@ @[<hv 2>%a@]@ done@]" pp_expr e1 pp_invariants invs pp_variants vars pp_expr e2
    | Eand (e1, e2) ->
        fprintf fmt "@[@[<hv 2>%a@]@ @[<hv 2>/\\ %a@]@]" pp_expr e1 pp_expr e2
    | Eor (e1, e2) ->
        fprintf fmt "@[@[<hv 2>%a@]@ @[<hv 2>\\/ %a@]@]" pp_expr e1 pp_expr e2
    | Enot e ->
        pp_not pp_expr fmt e
    | Ematch (e, cases, xcases) ->
        pp_match pp_expr pp_pattern fmt e cases xcases
    | Eabsurd ->
        pp_print_string fmt "absurd"
    | Epure t ->
        fprintf fmt "@[@[<hv 2>pure {@ %a@]@ }@]" pp_term t
    | Eidpur _ ->
        todo fmt "Eidpur"
    | Eraise (Qident {id_str="'Return"|"'Break"|"'Continue" as str}, opt_arg) ->
        let pp_opt_arg fmt = function
          | None -> ()
          | Some e -> fprintf fmt " %a" pp_expr e in
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
          | Some e -> fprintf fmt " %a" pp_expr e in
        fprintf fmt "raise %a%a" pp_qualid qid pp_opt_arg opt_arg
    | Eexn (id, pty, mask, e) ->
        fprintf fmt "@[%a in@ %a@]" pp_exn (id, pty, mask) pp_expr e
    | Eoptexn (id, mask, e) ->
        (* TODO mask *)
        fprintf fmt "@[<v>exception %a in@ %a@]" pp_id id pp_expr e
    | Efor (id, start, dir, end_, invs, body) ->
        let dir = match dir with Expr.To -> "to" | Expr.DownTo -> "downto" in
        let pp_invs =
          let pp_inv fmt =
            fprintf fmt "@[<hv 2>invariant { %a }@]" pp_term in
          pp_print_list ~pp_sep:(pp_sep "@ ") pp_inv in
        fprintf fmt "@[for %a = %a %s %a@[<hv 2>do@ %a%a@]@ done@]"
          pp_id id pp_expr start dir pp_expr end_ pp_invs invs pp_expr body
    (** annotations *)
    | Eassert (Expr.Assert, {term_desc=Tattr (ATstr {attr_string="hyp_name:Assert"}, t)}) ->
        fprintf fmt "@[<hv 2>assert {@ %a@ }@]" pp_term t
    | Eassert (Expr.Assume, {term_desc=Tattr (ATstr {attr_string="hyp_name:Assume"}, t)}) ->
        fprintf fmt "@[<hv 2>assume {@ %a@ }@]" pp_term t
    | Eassert (Expr.Check, {term_desc=Tattr (ATstr {attr_string="hyp_name:Check"}, t)}) ->
        fprintf fmt "@[<hv 2>check {@ %a@ }@]" pp_term t
    | Eassert (kind, t) ->
        let pp_assert_kind fmt kind =
          pp_print_string fmt
            (match kind with
            | Expr.Assert -> "assert"
            | Expr.Assume -> "assume"
            | Expr.Check -> "check") in
        fprintf fmt "@[<hv 2>%a {@ %a@ }@]" pp_assert_kind kind pp_term t
    | Escope (qid, e) ->
        pp_scope pp_expr fmt qid e
    | Elabel (id, e) ->
        fprintf fmt "label %a in %a" pp_id id pp_expr e
    | Ecast (e, pty) ->
        pp_cast pp_expr fmt e pty
    | Eghost e ->
        fprintf fmt "ghost %a" pp_expr e
    | Eattr (attr, e) ->
        pp_attr pp_expr fmt attr e

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
        pp_idapp pp_term fmt qid ts
    | Tapply (t1, t2) ->
        pp_apply pp_term fmt t1 t2
    | Tinfix (t1, op, t2) ->
        pp_infix pp_term fmt t1 op t2
    | Tinnfix (t1, op, t2) ->
        fprintf fmt "innfix (%a, %a, %a)" pp_term t1 pp_id op pp_term t2
    | Tbinop (t1, op, t2) ->
        fprintf fmt "%a %a %a" pp_term t1 pp_binop op pp_term t2
    | Tbinnop (t1, op, t2) ->
        fprintf fmt "Tbinnop (%a, %a, %a)" pp_term t1 pp_binop op pp_term t2
    | Tnot t ->
        pp_not pp_term fmt t
    | Tif (t1, t2, t3) ->
        pp_if pp_term fmt t1 t2 t3
    | Tquant _ ->
        fprintf fmt "Tquant _"
    | Tattr (attr, t) ->
        pp_attr pp_term fmt attr t
    | Tlet (id, t1, t2) ->
        pp_let pp_term fmt (id, false, t1, t2)
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
    | Tat (t, id) ->
        fprintf fmt "%a at %a" pp_term t pp_id id

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
            fprintf fmt "%a -> %a" pp_pattern p pp_term t in
          fprintf fmt "@ ensures { %a }"
            (pp_print_list ~pp_sep:(pp_sep "|") pp_case) cases in
    List.iter pp_post s.sp_post;
    let pp_xpost _ =
      todo fmt "sp_xpost" in
    List.iter pp_xpost s.sp_xpost;
    let pp_alias _ =
      todo fmt "sp_alias" in
    List.iter pp_alias s.sp_alias;
    List.iter (pp_variant fmt) s.sp_variant;
    (* TODO s.sp_checkrw *)
    if s.sp_diverge then
      pp_print_string fmt "@ diverge";
    if s.sp_partial then
      pp_print_string fmt "@ partial";

  and pp_pattern fmt p =
    match p.pat_desc with
    | Pwild ->
        pp_print_string fmt "_"
    | Pvar id ->
        pp_id fmt id
    | Papp (qid, args) ->
        pp_idapp pp_pattern fmt qid args
    | Prec _ ->
        todo fmt "Prec"
    | Ptuple ps ->
        pp_tuple pp_pattern fmt ps
    | Pas (p, id, ghost) ->
        let pp_ghost fmt = function
          | false -> ()
          | true -> pp_print_string fmt " ghost" in
        fprintf fmt "%a as %a%a" pp_pattern p pp_id id pp_ghost ghost
    | Por (p1, p2) ->
        fprintf fmt "%a | %a" pp_pattern p1 pp_pattern p2
    | Pcast (p, pty) ->
        pp_cast pp_pattern fmt p pty
    | Pscope (qid, p) ->
        pp_scope pp_pattern fmt qid p
    | Pparen p ->
        fprintf fmt "(%a)" pp_pattern p
    | Pghost p ->
        fprintf fmt "ghost %a" pp_pattern p

  and pp_type_decl fmt d =
    let pp_def fmt = function
      | TDalias pty ->
          pp_pty fmt pty
      | TDalgebraic variants ->
          let pp_param fmt (_, id_opt, ghost, pty) =
            let ghost = if ghost then "ghost " else "" in
            match id_opt with
            | None -> fprintf fmt "%s%a" ghost pp_pty pty
            | Some id -> fprintf fmt "(%s%a : %a)" ghost pp_id id pp_pty pty in
          let pp_variant fmt (_, id, params) =
            fprintf fmt "%a%a" pp_id id (pp_print_opt_list ~prefix:" " pp_param) params in
          let pp_variants = pp_print_list ~pp_sep:(pp_sep "@,| ") pp_variant in
          fprintf fmt "@,@[<v 2>  | %a@]" pp_variants variants
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
          fprintf fmt "%a%a{@,@[<v 2>  %a@]@,}%a" pp_vis d.td_vis pp_mut d.td_mut pp_fields fs pp_invariants d.td_inv
      | TDrange (i1, i2) ->
          fprintf fmt "< range %s..%s >" (BigInt.to_string i1) (BigInt.to_string i2)
      | TDfloat (i1, i2) ->
          fprintf fmt "< float %d..%d >" i1 i2 in
    let pp_wit fmt = function
      | [] -> ()
      | wits ->
          fprintf fmt " by { %a }" (pp_fields pp_expr) wits in
    fprintf fmt "%a%a = %a%a"
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

  and pp_decl fmt = function
    | Dtype decls ->
        let pp_type_decls = pp_print_list ~pp_sep:(pp_sep "@,with ") pp_type_decl in
        fprintf fmt "@[<v>type %a@]" pp_type_decls decls
    | Dlogic _ ->
        todo fmt "Dlogic"
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
    | Dlet (id, ghost, kind, {expr_desc=Efun (binders, pty_opt, mask, spec, e)}) ->
        pp_let_fun pp_expr fmt (id, ghost, kind, (binders, pty_opt, mask, spec, e))
    | Dlet (id, ghost, kind, e) ->
        pp_let pp_expr fmt (id, ghost, kind, e)
    | Drec defs ->
        let pp_fundefs =
          pp_print_list ~pp_sep:(pp_sep " and ") pp_fundef in
        fprintf fmt "let rec %a" pp_fundefs defs
    | Dexn (id, pty, mask) ->
        fprintf fmt "%a" pp_exn (id, pty, mask)
    | Dmeta _ ->
        todo fmt "Dmeta"
    | Dcloneexport _ ->
        todo fmt "Dcloneexport"
    | Duseexport qid ->
        fprintf fmt "clone %a" pp_qualid qid
    | Dcloneimport _ ->
        todo fmt "Dcloneimport"
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
        (* TODO syntax? Dscope isn't mentioned in parser.mly *)
        todo fmt "Dscope"

  let pp_decls =
    pp_print_list ~pp_sep:(pp_sep "@,@,") pp_decl

  let pp_mlw_file fmt mlw_file =
    fprintf fmt "(* WARNING parenthesis for associativity and precedence are missing *)@.";
    match mlw_file with
    | Decls decls ->
        pp_decls fmt decls
    | Modules modules ->
        let pp_module fmt (id, decls) =
          fprintf fmt "@[<v 2>module %a@,%a@]@ end" pp_id id pp_decls decls in
        let pp_modules =
          pp_print_list ~pp_sep:(pp_sep "@,@,") pp_module in
        fprintf fmt "@[<v>%a@]" pp_modules modules
end

module LatexInd (Conf: sig val prefix: string val flatten_applies : bool val comment_macros : bool end) = struct

  open Format
  open Why3
  open Ptree
  open Ident

  open Conf

  let sanitize =
    let my_char_to_alpha = function
      (* | '_' | '.' -> "" *)
      | c -> char_to_alpha c
    in
    sanitizer my_char_to_alpha my_char_to_alpha

  let sanitize2 =
    let aux = function
      | '_' -> "" (* "\\_" *)
      | c -> char_to_alpha c in
    sanitizer aux aux

  (** Optionally extract trailing numbers and quotes, after an optional single or double
      underscore *)
  let split_base_suffixes str =
    try
      let re = Str.regexp "_?_?\\([0-9]*\\)\\('*\\)$" in
      let n = Str.search_forward re str 0 in
      let base = String.sub str 0 n in
      let numbers =
        match Str.matched_group 1 str with
        | "" -> None
        | s -> Some s
      in
      let quotes =
        match Str.matched_group 2 str with
        | "" -> None
        | s -> Some s
      in
      Some (base, numbers, quotes)
    with Not_found ->
      None

  (** Requirements *)

  type command_shape = {name: string; name': string; arity: int}

  module Requirements = Set.Make (struct type t = command_shape let compare = compare end)

  let requirements = ref Requirements.empty

  let record_command_shape name name' arity =
    requirements := Requirements.add {name; name'; arity} !requirements

  (** {2 Printers} *)
  let pp_command' ~suffix fmt base =
    fprintf fmt "\\%s%s%s" prefix (sanitize base) suffix

  (** Print a string as a LaTeX command *)
  let pp_command fmt ~arity name =
    if match sn_decode name with | SNword _ -> false | _ -> true then
      failwith ("pp_command: argument not word: "^name);
    let name, name', suffix =
      if arity = 0 then
        match split_base_suffixes name with
        | Some (base, numbers, quotes) ->
            let numbers =
              match numbers with
              | Some s -> sprintf "_{%s}" s
              | None -> "" in
            let quotes =
              match quotes with
              | Some s -> s
              | None -> "" in
            base, base, numbers^quotes
        | _ -> name, name, ""
      else
        name^string_of_int arity, name, "" in
    record_command_shape name name' arity;
    pp_command' ~suffix fmt name

  let pp_var fmt id =
    pp_command fmt ~arity:0 id.id_str

  let pp_str str fmt () = fprintf fmt str

  let pp_command_shape ~comment_macros fmt {name; name'; arity} =
    let rec mk_args acc = function
      | 0 -> acc
      | n -> mk_args (sprintf "#%d" n::acc) (pred n) in
    let pp_args fmt n =
      if n = 0 then
        ()
      else
        let args = mk_args [] n in
        fprintf fmt "(%a)" (pp_print_list ~pp_sep:(pp_str ", ") pp_print_string) args in
    fprintf fmt "%s\\newcommand{%a}[%d]{\\mathsf{%s}%a}@."
      (if comment_macros then "% " else "")
      (pp_command' ~suffix:"") name arity (sanitize2 name') pp_args arity

  (** {2 Pretty-print inductive definition to latex }*)

  let latex_rule_name fmt s =
    let f = function
      | '_' -> pp_print_char fmt '-'
      | c -> pp_print_char fmt c
    in
    String.iter f s

  let id_of_qualid = function
    | Qident id
    | Qdot (_, id) -> id

  let rec str_of_qualid = function
    | Qident id -> id.id_str
    | Qdot (qid, id) -> str_of_qualid qid^"."^id.id_str

  let pp_arg pp fmt =
    fprintf fmt "{%a}" pp

  let pp_field pp fmt (qid, x) =
    fprintf fmt "%a\\texttt{=}%a"
      pp_var (id_of_qualid qid) pp x

  let rec pp_type fmt = function
    | PTtyvar id ->
        pp_var fmt id
    | PTtyapp (qid, ts) ->
        let str = str_of_qualid qid in
        let arity = List.length ts in
        fprintf fmt "%a%a" (pp_command ~arity) str
          (pp_print_list ~pp_sep:(pp_str "") (pp_arg pp_type)) ts
    | PTtuple ts ->
        fprintf fmt "(%a)"
          (pp_print_list ~pp_sep:(pp_str "") pp_type) ts
    | PTarrow (ty1, ty2) ->
        fprintf fmt "%a \\rightarrow %a"
          pp_type ty1 pp_type ty2
    | PTscope (_, ty) ->
        pp_type fmt ty
    | PTparen ty ->
        fprintf fmt "(%a)" pp_type ty
    | PTpure ty ->
        fprintf fmt "\\texttt{\\{}%a\\texttt{\\}}" pp_type ty
    | PTref _ -> failwith "pp_type: ref"

  let rec pp_pattern fmt p =
    match p.pat_desc with
    | Pwild ->
        fprintf fmt "\\texttt{anything}"
    | Pvar id ->
        fprintf fmt "%a" pp_var id
    | Papp (qid, ps) ->
        let str = str_of_qualid qid in
        let arity = List.length ps in
        fprintf fmt "%a%a" (pp_command ~arity) str
          (pp_print_list ~pp_sep:(pp_str "") (pp_arg pp_pattern)) ps
    | Prec fs ->
        fprintf fmt "\\texttt{\\{}%a\texttt{\\}}"
          (pp_print_list ~pp_sep:(pp_str "\\texttt{;} ") (pp_field pp_pattern)) fs
    | Ptuple ps ->
        fprintf fmt "(%a)" (pp_print_list ~pp_sep:(pp_str ", ") pp_pattern) ps
    | Pas (p, id, _) ->
        fprintf fmt "%a \texttt{as} %a" pp_pattern p pp_var id
    | Por (p1, p2) ->
        fprintf fmt "%a \texttt{|} %a" pp_pattern p1 pp_pattern p2
    | Pcast (p, ty) ->
        fprintf fmt "%a : %a" pp_pattern p pp_type ty
    | Pscope (_, p) ->
        pp_pattern fmt p
    | Pparen p ->
        fprintf fmt "(%a)" pp_pattern p
    | Pghost p ->
        pp_pattern fmt p

  let rec flatten_apply t =
    match t.term_desc with
    | Tapply ({term_desc=Tident qid}, t) -> Some (qid, [t])
    | Tapply (t1, t2) ->
        (match flatten_apply t1 with
         | Some (qid, ts) -> Some (qid, ts@[t2])
         | None -> None)
    | _ -> None

  let rec pp_term fmt t =
    match t.term_desc with
    | Ttrue ->
        fprintf fmt "\\top"
    | Tfalse ->
        fprintf fmt "\\bot"
    | Tconst n ->
        Number.print_constant fmt n
    | Tident qid ->
        let id = id_of_qualid qid in
        (match sn_decode id.id_str with
         | SNword _ -> pp_var fmt id
         | _ -> fprintf fmt "(%s)" id.id_str)
    | Tinnfix (t1, id, t2)
    | Tinfix (t1, id, t2) ->
        let op =
          match sn_decode id.id_str with
          | SNinfix "<>" -> "\\neq"
          | SNinfix op -> op
          | _ -> failwith ("pp_term: op not infix: |"^id.id_str^"|") in
        fprintf fmt "%a %s %a" pp_term t1 op pp_term t2
    | Tbinop (t1, op, t2)
    | Tbinnop (t1, op, t2) ->
        let str =
          let open Dterm in
          match op with
          | DTimplies -> "\\rightarrow"
          | DTiff -> "\\leftrightarrow"
          | DTand -> "\\wedge"
          | DTand_asym -> "\\bar\\wedge"
          | DTor -> "\\vee"
          | DTor_asym -> "\\bar\\vee"
          | DTby -> "\\texttt{by}"
          | DTso -> "\\texttt{so}" in
        fprintf fmt "%a %s %a" pp_term t1 str pp_term t2
    | Tidapp (qid, ts) ->
        let id = id_of_qualid qid in
        (match sn_decode id.id_str, ts with
         | SNword s, ts ->
             let arity = List.length ts in
             let pp_args = pp_print_list ~pp_sep:(pp_str "") (pp_arg pp_term) in
             fprintf fmt "%a%a" (pp_command ~arity) s pp_args ts
         | SNinfix s, [t1; t2] ->
             fprintf fmt "%a %s %a" pp_term t1 s pp_term t2
         | SNprefix s, [t]
         | SNtight s, [t] ->
             fprintf fmt "%s %a" s pp_term t
         | SNget s, [t1; t2] ->
             fprintf fmt "%a[%a]%s" pp_term t1 pp_term t2 s
         | SNset s, [t1; t2; t3] ->
             fprintf fmt "%a[%a]%s \\leftarrow %a" pp_term t1 pp_term t2 s pp_term t3
         | SNupdate s, [t1; t2; t3] ->
             fprintf fmt "%a[%a \\leftarrow %a]%s" pp_term t1 pp_term t2 pp_term t3 s
         | SNcut s, [t] ->
             fprintf fmt "%a[\\ldots]%s" pp_term t s
         | SNlcut s, [t1; t2] ->
             fprintf fmt "%a[\\ldots %a]%s" pp_term t1 pp_term t2 s
         | SNrcut s, [t1; t2] ->
             fprintf fmt "%a[%a \\ldots]%s" pp_term t1 pp_term t2 s
         | _ -> failwith (sprintf "pp_term Tidapp %s %d" id.id_str (List.length ts)))
    | Tapply (t1, t2) ->
        (match
           if flatten_applies
           then flatten_apply t
           else None
         with
         | Some (qid, ts) ->
             let str = str_of_qualid qid in
             let arity = List.length ts in
             fprintf fmt "%a%a" (pp_command ~arity) str
               (pp_print_list ~pp_sep:(pp_str "") (pp_arg pp_term)) ts
         | None ->
             fprintf fmt "%a %a" pp_term t1 pp_term t2)
    | Tnot {term_desc=Tinfix (t1, op, t2)} when
        sn_decode op.id_str = SNinfix "=" ->
        fprintf fmt "%a \\neq %a" pp_term t1 pp_term t2
    | Tnot t ->
        fprintf fmt "\\neg %a" pp_term t
    | Tif (t1, t2, t3) ->
        fprintf fmt "\\texttt{if}~%a~\\texttt{then}~%a~\\texttt{else}~%a"
          pp_term t1 pp_term t2 pp_term t3
    | Tlet (id, t1, t2) ->
        fprintf fmt "\\textbf{let}~%a = %a~\\textbf{in}~%a" pp_var id
          pp_term t1 pp_term t2
    | Tquant (_, _, _, t) ->
        pp_term fmt t
    | Tcase (t, bs) ->
        let pp_sep = pp_str " \\texttt{|} " in
        let pp_branch fmt (p, t') = fprintf fmt "%a \\rightarrow %a" pp_pattern p pp_term t' in
        fprintf fmt "\\texttt{match}~%a~\\texttt{with}~%a" pp_term t
          (pp_print_list ~pp_sep pp_branch) bs
    | Tcast (t, ty) ->
        fprintf fmt "%a \texttt{:} %a" pp_term t pp_type ty
    | Ttuple ts ->
        fprintf fmt "(%a)" (pp_print_list ~pp_sep:(pp_str ", ") pp_term) ts
    | Trecord fs ->
        let pp = pp_print_list ~pp_sep:(pp_str "\\texttt{;} ") (pp_field pp_term) in
        fprintf fmt "\\{%a\\}" pp fs
    | Tupdate (t, fs) ->
        let pp_fs = pp_print_list ~pp_sep:(pp_str "\\texttt{;} ") (pp_field pp_term) in
        fprintf fmt "\\{%a~\\texttt{with}~%a\\}" pp_term t pp_fs fs
    | Tscope (_, t) ->
        pp_term fmt t
    | Tattr _ -> failwith "pp_term: attr"
    | Tat _ -> failwith "pp_term: at"
    | Tasref _ -> failwith "pp_term: asref"

  let pp_rule fmt (id, terms) : unit =
    match List.rev terms with
    | [] -> invalid_arg "latex_rule: empty rule"
    | concl :: precs ->
        fprintf fmt "  \\inferrule[%a]@.    {%s%a}@.    {%a} \\\\@."
          latex_rule_name id.id_str
          (if precs = [] then "~" else "")
          (pp_print_list ~pp_sep:(pp_str "@ \\\\@ ") pp_term) (List.rev precs)
          pp_term concl

  let pp_rules fmt path defs =
    fprintf fmt "\\begin{mathparpagebreakable} %% %s@." (String.concat "." path);
    List.iter (pp_rule fmt) defs;
    fprintf fmt "\\end{mathparpagebreakable}@."

  exception Found of ind_decl

  (** Search an inductive type in mlw file by path (module.Theory.type or module.type) *)
  let search_inductive (path: string list) (mlw_file: mlw_file) : ind_decl =
    let name, decls =
      match path, mlw_file with
      | [name], Decls decls -> name, decls
      | [module_name; name], Modules modules ->
          let aux (id, _) = String.compare id.id_str module_name = 0 in
          name, snd (List.find aux modules)
      | _ -> raise Not_found in
    try
      let aux = function
        | Dind (Decl.Ind, ind_decls) ->
            let aux decl =
              if String.compare decl.in_ident.id_str name = 0 then
                raise (Found decl) in
            List.iter aux ind_decls
        | _ -> () in
      List.iter aux decls;
      raise Not_found
    with Found decl -> decl

  (** Flatten toplevel implies, let bindings, and universal quantifications *)
  let rec flatten_implies (t: term) : term list =
    match t.term_desc with
    | Tbinop (t1, Dterm.DTimplies, t2) ->
        t1 :: flatten_implies t2
    | Tquant (Dterm.DTforall, _, _, t) ->
        flatten_implies t
    | Tlet (id, t1, t2) ->
        let equality = (* id = t2 *)
          let id_term = {term_loc=Loc.dummy_position; term_desc=Tident (Qident id)} in
          let op = {Ptree.id_str=op_infix "="; Ptree.id_loc=Loc.dummy_position; id_ats=[]} in
          Tinfix (id_term, op, t1) in
        {term_loc=Loc.dummy_position; term_desc=equality} ::
        flatten_implies t2
    | _ -> [t]

  let main fmt mlw_file paths =
    let buf = Buffer.create 42 in
    let fmt' = formatter_of_buffer buf in
    let for_path path =
      try
        let decl = search_inductive path mlw_file in
        let defs = List.map (fun (_, id, t) -> id, flatten_implies t) decl.in_def in
        pp_rules fmt' path defs
      with Not_found ->
        eprintf "Could not find %s" (Strings.join "." path) in
    List.iter for_path paths;
    Requirements.iter (pp_command_shape ~comment_macros fmt) !requirements;
    pp_print_string fmt (Buffer.contents buf)
end

(** {2 Command line interface} *)

open Why3
open Format

let filename = ref None

let paths = Queue.create ()

let add_filename_then_path p =
  if !filename = None then
    filename := Some p
  else
    Queue.add (Strings.split '.' p) paths

type kind = Inductive

let kind = ref None

let set_kind = function
  | "inductive" -> kind := Some Inductive
  | str -> ksprintf invalid_arg "kind: %s" str

type output = Latex | Mlw | Ast

let output = ref None

let set_output = function
  | "latex" -> output := Some Latex
  | "mlw" -> output := Some Mlw
  | "ast" -> output := Some Ast
  | str -> ksprintf invalid_arg "output: --%s--" str

let prefix = ref "IND"

let usage =
  "Pretty print Why3 declarations (currently only inductive types in LaTeX using mathpartir).\n\
   why3 pp [--output=latex|mlw|ast] [--kind=inductive] [--prefix <prefix>] <filename> [<Module>.]<type> ..."

let options = [
  "--output", Arg.String set_output,    "<output> Output format";
  "--kind",   Arg.String set_kind,      "<category> Syntactic category to be printed (--kind=inductive only possible value for --output=latex)";
  "--prefix", Arg.String ((:=) prefix), "<prefix> Prefix for LaTeX commands (default for output latex: IND)";
]

let parse_mlw_file filename =
  let c = open_in filename in
  let lexbuf = Lexing.from_channel c in
  let mlw_file = Why3.Lexer.parse_mlw_file lexbuf in
  close_in c;
  mlw_file

let () =
  Arg.parse options add_filename_then_path usage;
  try
    match !filename with
    | Some filename ->
        let mlw_file = parse_mlw_file filename in
        (match !output, !kind, Queue.length paths with
         | Some Latex, Some Inductive, _ ->
             let paths = List.rev (Queue.fold (fun l x -> x :: l) [] paths) in
             let module M = LatexInd(struct let prefix = !prefix let flatten_applies = true let comment_macros = false end) in
             M.main std_formatter mlw_file paths
         | Some Mlw, None, 0 ->
             Mlw_printer.pp_mlw_file std_formatter mlw_file
         (* | Some Ast, None, 0 ->
          *     Ptree.pp_mlw_file std_formatter mlw_file *)
         | _, _, _ ->
             failwith "command line arguments" (* |ast *)
        )
    | None -> invalid_arg "no filename given"
  with Invalid_argument msg ->
    eprintf "Error: %s@." msg;
    exit 1
