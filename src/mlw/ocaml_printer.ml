(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2016   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Printer for extracted OCaml code *)

open Compile
open Format
open Ident
open Pp
open Ity
open Term
open Expr
open Ty
open Theory
open Pmodule
open Stdlib
open Pdecl
open Printer

type info = {
  info_syn          : syntax_map;
  info_convert      : syntax_map;
  info_current_th   : Theory.theory;
  info_current_mo   : Pmodule.pmodule option;
  info_th_known_map : Decl.known_map;
  info_mo_known_map : Pdecl.known_map;
  info_fname        : string option;
  flat              : bool;
}

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
    let h = Hstr.create 16 in
    List.iter (fun s -> Hstr.add h s ()) ocaml_keywords;
    Hstr.mem h

  let iprinter, aprinter =
    let isanitize = sanitizer char_to_alpha char_to_alnumus in
    let lsanitize = sanitizer char_to_lalpha char_to_alnumus in
    create_ident_printer ocaml_keywords ~sanitizer:isanitize,
    create_ident_printer ocaml_keywords ~sanitizer:lsanitize

  let forget_id vs = forget_id iprinter vs
  let _forget_ids = List.iter forget_id
  let forget_var (id, _, _) = forget_id id
  let forget_vars = List.iter forget_var

  let forget_let_defn = function
  | Lvar (v,_) -> forget_id v.pv_vs.vs_name
  | Lsym (s,_,_,_) -> forget_rs s
  | Lrec rdl -> List.iter (fun fd -> forget_rs fd.rec_sym) rdl

  let rec forget_pat = function
    | Pwild -> ()
    | Pident id -> forget_id id
    | Papp (_, pl) | Ptuple pl -> List.iter forget_pat pl
    | Por (p1, p2) -> forget_pat p1; forget_pat p2
    | Pas (p, _) -> forget_pat p

  let print_ident fmt id =
    let s = id_unique iprinter id in
    fprintf fmt "%s" s

  let is_local_id info id =
    Sid.mem id info.info_current_th.th_local ||
      Opt.fold (fun _ m -> Sid.mem id m.Pmodule.mod_local)
      false info.info_current_mo

  let print_qident ~sanitizer info fmt id =
    try
      if info.flat then raise Not_found;
      let lp, t, q =
        try Pmodule.restore_path id
        with Not_found -> Theory.restore_path id in
      let s = String.concat "__" q in
      let s = Ident.sanitizer char_to_alpha char_to_alnumus s in
      let s = sanitizer s in
      let s = if is_ocaml_keyword s then s ^ "_renamed" else s in (* FIXME *)
      if is_local_id info id then
        fprintf fmt "%s" s
      else begin
        let fname = if lp = [] then info.info_fname else None in
        let m = Strings.capitalize (module_name ?fname lp t) in
        fprintf fmt "%s.%s" m s end
    with Not_found ->
      let s = id_unique ~sanitizer iprinter id in
      fprintf fmt "%s" s

  let print_lident = print_qident ~sanitizer:Strings.uncapitalize
  let print_uident = print_qident ~sanitizer:Strings.capitalize

  let print_tv fmt tv =
    fprintf fmt "'%s" (id_unique aprinter tv.tv_name)

  let protect_on b s =
    if b then "(" ^^ s ^^ ")" else s

  let star fmt () = fprintf fmt " *@ "

  let rec print_list2 sep sep_m print1 print2 fmt (l1, l2) =
    match l1, l2 with
    | [x1], [x2] ->
      print1 fmt x1; sep_m fmt (); print2 fmt x2
    | x1 :: r1, x2 :: r2 ->
      print1 fmt x1; sep_m fmt (); print2 fmt x2; sep fmt ();
      print_list2 sep sep_m print1 print2 fmt (r1, r2)
    | _ -> ()

  let print_rs info fmt rs =
    fprintf fmt "%a" (print_lident info) rs.rs_name

  (** Types *)

  let rec print_ty ?(paren=false) info fmt = function
    | Tvar tv ->
      print_tv fmt tv
    | Ttuple [] ->
      fprintf fmt "unit"
    | Ttuple tl ->
      fprintf fmt (protect_on paren "@[%a@]")
        (print_list star (print_ty ~paren:true info)) tl
    | Tapp (ts, [t1; t2]) when id_equal ts ts_func.ts_name ->
      fprintf fmt (protect_on paren "@[%a ->@ %a@]")
        (print_ty ~paren:true info) t1 (print_ty info) t2
    | Tapp (ts, tl) ->
      match query_syntax info.info_syn ts with
      | Some s ->
        syntax_arguments s (print_ty ~paren:true info) fmt tl
      | None   ->
        match tl with
        | [] ->
          (print_lident info) fmt ts
        | [ty] ->
          fprintf fmt (protect_on paren "%a@ %a")
            (print_ty ~paren:true info) ty (print_lident info) ts
        | tl ->
          fprintf fmt (protect_on paren "(%a)@ %a")
            (print_list comma (print_ty ~paren:false info)) tl
            (print_lident info) ts

  let print_vsty info fmt (v, ty, _) =
    fprintf fmt "%a:@ %a" print_ident v (print_ty ~paren:false info) ty

  let print_tv_arg = print_tv
  let print_tv_args fmt = function
    | []   -> ()
    | [tv] -> fprintf fmt "%a@ " print_tv_arg tv
    | tvl  -> fprintf fmt "(%a)@ " (print_list comma print_tv_arg) tvl

  let print_vs_arg info fmt vs =
    fprintf fmt "@[(%a)@]" (print_vsty info) vs

  let print_path =
    print_list dot pp_print_string (* point-free *)

  let print_path_id fmt = function
    | [], id -> print_ident fmt id
    | p, id  -> fprintf fmt "%a.%a" print_path p print_ident id

  let print_theory_name fmt th =
    print_path_id fmt (th.th_path, th.th_name)

  let print_module_name fmt m =
    print_theory_name fmt m.mod_theory

  let get_record info rs =
    match Mid.find_opt rs.rs_name info.info_mo_known_map with
    | Some {pd_node = PDtype itdl} ->
      let itd = List.find (fun {itd_constructors=constr} ->
          List.exists (rs_equal rs) constr) itdl in
      List.filter (fun e -> not (rs_ghost e)) itd.itd_fields
    | _ -> []

  let rec print_pat info fmt = function
    | Pwild ->
       fprintf fmt "_"
    | Pident id ->
       print_ident fmt id
    | Pas (p, id) ->
       fprintf fmt "%a as %a" (print_pat info) p print_ident id
    | Por (p1, p2) ->
       fprintf fmt "%a | %a" (print_pat info) p1 (print_pat info) p2
    | Ptuple pl ->
      fprintf fmt "(%a)" (print_list comma (print_pat info)) pl
    | Papp (ls, pl) ->
      match query_syntax info.info_syn ls.ls_name, pl with
      | Some s, _ ->
        syntax_arguments s (print_pat info) fmt pl
      | None, pl ->
        let pjl = let rs = restore_rs ls in get_record info rs in
        match pjl with
        | []  -> print_papp info ls fmt pl
        | pjl ->
          fprintf fmt "@[<hov 2>{ %a }@]"
            (print_list2 semi equal (print_rs info) (print_pat info)) (pjl, pl)

  and print_papp info ls fmt = function
    | []  -> fprintf fmt "%a"      (print_uident info) ls.ls_name
    | [p] -> fprintf fmt "%a %a"   (print_uident info) ls.ls_name
                                   (print_pat info) p
    | pl  -> fprintf fmt "%a (%a)" (print_uident info) ls.ls_name
                                   (print_list comma (print_pat info)) pl

  (** Expressions *)

  let pv_name pv = pv.pv_vs.vs_name

  let ht_rs = Hrs.create 7 (* rec_rsym -> rec_sym *)

  let is_true e = match e.e_node with
    | Eapp (s, []) -> rs_equal s rs_true
    | _ -> false

  let is_false e = match e.e_node with
    | Eapp (s, []) -> rs_equal s rs_false
    | _ -> false

  let rec print_apply ?(paren=false) info rs fmt pvl =
    let isfield =
      match rs.rs_field with
      | None   -> false
      | Some _ -> true in
    let isconstructor () =
      match Mid.find_opt rs.rs_name info.info_mo_known_map with
      | Some {pd_node = PDtype its} ->
        let is_constructor its =
          List.exists (rs_equal rs) its.itd_constructors in
        List.exists is_constructor its
      | _ -> false in
    match query_syntax info.info_convert rs.rs_name,
          query_syntax info.info_syn rs.rs_name, pvl with
    | Some s, _, [{e_node = Econst _}] ->
      let print_constant fmt e = match e.e_node with
        | Econst c ->
          let s = BigInt.to_string (Number.compute_int c) in
          fprintf fmt "%s" s
        | _ -> assert false in
      syntax_arguments s print_constant fmt pvl
    | _, Some s, _ ->
      syntax_arguments s (print_expr ~paren:true info) fmt pvl;
    | _, _, tl when is_rs_tuple rs ->
      fprintf fmt "@[(%a)@]"
        (print_list comma (print_expr info)) tl
    | _,  _, [t1] when isfield ->
      fprintf fmt "%a.%a" (print_expr info) t1 print_ident rs.rs_name
    | _, _, tl when isconstructor () ->
      let pjl = get_record info rs in
      begin match pjl, tl with
      | [], [] ->
        (print_uident info) fmt rs.rs_name
      | [], [t] ->
        fprintf fmt "@[<hov 2>%a %a@]"
          (print_uident info) rs.rs_name (print_expr info) t
      | [], tl ->
        fprintf fmt "@[<hov 2>%a (%a)@]" (print_uident info) rs.rs_name
          (print_list comma (print_expr info)) tl
      | pjl, tl ->
        fprintf fmt "@[<hov 2>{ %a }@]"
          (print_list2 semi equal (print_rs info) (print_expr info)) (pjl, tl)
      end
    | _, _, [] ->
      (print_lident info) fmt rs.rs_name
    | _, _, tl ->
      fprintf fmt (protect_on paren "@[<hov 2>%a %a@]")
        (print_lident info) rs.rs_name
        (print_list space (print_expr ~paren:true info)) tl

  and print_let_def info fmt = function
    | Lvar (pv, e) ->
      fprintf fmt "@[<hov 2>let %a =@ %a@]"
        (print_lident info) (pv_name pv) (print_expr info) e;
    | Lsym (rs, res, args, ef) ->
      fprintf fmt "@[<hov 2>let %a@[%a@] : %a@ =@ @[%a@]@]"
        (print_lident info) rs.rs_name
        (print_list_pre space (print_vs_arg info)) args
        (print_ty info) res (print_expr info) ef;
      forget_vars args
    | Lrec (rdef) ->
      let print_one fst fmt = function
        | { rec_sym = rs1; rec_args = args; rec_exp = e; rec_res = res } ->
          fprintf fmt "@[<hov 2>%s %a@ %a :@ %a@ =@ %a@]"
            (if fst then "let rec" else "and")
            (print_lident info) rs1.rs_name
            (print_list space (print_vs_arg info)) args
            (print_ty info) res (print_expr info) e;
          forget_vars args
      in
      List.iter (fun fd -> Hrs.replace ht_rs fd.rec_rsym fd.rec_sym) rdef;
      print_list_next newline print_one fmt rdef;
      List.iter (fun fd -> Hrs.remove ht_rs fd.rec_rsym) rdef

  and print_enode ?(paren=false) info fmt = function
    | Econst c ->
      let n = Number.compute_int c in
      fprintf fmt "(Z.of_string \"%s\")" (BigInt.to_string n)
    | Evar pvs ->
      (print_lident info) fmt (pv_name pvs)
    | Elet (let_def, e) ->
      fprintf fmt (protect_on paren "@[%a@] in@ @[%a@]")
        (print_let_def info) let_def (print_expr info) e;
      forget_let_defn let_def
    | Eabsurd ->
      fprintf fmt (protect_on paren "assert false (* absurd *)")
    | Ehole -> ()
    | Eapp (rs, []) when rs_equal rs rs_true ->
      fprintf fmt "true"
    | Eapp (rs, []) when rs_equal rs rs_false ->
      fprintf fmt "false"
    | Eapp (rs, [e1; e2]) when rs_equal rs rs_func_app ->
      fprintf fmt (protect_on paren "@[<hov 1>%a %a@]")
        (print_expr info) e1 (print_expr ~paren:true info) e2
    | Eapp (rs, [])  ->
      (* avoids parenthesis around values *)
      fprintf fmt "%a" (print_apply info (Hrs.find_def ht_rs rs rs)) []
    | Eapp (rs, pvl) ->
      begin match query_syntax info.info_convert rs.rs_name, pvl with
        | Some s, [{e_node = Econst _}] ->
          let print_constant fmt e = begin match e.e_node with
            | Econst c ->
              let s = BigInt.to_string (Number.compute_int c) in
              fprintf fmt "%s" s
            | _ -> assert false end in
          syntax_arguments s print_constant fmt pvl
        | _ ->
      fprintf fmt (protect_on paren "%a")
        (print_apply info (Hrs.find_def ht_rs rs rs)) pvl end
    | Ematch (e, pl) ->
      fprintf fmt (protect_on paren "begin match @[%a@] with@\n@[%a@] end")
        (print_expr info) e (print_list newline (print_branch info)) pl
    | Eassign al ->
      let assign fmt (rho, rs, pv) =
        fprintf fmt "@[<hov 2>%a.%a <-@ %a@]"
          print_ident (pv_name rho) print_ident rs.rs_name
          print_ident (pv_name pv) in
      begin match al with
      | [] -> assert false | [a] -> assign fmt a
      | al -> fprintf fmt "@[begin %a end@]" (print_list semi assign) al end
    | Eif (e1, e2, {e_node = Eblock []}) ->
      fprintf fmt (protect_on paren
        "@[<hv>@[<hov 2>if@ %a@]@ then begin@;<1 2>@[%a@] end@]")
        (print_expr info) e1 (print_expr info) e2
    | Eif (e1, e2, e3) when is_false e2 && is_true e3 ->
      fprintf fmt (protect_on paren "not %a") (print_expr info ~paren:true) e1
    | Eif (e1, e2, e3) when is_true e2 ->
      fprintf fmt (protect_on paren "@[<hv>%a || %a@]")
        (print_expr info) e1 (print_expr info) e3
    | Eif (e1, e2, e3) when is_false e3 ->
      fprintf fmt (protect_on paren "@[<hv>%a && %a@]")
        (print_expr info) e1 (print_expr info) e2
    | Eif (e1, e2, e3) ->
      fprintf fmt (protect_on paren
        "@[<hv>@[<hov 2>if@ %a@]@ then@;<1 2>@[%a@]@;<1 0>else@;<1 2>@[%a@]@]")
        (print_expr info) e1 (print_expr info) e2 (print_expr info) e3
    | Eblock [] ->
      fprintf fmt "()"
    | Eblock [e] ->
      print_expr info fmt e
    | Eblock el ->
      fprintf fmt "@[<hv>begin@;<1 2>@[%a@]@ end@]"
        (print_list semi (print_expr info)) el
    | Efun (varl, e) ->
      fprintf fmt (protect_on paren "@[<hov 2>fun %a ->@ %a@]")
        (print_list space (print_vs_arg info)) varl (print_expr info) e
    | Ewhile (e1, e2) ->
      fprintf fmt "@[<hov 2>while %a do@\n%a@ done@]"
        (print_expr info) e1 (print_expr info) e2
    | Eraise (xs, e_opt) ->
      print_raise ~paren info xs fmt e_opt
    (* | Etuple _ -> (\* TODO *\) assert false *)
    | Efor (pv1, pv2, direction, pv3, e) ->
      let print_for_direction fmt = function
        | To -> fprintf fmt "to"
        | DownTo -> fprintf fmt "downto"
      in
      fprintf fmt "@[<hov 2>for %a = %a %a %a do@ @[%a@]@ done@]"
        (print_lident info) (pv_name pv1) (print_lident info) (pv_name pv2)
        print_for_direction direction (print_lident info) (pv_name pv3)
        (print_expr info) e
    | Etry (e, bl) ->
      fprintf fmt
        "@[<hv>@[<hov 2>begin@ try@ %a@] with@]@\n@[<hov>%a@]@\nend"
        (print_expr info) e (print_list newline (print_xbranch info)) bl
    | Eignore e -> fprintf fmt "ignore (%a)" (print_expr info) e
    (* | Enot _ -> (\* TODO *\) assert false *)
    (* | Ebinop _ -> (\* TODO *\) assert false *)
    (* | Ecast _ -> (\* TODO *\) assert false *)

  and print_branch info fmt (p, e) =
    fprintf fmt "@[<hov 4>| %a ->@ @[%a@]@]"
      (print_pat info) p (print_expr info) e

  and print_raise ~paren info xs fmt e_opt =
    match query_syntax info.info_syn xs.xs_name, e_opt with
    | Some s, None ->
      fprintf fmt "raise %s" s
    | Some s, Some e ->
      fprintf fmt (protect_on paren "raise (%a)")
        (syntax_arguments s (print_expr info)) [e]
    | None, None ->
      fprintf fmt (protect_on paren "raise %a")
        (print_uident info) xs.xs_name
    | None, Some e ->
      fprintf fmt (protect_on paren "raise (%a %a)")
        (print_uident info) xs.xs_name (print_expr ~paren:true info) e

  and print_xbranch info fmt (xs, pvl, e) =
    let print_var fmt pv =
      print_lident info fmt (pv_name pv) in
    match query_syntax info.info_syn xs.xs_name with
    | Some s ->
      fprintf fmt "@[<hov 4>| %a ->@ %a@]"
        (syntax_arguments s print_var) pvl (print_expr info ~paren:true) e
    | None   ->
      fprintf fmt "@[<hov 4>| %a %a ->@ %a@]" (print_uident info) (xs.xs_name)
        (print_list nothing print_var) pvl (print_expr info) e

  and print_expr ?(paren=false) info fmt e =
    print_enode ~paren info fmt e.e_node

  let print_type_decl info fst fmt its =
    let print_constr fmt (id, cs_args) =
      match cs_args with
      | [] -> fprintf fmt "@[<hov 4>| %a@]" (print_uident info) id
      | l -> fprintf fmt "@[<hov 4>| %a of %a@]" (print_uident info) id
               (print_list star (print_ty ~paren:false info)) l in
    let print_field fmt (is_mutable, id, ty) =
      fprintf fmt "%s%a: %a;" (if is_mutable then "mutable " else "")
        print_ident id (print_ty ~paren:false info) ty in
    let print_def fmt = function
      | None ->
        ()
      | Some (Ddata csl) ->
        fprintf fmt " =@\n%a" (print_list newline print_constr) csl
      | Some (Drecord fl) ->
        fprintf fmt " = %s{@\n%a@\n}"
          (if its.its_private then "private " else "")
          (print_list newline print_field) fl
      | Some (Dalias ty) ->
        fprintf fmt " =@ %a" (print_ty ~paren:false info) ty
    in
    fprintf fmt "@[<hov 2>%s %a%a%a@]"
      (if fst then "type" else "and") print_tv_args its.its_args
      (print_lident info) its.its_name print_def its.its_def

  let print_decl info fmt = function
    | Dlet ldef ->
      print_let_def info fmt ldef;
      fprintf fmt "@\n"
    | Dtype dl ->
      print_list_next newline (print_type_decl info) fmt dl;
      fprintf fmt "@\n"
    | Dexn (xs, None) ->
       fprintf fmt "exception %a@\n" print_ident xs.xs_name
    | Dexn (xs, Some t)->
      fprintf fmt "@[<hov 2>exception %a of %a@]@\n"
        print_ident xs.xs_name (print_ty ~paren:true info) t
    | Dclone _ ->
      assert false (*TODO*)

  let print_decl info fmt decl =
    let decl_name = get_decl_name decl in
    let decide_print id =
      if query_syntax info.info_syn id = None then begin
        print_decl info fmt decl;
        fprintf fmt "@." end in
    List.iter decide_print decl_name

end

let print_decl pargs ?old ?fname ~flat ({mod_theory = th} as m) fmt d =
  ignore (old);
  let info = {
    info_syn          = pargs.Pdriver.syntax;
    info_convert      = pargs.Pdriver.converter;
    info_current_th   = th;
    info_current_mo   = Some m;
    info_th_known_map = th.th_known;
    info_mo_known_map = m.mod_known;
    info_fname        = Opt.map Compile.clean_name fname;
    flat              = flat;
  } in
  Print.print_decl info fmt d

let fg ?fname m =
  let mod_name = m.mod_theory.th_name.id_string in
  let path     = m.mod_theory.th_path in
  (module_name ?fname path mod_name) ^ ".ml"

let () = Pdriver.register_printer "ocaml"
  ~desc:"printer for OCaml code" fg print_decl

(*
 * Local Variables:
 * compile-command: "make -C ../.. -j3 bin/why3extract.opt"
 * End:
 *)
