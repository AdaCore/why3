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

  let forget_tvs () =
    forget_all iprinter

  let forget_id vs = forget_id iprinter vs
  let _forget_ids = List.iter forget_id
  let forget_var (id, _, _) = forget_id id
  let forget_vars = List.iter forget_var

  let forget_let_defn = function
  | Lvar (v,_) -> forget_pv v
  | Lsym (s,_,_) -> forget_rs s
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

  let print_qident ~sanitizer info fmt id =
    try
      let _, _, q =
        try Pmodule.restore_path id
        with Not_found -> Theory.restore_path id in
      let s = String.concat "__" q in
      let s = Ident.sanitizer char_to_alpha char_to_alnumus s in
      let s = sanitizer s in
      let s = if is_ocaml_keyword s then s ^ "_renamed" else s in
      if Sid.mem id info.info_current_th.th_local ||
         Opt.fold (fun _ m -> Sid.mem id m.Pmodule.mod_local)
           false info.info_current_mo
      then fprintf fmt "%s" s
      else
        (* let fname = if lp = [] then info.info_fname else None in *)
        let m = Strings.capitalize "m" in
        fprintf fmt "%s.%s" m s
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

  (** Types *)

  let rec print_ty ?(paren=false) info fmt = function
    | Tvar tv ->
      print_tv fmt tv
    | Ttuple [] ->
      fprintf fmt "unit"
    | Ttuple tl ->
      fprintf fmt (protect_on paren "@[%a@]")
        (print_list star (print_ty ~paren:false info)) tl
    | Tapp (ts, [t1; t2]) when id_equal ts ts_func.ts_name ->
      fprintf fmt (protect_on paren "@[%a ->@ %a@]")
        (print_ty ~paren:true info) t1 (print_ty info) t2
    | Tapp (ts, tl) ->
      begin match query_syntax info.info_syn ts with
        | Some s -> syntax_arguments s (print_ty info) fmt tl
        | None   ->
          begin match tl with
            | [] ->
              print_ident fmt ts
            | [ty] ->
              fprintf fmt (protect_on paren "%a@ %a")
                (print_ty ~paren:true info) ty print_ident ts
            | tl ->
              fprintf fmt (protect_on paren "(%a)@ %a")
                (print_list comma (print_ty ~paren:false info)) tl
                print_ident ts
          end
      end

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
        let rs = restore_rs ls in
        let pjl = get_record info rs in
        match pjl, pl with
        | [], []  ->
          fprintf fmt "%a" (print_uident info) ls.ls_name
        | [], [p] ->
          fprintf fmt "%a %a"
            (print_uident info) ls.ls_name (print_pat info) p
        | [], _   ->
          fprintf fmt "%a (%a)"
            (print_uident info) ls.ls_name
            (print_list comma (print_pat info)) pl
        | _, _    ->
          let rec print_list2 sep sep_m print1 print2 fmt (l1, l2) =
          match l1, l2 with
          | x1 :: r1, x2 :: r2 ->
            print1 fmt x1; sep_m fmt (); print2 fmt x2; sep fmt ();
            print_list2 sep sep_m print1 print2 fmt (r1, r2)
          | _ -> ()
        in
        let print_rs info fmt rs =
          fprintf fmt "%a" (print_lident info) rs.rs_name in
        fprintf fmt "@[<hov 2>{ %a}@]"
          (print_list2 semi equal (print_rs info) (print_pat info)) (pjl, pl)

  (** Expressions *)

  let pv_name pv = pv.pv_vs.vs_name

  let ht_rs = Hrs.create 7 (* rec_rsym -> rec_sym *)

  let rec print_apply info fmt rs pvl =
    let isfield =
      match rs.rs_field with
      | None -> false
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
    | Some s, _, _ ->
      let print_constant fmt e = match e.e_node with
        | Econst c ->
          let c = BigInt.to_int (Number.compute_int c) in
          fprintf fmt "%d" c
        | _ -> print_expr info fmt e in
      syntax_arguments s print_constant fmt pvl
    | _, Some s, _ ->
      syntax_arguments s (print_expr info) fmt pvl
    | _, _, tl when is_rs_tuple rs ->
      fprintf fmt "@[(%a)@]"
        (print_list comma (print_expr info)) tl
    | _, _, [] ->
      print_ident fmt rs.rs_name
    | _,  _, [t1] when isfield ->
      fprintf fmt "%a.%a" (print_expr info) t1 print_ident rs.rs_name
    | _, _, tl when isconstructor () ->
      let pjl = get_record info rs in
      if pjl = [] then
        fprintf fmt "@[<hov 2>%a (%a)@]"
          print_ident rs.rs_name (print_list comma (print_expr info)) tl
      else
        let rec print_list2 sep sep_m print1 print2 fmt (l1, l2) =
          match l1, l2 with
          | x1 :: r1, x2 :: r2 ->
            print1 fmt x1; sep_m fmt (); print2 fmt x2; sep fmt ();
            print_list2 sep sep_m print1 print2 fmt (r1, r2)
          | _ -> () in
        let print_rs info fmt rs =
          fprintf fmt "%a" (print_lident info) rs.rs_name in
        fprintf fmt "@[<hov 2>{ %a}@]"
          (print_list2 semi equal (print_rs info) (print_expr info)) (pjl, tl)
    | _, _, tl ->
      fprintf fmt "@[<hov 2>%a %a@]"
        print_ident rs.rs_name (print_list space (print_expr info)) tl

  and print_let_def info fmt = function
    | Lvar (pv, e) ->
      fprintf fmt "@[<hov 2>let %a =@ %a@]"
        (print_lident info) (pv_name pv) (print_expr info) e;
    | Lsym (rs, args, ef) ->
      fprintf fmt "@[<hov 2>let %a %a@ =@ @[%a@]@]"
        (print_lident info) rs.rs_name
        (print_list space (print_vs_arg info)) args
        (print_expr info) ef;
      forget_vars args
    | Lrec (rdef) ->
      let print_one fst fmt = function
        | { rec_sym = rs1; rec_args = args; rec_exp = e } ->
          fprintf fmt "@[<hov 2>%s %a@ %a@ =@ %a@]"
            (if fst then "let rec" else "and")
            (print_lident info) rs1.rs_name
            (print_list space (print_vs_arg info)) args
            (print_expr info) e;
          forget_vars args;
          forget_tvs ()
      in
      List.iter (fun fd -> Hrs.replace ht_rs fd.rec_rsym fd.rec_sym) rdef;
      print_list_next newline print_one fmt rdef;
      List.iter (fun fd -> Hrs.remove ht_rs fd.rec_rsym) rdef

  and print_enode info fmt = function
    | Econst c ->
      let n = Number.compute_int c in
      fprintf fmt "(Z.of_string \"%s\")" (BigInt.to_string n)
    | Evar pvs ->
      (print_lident info) fmt (pv_name pvs)
    | Elet (let_def, e) ->
      fprintf fmt "@[%a@] in@ %a"
        (print_let_def info) let_def
        (print_expr info) e;
      forget_let_defn let_def
    | Eabsurd ->
      fprintf fmt "assert false (* absurd *)"
    | Eapp (s, []) when rs_equal s rs_true ->
      fprintf fmt "true"
    | Eapp (s, []) when rs_equal s rs_false ->
      fprintf fmt "false"
    | Eapp (s, [e1; e2]) when rs_equal s rs_func_app ->
      fprintf fmt "@[<hov 1>%a %a@]"
        (print_expr info) e1 (print_expr info) e2
    | Eapp (s, pvl) ->
      print_apply info fmt (Hrs.find_def ht_rs s s) pvl
    | Ematch (e, pl) ->
      fprintf fmt "begin match @[%a@] with@\n@[<hov>%a@] end"
        (print_expr info) e (print_list newline (print_branch info)) pl
    | Eassign [(rho, rs, pv)] ->
      fprintf fmt "%a.%a <-@ %a"
        print_ident (pv_name rho) print_ident rs.rs_name
        print_ident (pv_name pv)
    | Eif (e1, e2, {e_node = Eblock []}) ->
      fprintf fmt
        "@[<hv>@[<hov 2>if@ %a@]@ then begin@;<1 2>@[%a@] end@]"
        (print_expr info) e1 (print_expr info) e2
    | Eif (e1, e2, e3) ->
      fprintf fmt
        "@[<hv>@[<hov 2>if@ %a@]@ then@;<1 2>@[%a@]@;<1 0>else@;<1 2>@[%a@]@]"
        (print_expr info) e1 (print_expr info) e2 (print_expr info) e3
    | Eblock [] ->
      fprintf fmt "()"
    | Eblock [e] ->
      print_expr info fmt e
    | Eblock el ->
      fprintf fmt "@[<hv>begin@;<1 2>@[%a@]@ end@]"
        (print_list semi (print_expr info)) el
    | Efun (varl, e) ->
      fprintf fmt "@[<hov 2>(fun %a ->@ %a)@]"
        (print_list space (print_vs_arg info)) varl (print_expr info) e
    | Ewhile (e1, e2) ->
      fprintf fmt "@[<hov 2>while %a do@ %a@ done@]"
        (print_expr info) e1 (print_expr info) e2
    | Eraise (Xident id, None) -> (* FIXME : check exceptions in driver *)
      fprintf fmt "raise %a" (print_uident info) id
    | Eraise (Xident id, Some e) ->
      fprintf fmt "(raise %a %a)"
        (print_uident info) id (print_expr info) e
    | Etuple _ -> (* TODO *) assert false
    | Efor (pv1, pv2, direction, pv3, e) ->
      let print_for_direction fmt = function
        | To -> fprintf fmt "to"
        | DownTo -> fprintf fmt "downto"
      in
      fprintf fmt "@[<hov 2>for %a = %a %a %a do@ @[%a@]@ done@]"
        (print_lident info) (pv_name pv1)
        (print_lident info) (pv_name pv2)
        print_for_direction direction
        (print_lident info) (pv_name pv3)
        (print_expr info) e
    | Etry _ -> (* TODO *) assert false
    | Enot _ -> (* TODO *) assert false
    | Ebinop _ -> (* TODO *) assert false
    | Ecast _ -> (* TODO *) assert false
    | Eassign _ -> (* TODO *) assert false

  and print_branch info fmt (p, e) =
    fprintf fmt "@[<hov 4>| %a ->@ @[%a@]@]"
      (print_pat info) p (print_expr info) e

  and print_expr info fmt e =
    print_enode info fmt e.e_node

  let print_type_decl info fmt its =
    let print_constr fmt (id, cs_args) =
      match cs_args with
      | [] ->
         fprintf fmt "@[<hov 4>| %a@]"
                 print_ident id (* FIXME: first letter must be uppercase
                                       -> print_uident *)
      | l ->
         fprintf fmt "@[<hov 4>| %a of %a@]"
                 print_ident id (* FIXME: print_uident *)
                 (print_list star (print_ty ~paren:false info)) l in
    let print_field fmt (is_mutable, id, ty) =
      fprintf fmt "%s%a: %a;"
              (if is_mutable then "mutable " else "")
              print_ident id
              (print_ty ~paren:false info) ty in
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
      (if true then "type" else "and") (* FIXME: mutual recursive types *)
      print_tv_args its.its_args
      print_ident its.its_name  (* FIXME: first letter must be lowercase
                                   -> print_lident *)
      print_def its.its_def

  let print_decl info fmt = function
    | Dlet (ldef) ->
      print_let_def info fmt ldef;
      forget_tvs ();
      fprintf fmt "@\n@\n"
    | Dtype dl ->
       print_list newline (print_type_decl info) fmt dl;
       fprintf fmt "@\n@\n"
    | Dexn (xs, None) ->
       fprintf fmt "exception %a@\n@\n" print_ident xs.xs_name
    | Dexn (xs, Some t) ->
       fprintf fmt "@[<hov 2>exception %a of %a@]@\n@\n"
               print_ident xs.xs_name (print_ty ~paren:true info) t
end

let extract_module pargs ?old fmt ({mod_theory = th} as m) =
  ignore (pargs);
  ignore (old);
  ignore (m);
  let info = {
    info_syn          = pargs.Pdriver.syntax;
    info_convert      = pargs.Pdriver.converter;
    info_current_th   = th;
    info_current_mo   = Some m;
    info_th_known_map = th.th_known;
    info_mo_known_map = m.mod_known;
    info_fname        = None; (* TODO *)
  } in
  (* fprintf fmt "(\*@\n%a@\n*\)@\n" print_module m; *)
  fprintf fmt
    "(* This file has been generated from Why3 module %a *)@\n@\n"
    Print.print_module_name m;
  let mdecls = Translate.module_ info m in
  print_list nothing (Print.print_decl info) fmt mdecls;
  fprintf fmt "@."


let fg ?fname m =
  let mod_name = m.Pmodule.mod_theory.Theory.th_name.id_string in
  match fname with
  | None   -> mod_name ^ ".ml"
  | Some f ->
    (* TODO: replace with Filename.remove_extension
     * after migration to OCaml 4.04+ *)
    let remove_extension s =
      try Filename.chop_extension s
      with Invalid_argument _ -> s
    in
    let f = Filename.basename f in
    (remove_extension f) ^ "__" ^ mod_name ^ ".ml"

let () = Pdriver.register_printer "ocaml"
  ~desc:"printer for OCaml code" fg extract_module

(*
 * Local Variables:
 * compile-command: "make -C ../.. -j3 bin/why3extract.opt"
 * End:
 *)
