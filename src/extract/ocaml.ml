(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Printer for extracted OCaml code *)

open Format
open Ident
open Pp
open Ity
open Term
open Expr
open Ty
open Theory
open Pmodule
open Wstdlib
open Pdecl
open Printer

type info = {
  info_syn          : syntax_map;
  info_literal      : syntax_map;
  info_current_th   : Theory.theory;
  info_current_mo   : Pmodule.pmodule option;
  info_th_known_map : Decl.known_map;
  info_mo_known_map : Pdecl.known_map;
  info_fname        : string option;
  info_flat         : bool;
  info_prec         : int list Mid.t;
  info_current_ph   : string list; (* current path *)
}

(* operator precedence, from http://caml.inria.fr/pub/docs/manual-ocaml/expr.html
   ! ? ~ ...   | 1
   . .( .[ .~  | 2
   #...        | 3
   fun/cstr app| 4 left
   -_ -._      | 5
   ** lsl lsr  | 6 right
   * / %       | 7 left
   + -         | 8 left
   ::          | 9 right
   @ ^         | 10 right
   = < > !=    | 11 left
   & &&        | 12 right
   or ||       | 13 right
   ,           | 14
   <- :=       | 15 right
   if          | 16
   ;           | 17 right
   let fun try | 18 *)

(* pattern precedence, from http://caml.inria.fr/pub/docs/manual-ocaml/patterns.html#pattern

  ..           | 1
  lazy         | 2
  cstr/tag app | 3 right
  ::           | 4 right
  ,            | 5
  |            | 6 left
  as           | 7
 *)

module Print = struct

  open Mltree

  (* extraction attributes *)
  let optional_arg = create_attribute "ocaml:optional"
  let named_arg = create_attribute "ocaml:named"
  let ocaml_remove = create_attribute "ocaml:remove"

  let is_optional ~attrs =
    Sattr.mem optional_arg attrs

  let is_named ~attrs =
    Sattr.mem named_arg attrs

  let is_ocaml_remove ~attrs =
    Ident.Sattr.mem ocaml_remove attrs

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

  let _is_ocaml_keyword =
    let h = Hstr.create 16 in
    List.iter (fun s -> Hstr.add h s ()) ocaml_keywords;
    Hstr.mem h

  let char_to_alnumusquote c =
    match c with '\'' -> "\'" | _ -> char_to_alnumus c

  (* iprinter: local names
     aprinter: type variables
     tprinter: toplevel definitions *)
  let iprinter, aprinter, tprinter =
    let isanitize = sanitizer char_to_alnumus char_to_alnumusquote in
    let lsanitize = sanitizer char_to_lalnumus char_to_alnumusquote in
    create_ident_printer ocaml_keywords ~sanitizer:isanitize,
    create_ident_printer ocaml_keywords ~sanitizer:lsanitize,
    create_ident_printer ocaml_keywords ~sanitizer:lsanitize

  let forget_id id = forget_id iprinter id
  let _forget_ids = List.iter forget_id
  let forget_var (id, _, _) = forget_id id
  let forget_vars = List.iter forget_var

  let forget_let_defn = function
    | Lvar (v,_) -> forget_id v.pv_vs.vs_name
    | Lsym (s,_,_,_,_) | Lany (s,_,_,_) -> forget_rs s
    | Lrec rdl -> List.iter (fun fd -> forget_rs fd.rec_sym) rdl

  let rec forget_pat = function
    | Pwild -> ()
    | Pvar {vs_name=id} -> forget_id id
    | Papp (_, pl) | Ptuple pl -> List.iter forget_pat pl
    | Por (p1, p2) -> forget_pat p1; forget_pat p2
    | Pas (p, _) -> forget_pat p

  let print_global_ident ~sanitizer fmt id =
    let s = id_unique ~sanitizer tprinter id in
    Ident.forget_id tprinter id;
    fprintf fmt "%s" s

  let print_path ~sanitizer fmt (q, id) =
    assert (List.length q >= 1);
    match Lists.chop_last q with
    | [], _ -> print_global_ident ~sanitizer fmt id
    | q, _  ->
        fprintf fmt "%a.%a"
          (print_list dot string) q (print_global_ident ~sanitizer) id

  let rec remove_prefix acc current_path = match acc, current_path with
    | [], _ | _, [] -> acc
    | p1 :: _, p2 :: _ when p1 <> p2 -> acc
    | _ :: r1, _ :: r2 -> remove_prefix r1 r2

  let is_local_id info id =
    Sid.mem id info.info_current_th.th_local ||
    Opt.fold (fun _ m -> Sid.mem id m.Pmodule.mod_local)
      false info.info_current_mo

  exception Local

  let print_qident ~sanitizer info fmt id =
    try
      if info.info_flat then raise Not_found;
      if is_local_id info id then raise Local;
      let p, t, q =
        try Pmodule.restore_path id with Not_found -> Theory.restore_path id in
      let fname = if p = [] then info.info_fname else None in
      let m = Strings.capitalize (Ml_printer.module_name ?fname p t) in
      fprintf fmt "%s.%a" m (print_path ~sanitizer) (q, id)
    with
    | Not_found ->
        let s = id_unique ~sanitizer iprinter id in
        fprintf fmt "%s" s
    | Local ->
        let _, _, q =
          try Pmodule.restore_path id with Not_found ->
            Theory.restore_path id in
        let q = remove_prefix q (List.rev info.info_current_ph) in
        print_path ~sanitizer fmt (q, id)

  let print_lident = print_qident ~sanitizer:Strings.uncapitalize
  let print_uident = print_qident ~sanitizer:Strings.capitalize

  let print_tv ~use_quote fmt tv =
    fprintf fmt (if use_quote then "'%s" else "%s")
      (id_unique aprinter tv.tv_name)

  let protect_on ?(boxed=false) ?(be=false) b s =
    if b
    then if be
         then "begin@;<1 2>@["^^ s ^^ "@] end"
         else "@[<1>(" ^^ s ^^ ")@]"
    else if not boxed then "@[<hv>" ^^ s ^^ "@]"
    else s

  let star fmt () = fprintf fmt " *@ "

  let rec print_list2 sep sep_m print1 print2 fmt (l1, l2) =
    match l1, l2 with
    | [x1], [x2] ->
        print1 fmt x1; sep_m fmt (); print2 fmt x2
    | x1 :: r1, x2 :: r2 ->
        print1 fmt x1; sep_m fmt (); print2 fmt x2; sep fmt ();
        print_list2 sep sep_m print1 print2 fmt (r1, r2)
    | _ -> ()

  let complex_syntax s =
    String.contains s '%' || String.contains s ' ' || String.contains s '('

  let print_record_proj info fmt rs =
    match query_syntax info.info_syn rs.rs_name with
    | None ->
       fprintf fmt "%a" (print_lident info) rs.rs_name
    | Some s when complex_syntax s ->
       Loc.errorm ?loc:rs.rs_name.id_loc "Unsupported: complex record field"
    | Some s -> fprintf fmt "%s" s

  (** Types *)

  let rec print_ty ~use_quote ?(paren=false) info fmt = function
    | Tvar tv ->
        print_tv ~use_quote fmt tv
    | Ttuple [] ->
        fprintf fmt "unit"
    | Ttuple [t] ->
        print_ty  ~use_quote ~paren info fmt t
    | Ttuple tl ->
        fprintf fmt (protect_on paren "@[%a@]")
          (print_list star (print_ty ~use_quote ~paren:true info)) tl
    | Tarrow (t1, t2) ->
        fprintf fmt (protect_on paren "%a -> %a")
          (print_ty ~use_quote ~paren info) t1
          (print_ty ~use_quote ~paren info) t2
    | Tapp (ts, tl) ->
        match query_syntax info.info_syn ts with
        | Some s when complex_syntax s ->
            fprintf fmt (protect_on paren "%a")
              (syntax_arguments s (print_ty ~use_quote ~paren:true info)) tl
        | Some s ->
           fprintf fmt (protect_on paren "%a%s")
             (print_list_suf space (print_ty ~use_quote ~paren:true info)) tl
             s
        | None   ->
            match tl with
            | [] ->
                (print_lident info) fmt ts
            | [ty] ->
                fprintf fmt (protect_on paren "%a@ %a")
                  (print_ty ~use_quote ~paren:true info) ty (print_lident info)
                  ts
            | tl ->
                fprintf fmt (protect_on paren "(%a)@ %a")
                  (print_list comma (print_ty ~use_quote ~paren:false info)) tl
                  (print_lident info) ts

  let print_vsty_opt info fmt id ty =
    fprintf fmt "?%s:(%a:@ %a)" id.id_string (print_lident info) id
      (print_ty ~use_quote:false ~paren:false info) ty

  let print_vs_opt info fmt id =
    fprintf fmt "?%s:%a" id.id_string (print_lident info) id

  let print_vsty_named info fmt id ty =
    fprintf fmt "~%s:(%a:@ %a)" id.id_string (print_lident info) id
      (print_ty ~use_quote:false ~paren:false info) ty

  let print_vs_named info fmt id =
    fprintf fmt "~%s:%a" id.id_string (print_lident info) id

  let print_vsty info fmt (id, ty, _) =
    let attrs = id.id_attrs in
    if is_optional ~attrs then print_vsty_opt info fmt id ty
    else if is_named ~attrs then print_vsty_named info fmt id ty
    else fprintf fmt "(%a:@ %a)" (print_lident info) id
      (print_ty ~use_quote:false ~paren:false info) ty

  let print_vsty_opt_fun info fmt id ty = match ty with
    | Tapp (id_ty, [arg]) ->
        assert (query_syntax info.info_syn id_ty = Some "%1 option");
        fprintf fmt "?%s:%a" id.id_string
          (print_ty ~use_quote:false ~paren:false info) arg
    | _ ->
       Loc.errorm "invalid optional argument of type %a"
         (print_ty ~use_quote:false ~paren:false info) ty

  let print_vsty_named_fun info fmt id ty =
    fprintf fmt "%s:%a" id.id_string
      (print_ty ~use_quote:false ~paren:false info) ty

  let print_vsty_fun info fmt (id, ty, _) =
    let attrs = id.id_attrs in
    if is_optional ~attrs then print_vsty_opt_fun info fmt id ty
    else if is_named ~attrs then print_vsty_named_fun info fmt id ty
    else fprintf fmt "%a" (print_ty ~use_quote:false ~paren:true info) ty

  let print_vs_fun info fmt id =
    let attrs = id.id_attrs in
    if is_optional ~attrs then print_vs_opt info fmt id
    else if is_named ~attrs then print_vs_named info fmt id
    else print_lident info fmt id

  let print_tv_arg = print_tv
  let print_tv_args ~use_quote fmt = function
    | []   -> ()
    | [tv] -> fprintf fmt "%a@ " (print_tv_arg ~use_quote) tv
    | tvl  ->
        fprintf fmt "(%a)@ " (print_list comma (print_tv_arg ~use_quote)) tvl

  let print_vs_arg info fmt vs =
    fprintf fmt "@[%a@]" (print_vsty info) vs

  let get_record info rs =
    match Mid.find_opt rs.rs_name info.info_mo_known_map with
    | Some {pd_node = PDtype itdl} ->
        let eq_rs {itd_constructors} =
          List.exists (rs_equal rs) itd_constructors in
        let itd = List.find eq_rs itdl in
        List.filter (fun e -> not (rs_ghost e)) itd.itd_fields
    | _ -> []

  let rec print_pat info prec fmt = function
    | Pwild ->
        fprintf fmt "_"
    | Pvar {vs_name=id} ->
        (print_lident info) fmt id
    | Pas (p, {vs_name=id}) ->
        fprintf fmt (protect_on (prec < 7) "%a as %a") (print_pat info 6) p
          (print_lident info) id
    | Por (p1, p2) ->
        fprintf fmt (protect_on (prec < 6) "%a | %a")
          (print_pat info 6) p1
          (print_pat info 5) p2
    | Ptuple pl ->
        fprintf fmt "(%a)" (print_list comma (print_pat info 4)) pl
    | Papp (ls, pl) ->
        match query_syntax info.info_syn ls.ls_name with
        | Some s when complex_syntax s || pl = [] ->
           fprintf fmt (protect_on (prec < 4) "%a")
             (syntax_arguments s (print_pat info 1)) pl
        | Some s ->
           fprintf fmt (protect_on (prec < 3) "%s (%a)")
             s (print_list comma (print_pat info 4)) pl
        | None ->
            let pjl = let rs = restore_rs ls in get_record info rs in
            match pjl with
            | []  -> print_papp info ls fmt pl
            | pjl ->
                fprintf fmt (protect_on (prec < 3) "@[<hov 2>{ %a }@]")
                  (print_list2 semi equal (print_record_proj info)
                  (print_pat info 6)) (pjl, pl)

  and print_papp info ls fmt = function
    | []  -> fprintf fmt "%a"      (print_uident info) ls.ls_name
    | [p] -> fprintf fmt "%a %a"   (print_uident info) ls.ls_name
               (print_pat info 3) p
    | pl  -> fprintf fmt "%a (%a)" (print_uident info) ls.ls_name
               (print_list comma (print_pat info 4)) pl

  (** Expressions *)

  let pv_name pv = pv.pv_vs.vs_name
  let print_pv info fmt pv = print_lident info fmt (pv_name pv)

  let is_field rs =
      match rs.rs_field with
      | None   -> false
      | Some _ -> true

  let check_val_in_drv info loc id =
    (* here [rs] refers to a [val] declaration *)
    match query_syntax info.info_syn id with
    | None (* when info.info_flat *) ->
        Loc.errorm ?loc "Symbol %a cannot be extracted" (print_lident info) id
    | _ -> ()

  let is_mapped_to_int info ity =
    match ity.ity_node with
    | Ityapp ({ its_ts = ts }, _, _) ->
        query_syntax info.info_syn ts.ts_name = Some "int"
    | _ -> false

  let print_constant fmt e = begin match e.e_node with
    | Econst (Constant.ConstInt c) ->
        let v = c.Number.il_int in
        let s = BigInt.to_string v in
        if BigInt.lt v BigInt.zero then fprintf fmt "(%s)" s
        else fprintf fmt "%s" s
    | Econst (Constant.ConstStr s) ->
       Constant.print_string_def fmt s
    | _ -> assert false end

  let print_for_direction fmt = function
    | To     -> fprintf fmt "to"
    | DownTo -> fprintf fmt "downto"

  let rec print_apply_args info fmt = function
    | expr :: exprl, pv :: pvl ->
        if is_optional ~attrs:(pv_name pv).id_attrs then
          begin match expr.e_node with
            | Eapp (rs, _, false)
              when query_syntax info.info_syn rs.rs_name = Some "None" -> ()
            | _ -> fprintf fmt "?%s:%a" (pv_name pv).id_string
                     (print_expr info 1) expr end
        else if is_named ~attrs:(pv_name pv).id_attrs then
          fprintf fmt "~%s:%a" (pv_name pv).id_string
            (print_expr info 1) expr
        else fprintf fmt "%a" (print_expr info 3) expr;
        if exprl <> [] then fprintf fmt "@ ";
        print_apply_args info fmt (exprl, pvl)
    | expr :: exprl, [] ->
        fprintf fmt "%a" (print_expr info 3) expr;
        print_apply_args info fmt (exprl, [])
    | [], _ -> ()

  and print_apply info prec rs fmt pvl =
    let isconstructor () =
      match Mid.find_opt rs.rs_name info.info_mo_known_map with
      | Some {pd_node = PDtype its} ->
          let is_constructor its =
            List.exists (rs_equal rs) its.itd_constructors in
          List.exists is_constructor its
      | _ -> false in
    if rs_equal rs rs_ref_proj
    then
      match pvl with
      | [x] -> fprintf fmt "!%a" (print_expr info 1) x
      | _ -> assert false
    else
      match query_syntax info.info_syn rs.rs_name, pvl with
      | Some s, _ when complex_syntax s ->
          let arity = syntax_arity s in
          if List.length pvl = arity then begin
            let p = Mid.find rs.rs_name info.info_prec in
            let s =
              if p = [] || prec < List.hd p
              then Format.sprintf "(%s)" s
              else s in
            syntax_arguments_prec s (print_expr info) p fmt pvl
          end else begin
            let ids =
              let id i = id_register (id_fresh ("x" ^ string_of_int i)) in
              Lists.init arity id in
            fprintf fmt (protect_on (prec < 4) "@[(fun %a -> %a)@]%t%a")
              (print_list space (print_lident info)) ids
              (syntax_arguments s (print_lident info)) ids
              (fun fmt -> if pvl = [] then () else fprintf fmt "@;<1 2>")
              (print_apply_args info) (pvl, [])
          end
      | _, [t1] when is_field rs ->
          fprintf fmt (protect_on (prec < 2) "%a.%a")
            (print_expr info 2) t1 (print_record_proj info) rs
      | Some s, _ ->
         fprintf fmt (protect_on (prec < 4) "%s %a") s
           (print_apply_args info) (pvl, rs.rs_cty.cty_args)
      | None, [t] when is_rs_tuple rs ->
          print_expr info prec fmt t
      | None, tl when is_rs_tuple rs ->
         fprintf fmt "@[(%a)@]" (print_list comma (print_expr info 14)) tl
      | None, tl when isconstructor () ->
         let pjl = get_record info rs in
         begin match pjl, tl with
         | [], [] ->
            (print_uident info) fmt rs.rs_name
         | [], [t] ->
             fprintf fmt (protect_on (prec < 4) "%a %a") (print_uident info) rs.rs_name
               (print_expr info 2) t
         | [], tl ->
             fprintf fmt (protect_on (prec < 4) "%a (%a)") (print_uident info) rs.rs_name
               (print_list comma (print_expr info 14)) tl
         | pjl, tl -> let equal fmt () = fprintf fmt " =@ " in
                      fprintf fmt "@[<hov 2>{ %a }@]"
                        (print_list2 semi equal (print_record_proj info)
                           (print_expr info 17)) (pjl, tl) end
      | None, [] ->
         (print_lident info) fmt rs.rs_name
      | _, tl ->
         fprintf fmt (protect_on (prec < 4) "%a %a")
           (print_lident info) rs.rs_name
           (print_apply_args info) (tl, rs.rs_cty.cty_args)

  and print_svar fmt s =
    print_list space (print_tv ~use_quote:false) fmt (Stv.elements s)

  and print_fun_type_args info fmt (args, s, res, e) =
    if Stv.is_empty s then
      fprintf fmt "@[%a@]:@ %a@ =@ @[<hv>%a@]"
        (print_list_suf space (print_vs_arg info)) args
        (print_ty ~use_quote:false info) res
        (print_expr ~opr:false info 18) e
    else
      let id_args = List.map (fun (id, _, _) -> id) args in
      let arrow fmt () = fprintf fmt " ->@ " in
      let start fmt () = fprintf fmt "fun@ " in
      fprintf fmt ":@ @[<h>type @[%a@]. @[%a@ %a@]@] =@ \
                   @[<hv 2>@[%a@]%a@]"
        print_svar s
        (print_list_suf arrow (print_vsty_fun info)) args
        (print_ty ~use_quote:false ~paren:true info) res
        (print_list_delim ~start ~stop:arrow ~sep:space (print_vs_fun info))
          id_args
        (print_expr ~opr:false info 18) e

  and print_let_def ?(functor_arg=false) info fmt = function
    | Lvar (pv, e) ->
        fprintf fmt "@[<hov 2>let %a =@ %a@]"
          (print_lident info) (pv_name pv) (print_expr ~opr:false info 18) e
    | Lsym (rs, svar, res, args, ef) ->
        fprintf fmt "@[<hov 2>let %a %a@]"
          (print_lident info) rs.rs_name
          (print_fun_type_args info) (args,svar,res,ef);
       forget_vars args
    | Lrec rdef ->
        let print_one fst fmt = function
          | { rec_sym = rs1; rec_args = args; rec_exp = e;
              rec_res = res; rec_svar = s } ->
              fprintf fmt "@[<hov 2>%s %a %a@]"
                (if fst then "let rec" else "and")
                (print_lident info) rs1.rs_name
                (print_fun_type_args info) (args, s, res, e);
              forget_vars args in
        print_list_next newline print_one fmt rdef;
    | Lany (rs, _svar, res, []) when functor_arg ->
        fprintf fmt "@[<hov 2>val %a : %a@]"
          (print_lident info) rs.rs_name
          (print_ty ~use_quote:true info) res;
    | Lany (rs, _svar, res, args) when functor_arg ->
        let print_ty_arg info fmt (_, ty, _) =
          fprintf fmt "@[%a@]" (print_ty ~use_quote:true info) ty in
        fprintf fmt "@[<hov 2>val %a : @[%a@] ->@ %a@]"
          (print_lident info) rs.rs_name
          (print_list arrow (print_ty_arg info)) args
          (print_ty ~use_quote:true info) res;
        forget_vars args
    | Lany ({rs_name}, _, _, _) -> check_val_in_drv info rs_name.id_loc rs_name

  and print_expr ?(boxed=false) ?(opr=true) ?(be=false) info prec fmt e =
    let protect_on_be ?(boxed=false) b s = protect_on ~boxed ~be:true b s in
    let protect_on ?(boxed=false) b s = protect_on ~boxed ~be b s in
    match e.e_node with
    | Econst (Constant.ConstInt c) ->
        let n = c.Number.il_int in
        let n = BigInt.to_string n in
        let id = match e.e_ity with
          | I { ity_node = Ityapp ({its_ts = ts},_,_) } -> ts.ts_name
          | _ -> assert false in
        (match query_syntax info.info_literal id with
         | Some s -> syntax_arguments s print_constant fmt [e]
         | None when n = "0" -> fprintf fmt "Z.zero"
         | None when n = "1" -> fprintf fmt "Z.one"
         | None   -> fprintf fmt (protect_on (prec < 4) "Z.of_string \"%s\"") n)
    | Econst (Constant.ConstStr s) ->
        Constant.print_string_def fmt s
    | Econst (Constant.ConstReal _) -> assert false (* TODO *)
    | Evar pvs ->
        (print_lident info) fmt (pv_name pvs)
    | Elet (let_def, e) ->
        fprintf fmt (protect_on ~boxed (opr && prec < 18) "@[%a in@]@;%a")
          (print_let_def info) let_def (print_expr ~boxed:true ~opr info 18) e;
        forget_let_defn let_def
    | Eabsurd ->
        fprintf fmt (protect_on (opr && prec < 4) "assert false (* absurd *)")
    | Eapp (rs, [], _) when rs_equal rs rs_true ->
        fprintf fmt "true"
    | Eapp (rs, [], _) when rs_equal rs rs_false ->
        fprintf fmt "false"
    | Eapp (rs, [e], _)
         when query_syntax info.info_syn rs.rs_name = Some "%1" ->
        print_expr ~boxed ~opr ~be info prec fmt e
    | Eapp (rs, pvl, _) ->
        print_apply info prec rs fmt pvl
    | Ematch (e1, [p, e2], []) ->
        fprintf fmt (protect_on (opr && prec < 18) "let %a =@ %a in@ %a")
          (print_pat info 6) p (print_expr ~opr:false info 18) e1
          (print_expr ~opr info 18) e2
    | Ematch (e, pl, []) ->
        fprintf fmt
          (if prec < 18 && opr
           then "@[<hv>@[<hv 2>begin@ match@ %a@]@ with@]@\n@[<hv>%a@]@\nend"
           else "@[<hv>@[<hv 2>match@ %a@]@ with@]@\n@[<hv>%a@]")
          (print_expr info 18) e
          (print_list newline (print_branch info)) pl
    | Eassign al ->
        let assign fmt (rho, rs, e) =
          if rs_equal rs rs_ref_proj
          then fprintf fmt "@[<hv 2>%a :=@ %a@]"
                 (print_lident info) (pv_name rho) (print_expr info 15) e
          else if is_field rs
          then fprintf fmt "@[<hv 2>%a.%a <-@ %a@]"
                 (print_lident info) (pv_name rho) (print_record_proj info) rs
                (print_expr info 15) e
          else
            match query_syntax info.info_syn rs.rs_name with
            | Some s ->
               fprintf fmt "@[<hv 2>%a <-@ %a@]"
                (syntax_arguments s (print_lident info)) [pv_name rho]
                (print_expr info 15) e
            | None ->
               fprintf fmt "@[<hv 2>%a.%a <-@ %a@]"
                 (print_lident info) (pv_name rho) (print_lident info) rs.rs_name
                 (print_expr info 15) e in
        begin match al with
        | [] -> assert false | [a] -> assign fmt a
        | al -> fprintf fmt "@[begin %a end@]" (print_list semi assign) al end
    | Eif (e1, e2, {e_node = Eblock []}) ->
        fprintf fmt
          (protect_on (opr && prec < 16)
             "@[<hv>@[<hv 2>if@ %a@]@ then %a@]")
          (print_expr ~opr:false info 15) e1 (print_expr ~be:true info 15) e2
    | Eif (e1, e2, e3) when is_false e2 && is_true e3 ->
        fprintf fmt (protect_on (prec < 4) "not %a")
          (print_expr info 3) e1
    | Eif (e1, e2, e3) when is_true e2 ->
        fprintf fmt (protect_on (prec < 13) "@[<hv>%a || %a@]")
          (print_expr info 12) e1 (print_expr info 13) e3
    | Eif (e1, e2, e3) when is_false e3 ->
        fprintf fmt (protect_on (prec < 12) "@[<hv>%a && %a@]")
          (print_expr info 11) e1 (print_expr info 12) e2
    | Eif (e1, e2, e3) ->
        fprintf fmt (protect_on (opr && prec < 16)
                       "@[<hv>@[<hv>if %a@]\
                        @;<1 0>@[<hv 2>then@;%a@]\
                        @;<1 0>@[<hv 2>else@;%a@]@]")
          (print_expr ~opr:false info 15) e1
          (print_expr ~opr:false ~be:true info 15) e2
          (print_expr ~be:true info 15) e3
    | Eblock [] ->
        fprintf fmt "()"
    | Eblock [e] ->
        print_expr ~be info prec fmt e
    | Eblock el ->
        let semibreak fmt () = fprintf fmt ";@ " in
        let rec aux fmt = function
          | [] -> assert false
          | [e] -> print_expr ~opr:false info 18 fmt e
          | h::t -> print_expr info 17 fmt h; semibreak fmt (); aux fmt t in
        fprintf fmt
          (if prec < 17
           then "@[<hv>begin@;<1 2>@[<hv>%a@]@ end@]"
           else "@[<hv>@[<hv>%a@]@]") aux el
    | Efun (varl, e) ->
        fprintf fmt (protect_on (opr && prec < 18) "@[<hv 2>fun %a ->@ %a@]")
          (print_list space (print_vs_arg info)) varl (print_expr info 17) e
    | Ewhile (e1, e2) ->
        fprintf fmt "@[<hv 2>while %a do@\n%a@;<1 -2>done@]"
          (print_expr info 18) e1 (print_expr ~opr:false info 18) e2
    | Eraise (xs, e_opt) ->
        print_raise ~paren:(prec < 4) info xs fmt e_opt
    | Efor (pv1, pv2, dir, pv3, e) ->
        if is_mapped_to_int info pv1.pv_ity then begin
          fprintf fmt "@[<hv 2>for %a = %a %a %a do@ @[%a@]@ done@]"
            (print_lident info) (pv_name pv1) (print_lident info) (pv_name pv2)
            print_for_direction dir (print_lident info) (pv_name pv3)
            (print_expr ~opr:false info 18) e;
          forget_pv pv1 end
        else
          let for_id  = id_register (id_fresh "for_loop_to") in
          let cmp, op = match dir with
            | To     -> "Z.leq", "Z.succ"
            | DownTo -> "Z.geq", "Z.pred" in
          fprintf fmt (protect_on_be (opr && prec < 18)
                         "@[<hv 2>let rec %a %a =@ \
                          @[<hv 2>if %s %a %a@]@;<1 0>\
                          @[<hv 2>then begin@ %a;@ %a (%s %a)@;<1 -2>end@]@;<1 -2>in %a %a@]")
          (* let rec *) (print_lident info) for_id (print_pv info) pv1
          (* if      *)  cmp (print_pv info) pv1 (print_pv info) pv3
          (* then    *) (print_expr info 16) e (print_lident info) for_id
                        op (print_pv info) pv1
          (* in      *) (print_lident info) for_id (print_pv info) pv2
    | Ematch (e, [], xl) ->
        fprintf fmt
          (if prec < 18 && opr
           then "@[<hv>@[<hv 2>begin@ try@ %a@]@ with@]@\n@[<hv>%a@]@\nend"
           else "@[<hv>@[<hv 2>try@ %a@]@ with@]@\n@[<hv>%a@]")
          (print_expr ~be:true ~opr:false info 17) e
          (print_list newline (print_xbranch info false)) xl
    | Ematch (e, bl, xl) ->
        fprintf fmt
          (if (prec < 18 && opr)
           then "@[begin match @[%a@]@ with@]@\n@[<hv>%a@\n%a@]@\nend"
           else "@[<hv>match @[%a@]@ with@]@\n@[<hv>%a@\n%a@]")
          (print_expr ~be:true ~opr:false info 17) e
          (print_list newline (print_branch info)) bl
          (print_list newline (print_xbranch info true)) xl
    | Eexn (xs, None, e) ->
        fprintf fmt "@[<hv>let exception %a in@\n%a@]"
          (print_uident info) xs.xs_name (print_expr info 18) e
    | Eexn (xs, Some t, e) ->
        fprintf fmt "@[<hv>let exception %a of %a in@\n%a@]"
          (print_uident info) xs.xs_name (print_ty ~use_quote:false ~paren:true info) t
          (print_expr info 18) e
    | Eignore e ->
        fprintf fmt (protect_on (prec < 4)"ignore %a")
          (print_expr info 3) e

  and print_branch info fmt (p, e) =
    fprintf fmt "@[<hv 2>| %a ->@ @[%a@]@]"
      (print_pat info 5) p (print_expr info 17) e;
    forget_pat p

  and print_raise ~paren info xs fmt e_opt =
    match query_syntax info.info_syn xs.xs_name, e_opt with
    | Some s, None ->
        fprintf fmt "raise (%s)" s
    | Some s, Some e when complex_syntax s ->
        fprintf fmt (protect_on paren "raise %a")
          (syntax_arguments_prec s (print_expr info) []) [e]
    | Some s, Some e ->
        fprintf fmt (protect_on paren "raise (%s %a)")
          s (print_expr info 3) e
    | None, None ->
        fprintf fmt (protect_on paren "raise %a")
          (print_uident info) xs.xs_name
    | None, Some e ->
        fprintf fmt (protect_on paren "raise (%a %a)")
          (print_uident info) xs.xs_name (print_expr info 3) e

  and print_xbranch info case fmt (xs, pvl, e) =
    let print_exn fmt () =
      if case then fprintf fmt "exception " else fprintf fmt "" in
    let print_var fmt pv = print_lident info fmt (pv_name pv) in
    match query_syntax info.info_syn xs.xs_name, pvl with
    | Some s, _ when complex_syntax s || pvl = [] ->
        fprintf fmt "@[<hov 4>| %a%a ->@ %a@]"
          print_exn () (syntax_arguments s print_var) pvl
          (print_expr info 17) e
    | Some s, _ -> fprintf fmt "@[<hov 4>| %a%s (%a) ->@ %a@]"
        print_exn () s
        (print_list comma print_var) pvl (print_expr info 17) e
    | None, [] -> fprintf fmt "@[<hov 4>| %a%a ->@ %a@]"
        print_exn () (print_uident info) xs.xs_name (print_expr info 17) e
    | None, [pv] -> fprintf fmt "@[<hov 4>| %a%a %a ->@ %a@]"
        print_exn () (print_uident info) xs.xs_name print_var pv
        (print_expr info 17) e
    | None, pvl -> fprintf fmt "@[<hov 4>| %a%a (%a) ->@ %a@]"
        print_exn () (print_uident info) xs.xs_name
        (print_list comma print_var) pvl (print_expr info 17) e

  let print_type_decl info fst fmt its =
    let print_constr fmt (id, cs_args) =
      match cs_args with
      | [] -> fprintf fmt "@[<hov 4>| %a@]" (print_uident info) id
      | l -> fprintf fmt "@[<hov 4>| %a of %a@]" (print_uident info) id
               (print_list star (print_ty ~use_quote:true ~paren:false info)) l in
    let print_field fmt (is_mutable, id, ty) =
      fprintf fmt "%s%a: @[%a@];" (if is_mutable then "mutable " else "")
        (print_lident info) id (print_ty ~use_quote:true ~paren:false info) ty in
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
          fprintf fmt " =@ %a" (print_ty ~use_quote:true ~paren:false info) ty
      | Some (Drange _) ->
          fprintf fmt " =@ Z.t"
      | Some (Dfloat _) ->
          assert false (*TODO*)
    in
    let attrs = its.its_name.id_attrs in
    if not (is_ocaml_remove ~attrs) then
      fprintf fmt "@[<hov 2>@[%s %a%a@]%a@]"
        (if fst then "type" else "and") (print_tv_args ~use_quote:true) its.its_args
        (print_lident info) its.its_name print_def its.its_def

  let rec is_signature_decl info = function
    | Dtype _ -> true
    | Dlet (Lany _) -> true
    | Dval _ -> true
    | Dlet _ -> false
    | Dexn _ -> true
    | Dmodule (_, dl) -> is_signature info dl

  and is_signature info dl =
    List.for_all (is_signature_decl info) dl

  let extract_functor_args info dl =
    let rec extract args = function
      | Dmodule (_, []) :: dl -> extract args dl
      | Dmodule (x, dlx) :: dl when is_signature info dlx ->
          extract ((x, dlx) :: args) dl
      | dl -> List.rev args, dl in
    extract [] dl

  let print_top_val ?(functor_arg=false) info fmt ({pv_vs}, ty) =
    if functor_arg then
      fprintf fmt "@[<hov 2>val %a : %a@]"
        (print_lident info) pv_vs.vs_name (print_ty ~use_quote:true info) ty
    else
      check_val_in_drv info pv_vs.vs_name.id_loc pv_vs.vs_name

  let rec print_decl ?(functor_arg=false) info fmt = function
    | Dlet ldef ->
        print_let_def info ~functor_arg fmt ldef
    | Dval (pv, ty) ->
        print_top_val info ~functor_arg fmt (pv, ty)
    | Dtype dl ->
        print_list_next newline (print_type_decl info) fmt dl
    | Dexn (xs, None) ->
        fprintf fmt "exception %a" (print_uident info) xs.xs_name
    | Dexn (xs, Some t)->
        fprintf fmt "@[<hov 2>exception %a of %a@]"
          (print_uident info) xs.xs_name (print_ty ~use_quote:true ~paren:true info) t
    | Dmodule (s, dl) ->
        let args, dl = extract_functor_args info dl in
        let info = { info with info_current_ph = s :: info.info_current_ph } in
        fprintf fmt "@[@[<hov 2>module %s%a@ =@]@\n@[<hov 2>struct@ %a@]@ end" s
          (print_functor_args info) args
          (print_list newline2 (print_decl info)) dl

  and print_functor_args info fmt args =
    let print_sig info fmt dl =
      fprintf fmt "sig@ %a@ end"
        (print_list newline (print_decl info ~functor_arg:true)) dl in
    let print_pair fmt (s, dl) =
      let info = { info with info_current_ph = s :: info.info_current_ph } in
      fprintf fmt "(%s:@ %a)" s (print_sig info) dl in
    fprintf fmt "%a" (print_list space print_pair) args

  let print_decl info fmt decl =
    (* avoids printing the same decl for mutually recursive decls *)
    let memo = Hashtbl.create 64 in
    let decl_name = get_decl_name decl in
    let decide_print id =
      if query_syntax info.info_syn id = None &&
         not (Hashtbl.mem memo decl) then begin
        Hashtbl.add memo decl (); print_decl info fmt decl;
        fprintf fmt "@\n@." end in
    List.iter decide_print decl_name

end

let print_decl =
  let memo = Hashtbl.create 16 in
  fun pargs ?old ?fname ~flat ({mod_theory = th} as m) fmt d ->
    ignore (old);
    let info = {
      info_syn          = pargs.Pdriver.syntax;
      info_literal      = pargs.Pdriver.literal;
      info_current_th   = th;
      info_current_mo   = Some m;
      info_th_known_map = th.th_known;
      info_mo_known_map = m.mod_known;
      info_fname        = Opt.map Ml_printer.clean_name fname;
      info_flat         = flat;
      info_prec         = pargs.Pdriver.prec;
      info_current_ph   = [];
      } in
    if not (Hashtbl.mem memo d) then begin Hashtbl.add memo d ();
      Print.print_decl info fmt d end

let ng suffix ?fname m =
  let mod_name = m.mod_theory.th_name.id_string in
  let path     = m.mod_theory.th_path in
  (Ml_printer.module_name ?fname path mod_name) ^ suffix

let ocaml_printer = Pdriver.{
    desc = "printer for Ocaml code";
    implem_printer = {
        filename_generator = ng ".ml";
        decl_printer = print_decl ~flat:false;
        prelude_printer = default_prelude_printer;
        header_printer = dummy_border_printer;
        footer_printer = dummy_border_printer;
      };
    flat_printer = {
        filename_generator = ng ".ml";
        decl_printer = print_decl ~flat:true;
        prelude_printer = default_prelude_printer;
        header_printer = dummy_border_printer;
        footer_printer = dummy_border_printer;
      };
    interf_printer = None
  }

let () = Pdriver.register_printer "ocaml" ocaml_printer
