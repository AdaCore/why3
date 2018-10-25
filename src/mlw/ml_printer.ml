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

(** {2 Library for code used by different printers} *)

open Format
open Pdriver
open Expr
open Ident
open Term
open Ty
open Ity
open Printer
open Pp
open Theory
open Pmodule
open Compile

open Mltree

type info = {
  info_syn          : syntax_map;
  info_literal      : syntax_map;
  info_current_th   : Theory.theory;
  info_current_mo   : Pmodule.pmodule option;
  info_th_known_map : Decl.known_map;
  info_mo_known_map : Pdecl.known_map;
  info_fname        : string option;
  info_flat         : bool;
  info_current_ph   : string list; (* current path *)
}

let create_info pargs fname ~flat ({mod_theory = th} as m) = {
  info_syn          = pargs.syntax;
  info_literal      = pargs.literal;
  info_current_th   = th;
  info_current_mo   = Some m;
  info_th_known_map = th.th_known;
  info_mo_known_map = m.Pmodule.mod_known;
  info_fname        = fname;
  info_flat         = flat;
  info_current_ph   = [];
}

let add_current_path info s =
  { info with info_current_ph = s :: info.info_current_ph }

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

let check_val_in_drv info ({rs_name = {id_loc = loc}} as rs) =
  (* here [rs] refers to a [val] declaration *)
  match query_syntax info.info_syn rs.rs_name with
  | None (* when info.info_flat *) ->
      Loc.errorm ?loc "Function %a cannot be extracted" Expr.print_rs rs
  | _ -> ()

module type S = sig
  val iprinter : Ident.ident_printer
  val aprinter : Ident.ident_printer
  val tprinter : Ident.ident_printer
  val forget_id : Ident.ident -> unit
  val _forget_ids : Ident.ident list -> unit
  val forget_var : Mltree.var -> unit
  val forget_vars : Mltree.var list -> unit
  val forget_let_defn : Mltree.let_def -> unit
  val forget_pat : Mltree.pat -> unit
  val print_global_ident :
    sanitizer:(string -> string) -> Format.formatter -> Ident.ident -> unit
  val print_path :
    sanitizer:(string -> string) ->
    Format.formatter -> string list * Ident.ident -> unit
  val print_lident : info -> Format.formatter -> Ident.Sid.elt -> unit
  val print_uident : info -> Format.formatter -> Ident.Sid.elt -> unit
  val print_tv : Format.formatter -> Ty.tvsymbol -> unit
  val print_rs : info -> Format.formatter -> Expr.rsymbol -> unit

  (* FIXME : make this independent of the printing function for ident *)
  val check_type_in_drv : info -> ident -> unit

  val print_ty : ?paren:bool -> info -> ty pp
end

module MLPrinter (K: sig val keywords: string list end) = struct
  (* iprinter: local names
     aprinter: type variables
     tprinter: toplevel definitions *)
  let iprinter, aprinter, tprinter =
    let isanitize = sanitizer char_to_alnumus char_to_alnumus in
    let lsanitize = sanitizer char_to_lalnumus char_to_alnumus in
    create_ident_printer K.keywords ~sanitizer:isanitize,
    create_ident_printer K.keywords ~sanitizer:lsanitize,
    create_ident_printer K.keywords ~sanitizer:lsanitize

  let forget_id id = forget_id iprinter id
  let _forget_ids = List.iter forget_id
  let forget_var ((id, _, _): Mltree.var) = forget_id id
  let forget_vars = List.iter forget_var

  let forget_let_defn = function
    | Lvar (v,_) -> forget_id v.pv_vs.vs_name
    | Lsym (s,_,_,_) | Lany (s,_,_) -> forget_rs s
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
      let m = Strings.capitalize (module_name ?fname p t) in
      fprintf fmt "%s.%a" m (print_path ~sanitizer) (q, id)
    with
    | Not_found ->
        let s = id_unique ~sanitizer iprinter id in
        fprintf fmt "%s" s
    | Local ->
        let _, _, q = try Pmodule.restore_path id with Not_found ->
          Theory.restore_path id in
        let q = remove_prefix q (List.rev info.info_current_ph) in
        print_path ~sanitizer fmt (q, id)

  let print_lident = print_qident ~sanitizer:Strings.uncapitalize
  let print_uident = print_qident ~sanitizer:Strings.capitalize

  let print_tv fmt tv =
    fprintf fmt "'%s" (id_unique aprinter tv.tv_name)

  let print_rs info fmt rs =
    fprintf fmt "%a" (print_lident info) rs.rs_name

  let check_type_in_drv info ({id_loc = loc} as ty_id) =
    match query_syntax info.info_syn ty_id with
    | None ->
        Loc.errorm ?loc "Type %a cannot be extracted" (print_lident info) ty_id
    | _ -> ()

  (** Types *)
  let rec print_ty ?(paren=false) info fmt = function
    | Tvar tv ->
        print_tv fmt tv
    | Ttuple [] ->
        fprintf fmt "unit"
    | Ttuple [t] ->
        print_ty ~paren info fmt t
    | Ttuple tl ->
        fprintf fmt (protect_on paren "@[%a@]")
          (print_list star (print_ty ~paren:true info)) tl
    | Tapp (ts, tl) ->
        match query_syntax info.info_syn ts with
        | Some s ->
            fprintf fmt (protect_on paren "%a")
              (syntax_arguments s (print_ty ~paren:true info)) tl
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

end
