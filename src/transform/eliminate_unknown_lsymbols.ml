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

open Term
open Decl
open Theory
open Task

let debug = Debug.register_info_flag "eliminate_unknown_lsymbols"
  ~desc:"Print@ debugging@ messages@ of@ the@ eliminate_unknown_types@ transformation."

let abstraction (keep : lsymbol -> bool) =
  let term_table = Hterm.create 257 in
  let extra_decls = ref [] in

  let rec abstract t : term =
    match t.t_node with
    | Tvar _ | Tconst _ | Tapp(_,[]) | Ttrue | Tfalse -> t
    | Tapp (ls,_) when keep ls ->
      t_map abstract t
    | Tlet _ | Tnot _ | Tbinop _ | Tif _ ->
      t_map abstract t
    | _ ->
      if Debug.test_flag debug then
        Format.printf "eliminate@ %a@." Pretty.print_term t;
      let (ls, tabs) = try Hterm.find term_table t with Not_found ->
        let ls = create_lsymbol (Ident.id_fresh "abstr") [] t.t_ty in
        let tabs = t_app ls [] t.t_ty in
        Hterm.add term_table t (ls, tabs);
        ls, tabs in
      extra_decls := ls :: !extra_decls;
      tabs
  in

  let abstract_decl (d : decl) : decl list =
    let d = decl_map abstract d in
    let l = List.fold_left
        (fun acc ls -> create_param_decl ls :: acc)
        [d] !extra_decls in
    extra_decls := [];
    l
  in

  Trans.decl abstract_decl None

let syntactic_transform transf =
  Trans.bind (Trans.fold (fun hd acc ->
  match hd.task_decl.td_node with
  | Decl { d_node = Dlogic ((ls,_def)::[]) } -> Sls.add ls acc
  | _ -> acc) Sls.empty)
  (fun decl ->
  Trans.on_meta Printer.meta_syntax_logic (fun metas ->
    let symbols = List.fold_left (fun acc meta_arg ->
      match meta_arg with
      | [Theory.MAls ls; Theory.MAstr _; Theory.MAint _] -> Sls.add ls acc
      | _ -> assert false) decl metas in
    let keep ls =  Sls.exists (ls_equal ls) symbols in
    Trans.compose (transf keep)
      (Trans.decl (fun d -> match d.d_node with
           | Dparam l when not (keep l || l.ls_args = []) -> []
           | _ -> [d]) None)))

let () =
  Trans.register_transform "eliminate_unknown_lsymbols"
    (syntactic_transform abstraction)
    ~desc:"Abstract@ applications@ of@ non-built-in@ symbols@ with@ \
      constants.@ Used@ by@ the@ Gappa@ pretty-printer."
