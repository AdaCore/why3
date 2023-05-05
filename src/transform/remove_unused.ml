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

let _debug =
  Debug.register_info_flag "remove_unused"
    ~desc:
      "Print@ debugging@ messages@ of@ the@ 'remove_unused'@ transformation."

let meta_depends =
  Theory.(
    register_meta
      ~desc:
        "declares an dependency between a proposition and a logic symbol. Used \
         by the transformation `remove_unused`"
      "remove_unused:dependency" [ MTprsymbol; MTlsymbol ])

type used_symbols = {
  keep_constants : bool;
  depends : Ident.Sid.t Decl.Mpr.t;
  closure : Ident.Sid.t Ident.Mid.t;
  used_ids : Ident.Sid.t;
}

let rec add_used_ids used_symbols ids =
  let uids = Ident.Sid.union used_symbols.used_ids ids in
  let new_ids, closure =
    Ident.Sid.fold (fun x ((new_ids, closure) as acc) ->
      try
        let new_ids = Ident.Sid.union new_ids (Ident.Mid.find x closure) in
        new_ids, Ident.Mid.remove x closure
      with Not_found -> acc) ids (Ident.Sid.empty, used_symbols.closure)
  in
  let r = { used_symbols with used_ids = uids ; closure } in
  if Ident.Sid.is_empty new_ids then r
  else add_used_ids r new_ids

let initial keep_constants =
  let builtins = [ Term.(ps_equ.ls_name); Ty.(ts_int.ts_name) ] in
  let used_ids = List.fold_right Ident.Sid.add builtins Ident.Sid.empty in
  { keep_constants; depends = Decl.Mpr.empty; closure = Ident.Mid.empty; used_ids }

let add_dependency usymb l =
  match l with
  | Theory.[ MApr pr; MAls ls ] ->
      let id = ls.Term.ls_name in
      let d =
        Decl.Mpr.change
          (function
            | None -> Some (Ident.Sid.singleton id)
            | Some s -> Some (Ident.Sid.add id s))
          pr usymb.depends
      in
      { usymb with depends = d }
  | _ -> assert false (* wrongly typed meta, impossible *)

(* The second step of the removal : transverse the task decls and keep
   only the ones we want *)
let do_removal_unused_decl usymb (td : Theory.tdecl) : Theory.tdecl option =
  let open Ident in
  let open Decl in
  let open Theory in
  match td.td_node with
  | Meta (mt, [ MApr pr; MAls _ls ]) when meta_equal mt meta_depends ->
      if Sid.mem pr.pr_name usymb.used_ids then Some td else None
  | Meta (_, margs) ->
      let kept_arg = function
        | MApr pr -> Sid.mem pr.pr_name usymb.used_ids
        | MAty ty ->
            let s = Decl.get_used_syms_ty ty in
            Sid.subset s usymb.used_ids
        | MAts ts -> Sid.mem ts.Ty.ts_name usymb.used_ids
        | MAls ls -> Sid.mem ls.Term.ls_name usymb.used_ids
        | MAstr _ | MAint _ | MAid _ -> true
      in
      if List.for_all kept_arg margs then Some td else None
  | Use _ | Clone _ -> Some td
  | Decl d -> (
      match d.d_node with
      | Dprop (_, pr, _t) ->
          if Sid.mem pr.pr_name usymb.used_ids then Some td else None
      | Ddata _ | Dlogic _ | Dtype _ | Dparam _ | Dind _ ->
          if Sid.is_empty (Sid.inter d.d_news usymb.used_ids) then None
          else Some td)
(*
let metas_remove =
  let open Theory in
  List.fold_left
    (fun acc mt -> Smeta.add mt acc)
    Smeta.empty
    [meta_depends ;
     Printer.meta_remove_prop;
     Printer.meta_remove_logic;
     Printer.meta_remove_type]
*)
(* The first step of the removal : compute the used identifiers *)
let rec compute_used_ids usymb task : used_symbols =
  let open Theory in
  match task with
  | None -> usymb
  | Some Task.{ task_decl = td; task_prev = ta } ->
      let open Ident in
      let open Decl in
      let usymb =
        match td.td_node with
        | Use _ | Clone _ | Meta _ -> usymb
          (*
        | Meta (mt, _) when Smeta.mem mt metas_remove -> usymb
        | Meta (_, margs) ->
            let used_ids =
              List.fold_left
                (fun acc arg ->
                   match arg with
                   | MApr pr -> Sid.add pr.pr_name acc
                   | MAty ty ->
                       let s = Decl.get_used_syms_ty ty in
                       Sid.union s acc
                   | MAts ts -> Sid.add ts.Ty.ts_name acc
                   | MAls ls -> Sid.add ls.Term.ls_name acc
                   | MAstr _ | MAint _ | MAid _ -> acc)
                usymb.used_ids margs
            in
            { usymb with used_ids }
*)
        | Decl d ->
            begin
            match d.d_node with
            | Dprop (_, pr, _t) -> (
                try
                  let s = Mpr.find pr usymb.depends in
                  if Sid.is_empty (Sid.inter s usymb.used_ids) then
                  let ids = Sid.add pr.pr_name (Decl.get_used_syms_decl d) in
                  { usymb with closure = Sid.fold (fun x acc -> Mid.add x ids acc) s usymb.closure }
                  else raise Not_found
                with Not_found ->
                  let ids = Decl.get_used_syms_decl d in
                  let usymb = add_used_ids usymb ids in
                  {
                    usymb with
                    used_ids = Sid.add pr.pr_name usymb.used_ids;
                  })
            | Ddata _ | Dlogic _ | Dtype _ | Dparam _ | Dind _ ->
                let declares_a_constant =
                  match d.d_node with
                  | Dparam ls -> ls.Term.ls_args = []
                  | Dlogic dl ->
                      List.exists (fun (ls, _) -> ls.Term.ls_args = []) dl
                  | Dprop _ | Ddata _ | Dtype _ | Dind _ -> false
                in
                let is_needed =
                  (declares_a_constant && usymb.keep_constants)
                  || not (Sid.is_empty (Sid.inter d.d_news usymb.used_ids))
                in
                if is_needed then
                  let ids = Decl.get_used_syms_decl d in
                  add_used_ids usymb (Sid.union ids d.d_news)
                else
                  usymb
          end
      in
      compute_used_ids usymb ta

(* wrapper to call Trans.fold *)
let do_removal_wrapper usymb : Task.task Trans.trans =
  let o th t =
    match do_removal_unused_decl usymb th.Task.task_decl with
    | None -> t
    | Some td -> Task.add_tdecl t td
  in
  Trans.fold o None

let remove_unused_wrapper keep_constants =
  let o t =
    let usymb =
      Task.on_meta meta_depends add_dependency (initial keep_constants) t
    in
    let usymb = compute_used_ids usymb t in
    Trans.apply (do_removal_wrapper usymb) t
  in
  Trans.store o

let remove_unused_keep_constants = remove_unused_wrapper true
let remove_unused = remove_unused_wrapper false

let () =
  Trans.register_transform "remove_unused_keep_constants"
    remove_unused_keep_constants
    ~desc:
      "Remove@ unused@ type@ symbols@ and@ unused@ non-constant@ logic@ symbols"

let () =
  Trans.register_transform "remove_unused" remove_unused
    ~desc:"Remove@ unused@ type@ symbols@ and@ unused@ logic@ symbols"
