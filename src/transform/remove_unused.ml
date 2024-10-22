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

let debug =
  Debug.register_info_flag "remove_unused"
    ~desc:
      "Print@ debugging@ messages@ of@ the@ 'remove_unused'@ transformation."

let meta_depends_remove_constant =
  Theory.(
    register_meta
      ~desc:
        "declares that a constant can be removed by the transformation `remove_unused_keep_constants`"
      "remove_unused:remove_constant" [ MTlsymbol ])

let meta_remove_unused_keep =
  Theory.(
    register_meta
      ~desc:
        "declares that a symbol should never be removed by the transformation `remove_unused`"
      "remove_unused:keep" [ MTlsymbol ])

type used_symbols = {
  keep_constants : bool;
  depends : Ident.Sid.t Decl.Mpr.t;
  closure : Ident.Sid.t Ident.Mid.t;
  constants_to_remove : Ident.Sid.t;
  symbols_to_keep : Ident.Sid.t;
  used_ids : Ident.Sid.t;
}

let pp_id fmt id =
  Format.fprintf fmt "%s" id.Ident.id_string

let pp_sid fmt s =
  Format.fprintf fmt "@[%a@]"  (Pp.print_list Pp.comma pp_id) (Ident.Sid.elements s)


let rec add_used_ids used_symbols ids =
  Debug.dprintf debug "Adding used symbols %a@." pp_sid ids;
  let uids = Ident.Sid.union used_symbols.used_ids ids in
  let new_ids, closure =
    Ident.Sid.fold (fun x ((new_ids, closure) as acc) ->
      try
        let new_ids = Ident.Sid.union new_ids (Ident.Mid.find x closure) in
        Debug.dprintf debug "Found closure for symbol %a@." pp_id x;
        Debug.dprintf debug "Adding symbols %a@." pp_sid new_ids;
        new_ids, Ident.Mid.remove x closure
      with Not_found -> acc) ids (Ident.Sid.empty, used_symbols.closure)
  in
  let r = { used_symbols with used_ids = uids ; closure } in
  if Ident.Sid.is_empty new_ids then r
  else add_used_ids r new_ids

let initial keep_constants =
  let builtins = [ Term.(ps_equ.ls_name); Ty.(ts_int.ts_name) ] in
  let used_ids = List.fold_right Ident.Sid.add builtins Ident.Sid.empty in
  { keep_constants;
    depends = Decl.Mpr.empty;
    closure = Ident.Mid.empty;
    constants_to_remove = Ident.Sid.empty;
    symbols_to_keep = Ident.Sid.empty;
    used_ids }

let add_dependency usymb l =
  match l with
  | Theory.[ MApr pr; MAls ls ] ->
      (* records in `usymb.depends` the declared dependency between
         hypothesis `pr` and symbol `ls` *)
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

let add_removed_constant usymb l =
  match l with
  | Theory.[ MAls ls ] ->
      let id = ls.Term.ls_name in
      { usymb with constants_to_remove = Ident.Sid.add id usymb.constants_to_remove }
  | _ -> assert false (* wrongly typed meta, impossible *)

let add_kept_symbol usymb l =
  match l with
  | Theory.[ MAls ls ] ->
      let id = ls.Term.ls_name in
      { usymb with symbols_to_keep = Ident.Sid.add id usymb.symbols_to_keep }
  | _ -> assert false (* wrongly typed meta, impossible *)

(* The second step of the removal : transverse the task decls and keep
   only the ones we want *)

let metas_keep_if_at_least_one_arg_is_used =
  let open Theory in
  List.fold_left
    (fun acc mt -> Smeta.add mt acc)
    Smeta.empty
    [meta_range;
     meta_float]

let do_removal_unused_decl usymb (td : Theory.tdecl) : Theory.tdecl option =
  let open Ident in
  let open Decl in
  let open Theory in
  match td.td_node with
  | Meta (mt, [ MApr pr; MAls _ls ]) when meta_equal mt Pdecl.meta_depends ->
      if Sid.mem pr.pr_name usymb.used_ids then Some td else None
  | Meta (mt, margs) ->
      let kept_arg at_least_one = function
        | MApr pr -> Sid.mem pr.pr_name usymb.used_ids
        | MAty ty ->
            let s = Decl.get_used_syms_ty ty in
            if at_least_one then
              not (Ident.Sid.(is_empty (inter s usymb.used_ids)))
            else
              Sid.subset s usymb.used_ids
        | MAts ts -> Sid.mem ts.Ty.ts_name usymb.used_ids
        | MAls ls -> Sid.mem ls.Term.ls_name usymb.used_ids
        | MAstr _ | MAint _ | MAid _ -> true
      in
      if Smeta.mem mt metas_keep_if_at_least_one_arg_is_used then
        if List.exists (kept_arg true) margs then Some td else None
      else
      if List.for_all (kept_arg false) margs then Some td else None
  | Use _ | Clone _ -> Some td
  | Decl d -> (
      match d.d_node with
      | Dprop (_, pr, _t) ->
          if Sid.mem pr.pr_name usymb.used_ids then Some td else None
      | Ddata _ | Dlogic _ | Dtype _ | Dparam _ | Dind _ ->
          if Sid.is_empty (Sid.inter d.d_news usymb.used_ids) then None
          else Some td)


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
        | Decl d ->
            begin
            match d.d_node with
            | Dprop (_, pr, _t) -> (
                try
                  let s = Mpr.find pr usymb.depends in
                  Debug.dprintf debug "@[checking if hypothesis %a is needed:@\n"
                    pp_id pr.pr_name;
                  Debug.dprintf debug "  declared dependencies: %a@\n"
                    pp_sid s;
                  Debug.dprintf debug "  current needed symbols: %a@\n"
                    pp_sid usymb.used_ids;
                  let b = Sid.is_empty (Sid.inter s usymb.used_ids) in
                  Debug.dprintf debug "  -> removing? %b@]@." b;
                  if b then
                    let ids = Sid.add pr.pr_name (Decl.get_used_syms_decl d) in
                    { usymb with closure =
                                   Sid.fold (fun x acc ->
                                       let ids = try
                                           Sid.union (Mid.find x acc) ids
                                         with Not_found -> ids
                                       in
                                       Debug.dprintf debug "Recording closure for symbol %a -> %a@."
                                         pp_id x pp_sid ids;
                                       Mid.add x ids acc) s usymb.closure }
                  else
                    raise Not_found
                with Not_found ->
                  let ids = Decl.get_used_syms_decl d in
                  let usymb = add_used_ids usymb ids in
                  {
                    usymb with
                    used_ids = Sid.add pr.pr_name usymb.used_ids;
                  })
            | Ddata _ | Dlogic _ | Dtype _ | Dparam _ | Dind _ ->
                let keep_symbol ls =
                  (* a symbol is kept if either
                     - it is explicitly marked with "remove_unused:keep", or
                     - it is a constant and we want to keep constants, unless
                       it is explicitly marked with "remove_unused:remove_constant"
                  *)
                  Ident.Sid.mem ls.Term.ls_name usymb.symbols_to_keep ||
                  (ls.Term.ls_args = [] && usymb.keep_constants &&
                   not (Ident.Sid.mem ls.Term.ls_name usymb.constants_to_remove))
                in
                let declares_a_needed_symbol =
                  match d.d_node with
                  | Dparam ls -> keep_symbol ls
                  | Dlogic dl ->
                      List.exists
                        (fun (ls, _) -> keep_symbol ls) dl
                  | Dprop _ | Ddata _ | Dtype _ | Dind _ -> false
                in
                let is_needed =
                  declares_a_needed_symbol
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
      Task.on_meta Pdecl.meta_depends add_dependency (initial keep_constants) t
    in
    let usymb =
      Task.on_meta meta_depends_remove_constant add_removed_constant usymb t
    in
    let usymb =
      Task.on_meta meta_remove_unused_keep add_kept_symbol usymb t
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
