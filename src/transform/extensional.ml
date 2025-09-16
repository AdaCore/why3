(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ty
open Decl
open Term

let trans mts =
  let rec aux sign t =
    match t.t_node with
    | Tapp (fs, ([{ t_ty = Some { ty_node = Tyapp (ts, _) } } as t1;t2] as tl))
          when not sign && ls_equal fs ps_equ ->
        begin match Mts.find_opt ts mts with
        | Some ls when ls.ls_value = None ->
           begin try
               t_attr_copy t (t_app ls tl None)
             with e ->
               Format.eprintf "exception: %a@." Exn_printer.exn_printer e;
               let (libpath,theory,qualid) = Theory.restore_path ls.ls_name in
               Format.eprintf "ls = %a,@ ls.ls_args = @[%a@]@."
                 (Pp.print_list Pp.dot Pp.print_string) (libpath @ [theory] @ qualid)
                 (Pp.print_list Pp.comma Pretty.print_ty) ls.ls_args;
               Format.eprintf "t1 = %a,@ ty1 = %a@." Pretty.print_term t1
                 (Pp.print_option Pretty.print_ty) t1.t_ty;
               Format.eprintf "t2 = %a,@ ty2 = %a@." Pretty.print_term t2
                 (Pp.print_option Pretty.print_ty) t2.t_ty;
               assert false;
           end
        | Some ls ->
            t_attr_copy t (t_equ (t_app_infer ls [t1]) (t_app_infer ls [t2]))
        | None -> t
        end
    | Tapp _ -> t
    | _ when t.t_ty = None -> t_map_sign aux sign t
    | _ -> t in
  aux

let meta = Theory.register_meta "extensionality" [Theory.MTlsymbol]
  ~desc:"Use the given symbol in place of an equality (if binary predicate),@ or apply it to both sides of an equality (if unary function),@ assuming the resulting expression is well-typed."

let compute_mts sls =
  Sls.fold (fun ls mts ->
      match ls.ls_args, ls.ls_value with
      | [{ ty_node = Tyapp (ts, _) }; _], None | [{ ty_node = Tyapp (ts, _) }], Some _ ->
         if Mts.mem ts mts then
           raise (Theory.IllFormedMeta (meta, Format.asprintf "Already defined meta for type `%a`"
                                                Pretty.print_ts ts))
         else
           Mts.add ts ls mts
      | _ ->
          raise (Theory.IllFormedMeta (meta, Format.asprintf "'%a' is neither a binary predicate nor a unary function" Pretty.print_ls ls))
    ) sls Mts.empty

let rewrite_prop mts p v t =
  let sign = match p with Paxiom | Plemma -> true | Pgoal -> false in
  [create_prop_decl p v (trans mts sign t)]

let extensionality_all =
  Trans.on_tagged_ls meta (fun sls ->
      let mts = compute_mts sls in
      Trans.decl (fun d ->
          match d.d_node with
          | Dprop (p, v, t) -> rewrite_prop mts p v t
          | _ -> [d]
        ) None
    )

let extensionality_goal =
  Trans.on_tagged_ls meta (fun sls ->
      let mts = compute_mts sls in
      Trans.decl (fun d ->
          match d.d_node with
          | Dprop (Pgoal, v, t) -> rewrite_prop mts Pgoal v t
          | _ -> [d]
        ) None
    )

let () =
  Trans.register_transform "extensionality_all" extensionality_all
    ~desc:"Apply an extensionality property@ to some equalities of the task,@ when they occur in positive position."

let () =
  Trans.register_transform "extensionality_goal" extensionality_goal
    ~desc:"Apply an extensionality property@ to goal if it is an equality."
