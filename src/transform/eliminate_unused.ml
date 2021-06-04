(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)


open Ty
open Term
open Decl

let debug = Debug.register_info_flag "eliminate_unused"
  ~desc:"Print@ debugging@ messages@ of@ the@ \
    'eliminate_unused'@ transformation."


type used_symbols = {
    keep_logic_symbols : bool;
    used_ts : Sts.t;
    used_ls : Sls.t;
  }

let initial b =
  { keep_logic_symbols = b;
    used_ts = Sts.add ts_int Sts.empty;
    used_ls = Sls.add ps_equ Sls.empty }

let used_symbols_in_type =
  ty_s_fold
    (fun acc ts ->
      { acc with used_ts = Sts.add ts acc.used_ts})

let used_type_symbols_in_lsymbol us ls =
  let us = Opt.fold used_symbols_in_type us ls.ls_value in
  List.fold_left used_symbols_in_type us ls.ls_args

let used_symbols_in_term =
  t_s_fold
    used_symbols_in_type
    (fun acc ls ->
      { acc with used_ls = Sls.add ls acc.used_ls})

let rec eliminate_unused_decl acc task : Task.task =
  match task with
  | None -> None
  | Some Task.{ task_decl = td ; task_prev = ta } ->
     match td.Theory.td_node with
     | Theory.Use _ | Theory.Clone _ | Theory.Meta _ ->
        let ta = eliminate_unused_decl acc ta in
        Task.add_tdecl ta td
     | Theory.Decl d ->
        match d.d_node with
        | Dprop (_,_,t) ->
           let acc = used_symbols_in_term acc t in
           let ta = eliminate_unused_decl acc ta in
           Task.add_decl ta d
        | Ddata ddl ->
           if List.exists
                (fun (ts,cl) ->
                  Sts.mem ts acc.used_ts ||
                    List.exists
                      (fun (ls,pl) ->
                        Sls.mem ls acc.used_ls ||
                          List.exists
                            (function None -> false
                                    | Some ls -> Sls.mem ls acc.used_ls)
                            pl)
                      cl)
                ddl
           then
             let acc =
               List.fold_left
                 (fun acc (_,cl) ->
                   List.fold_left
                     (fun acc (ls,_) -> used_type_symbols_in_lsymbol acc ls)
                     acc cl)
                 acc ddl
             in
             let ta = eliminate_unused_decl acc ta in
             Task.add_decl ta d
           else
             begin
               let l =
                 List.fold_left (fun acc (ts,_) -> ts::acc) [] ddl
               in
               Debug.dprintf debug "[eliminate_unused] removing datatypes %a@."
                 (Pp.print_list Pp.comma Pretty.print_ts) l;
               eliminate_unused_decl acc ta
             end
     | Dlogic dl ->
        if acc.keep_logic_symbols || List.exists (fun (ls,_) -> Sls.mem ls acc.used_ls) dl
        then
          let acc =
            List.fold_left
              (fun acc (ls,lsdef) ->
                let acc = used_type_symbols_in_lsymbol acc ls in
                let _,t = open_ls_defn lsdef in
                used_symbols_in_term acc t)
              acc dl
          in
          let ta = eliminate_unused_decl acc ta in
          Task.add_decl ta d
        else
          begin
            let l =
              List.fold_left (fun acc (ls,_) -> ls::acc) [] dl
            in
            Debug.dprintf debug "[eliminate_unused] removing logic decls %a@."
              (Pp.print_list Pp.comma Pretty.print_ls) l;
            eliminate_unused_decl acc ta
          end
     | Dtype tys ->
        if Sts.mem tys acc.used_ts then
          let ta = eliminate_unused_decl acc ta in
          Task.add_decl ta d
        else
          begin
            Debug.dprintf debug "[eliminate_unused] removing type decl '%a'@." Pretty.print_ts tys;
            eliminate_unused_decl acc ta
          end
     | Dparam ls ->
        if acc.keep_logic_symbols || Sls.mem ls acc.used_ls then
          let acc = used_type_symbols_in_lsymbol acc ls in
          let ta = eliminate_unused_decl acc ta in
          Task.add_decl ta d
        else
          begin
            Debug.dprintf debug "[eliminate_unused] removing param decl '%a'@." Pretty.print_ls ls;
            eliminate_unused_decl acc ta
          end
     | Dind (_,il) ->
        if acc.keep_logic_symbols || List.exists (fun (ls,_) -> Sls.mem ls acc.used_ls) il
        then
          let acc =
            List.fold_left
              (fun acc (ls,cl) ->
                let acc = used_type_symbols_in_lsymbol acc ls in
                List.fold_left
                  (fun acc (_,t) -> used_symbols_in_term acc t)
                  acc cl)
              acc il
          in
          let ta = eliminate_unused_decl acc ta in
          Task.add_decl ta d
        else
          begin
            let l =
              List.fold_left (fun acc (ls,_) -> ls::acc) [] il
            in
            Debug.dprintf debug "[eliminate_unused] removing inductive decls %a@."
              (Pp.print_list Pp.comma Pretty.print_ls) l;
            eliminate_unused_decl acc ta
          end


let eliminate_unused_types = Trans.store (eliminate_unused_decl (initial true))

let eliminate_unused = Trans.store (eliminate_unused_decl (initial false))

let () =
  Trans.register_transform "eliminate_unused" eliminate_unused
    ~desc:"Eliminate@ unused@ type@ symbols@ and@ logic@ symbols"
