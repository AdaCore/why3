(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Ident
open Theory
open Context

(* the memoisation is inside the function *)
type 'a t = { all : context -> 'a;
           clear : unit -> unit;
         }


let compose f g = {all = (fun x -> g.all (f.all x));
                   clear = (fun () -> f.clear (); g.clear ());
                  }

let translation f c = {all = (fun x -> c (f.all x));
                       clear = f.clear}

let apply f x = f.all x

let clear f = f.clear ()

let memo f tag h x =
  try Hashtbl.find h (tag x)
  with Not_found ->
    let r = f x in
    Hashtbl.add h (tag x) r;
    r

let d_tag d = d.d_tag
let ctxt_tag c = c.ctxt_tag

let t all clear clearf =
  {all = all;
   clear = match clear with
     | None -> clearf
     | Some clear -> (fun () -> clear ();clear ())
  }

let fold_up ?clear f_fold v_empty =
  let memo_t = Hashtbl.create 64 in
  let rewind env todo =
    List.fold_left
      (fun env (desc,ctxt) ->
         let env = f_fold ctxt env desc in
         Hashtbl.add memo_t ctxt.ctxt_tag env;
         env) env todo in
  let rec f todo ctxt =
    match ctxt.ctxt_decls with
      | None -> rewind v_empty todo
      | Some (decls,ctxt2) ->
          try
            let env = Hashtbl.find memo_t ctxt2.ctxt_tag in
            rewind env ((decls,ctxt)::todo)
          with Not_found -> f ((decls,ctxt)::todo) ctxt2
  in
  t (f []) clear (fun () -> Hashtbl.clear memo_t)


let fold_map_up ?clear f_fold v_empty =
  let v_empty = v_empty,empty_context in
  let f_fold ctxt (env,ctxt2) decl = f_fold ctxt env ctxt2 decl in
  translation (fold_up ?clear f_fold v_empty) snd

let elt ?clear f_elt =
  let memo_elt = Hashtbl.create 64 in
  let f_elt _ () ctx x = (),
    List.fold_left add_decl ctx (memo f_elt d_tag memo_elt x) in
  let f = fold_map_up ?clear f_elt () in
  {f with clear = fun () -> Hashtbl.clear memo_elt; f.clear ()}

let fold_bottom ?tag ?clear f_fold v_empty =
  let tag_clear,tag_memo = match tag with
    | None -> (fun () -> ()), (fun f v ctxt -> f v ctxt)
    | Some tag_env ->
        let memo_t = Hashtbl.create 64 in
        (fun () -> Hashtbl.clear memo_t),(fun f v ctxt ->
           try
             Hashtbl.find memo_t (ctxt.ctxt_tag,(tag_env v : int))
           with Not_found ->
             let r = f v ctxt in
             Hashtbl.add memo_t (ctxt.ctxt_tag,tag_env v) r;
             r
        ) in
  let rec f v ctxt =
    match ctxt.ctxt_decls with
      | None -> v
      | Some(d,ctxt2) ->
          let v = f_fold ctxt v d in
          tag_memo f v ctxt2 in
  let memo_t = Hashtbl.create 16 in
  t (memo (f v_empty) ctxt_tag memo_t) clear (fun () -> tag_clear ();Hashtbl.clear memo_t)


let fold_map_bottom ?tag ?clear f_fold v_empty =
  let rewind ldone ctxt =
    List.fold_left (List.fold_left add_decl) ctxt ldone in
  let tag_clear,tag_memo = match tag with
    | None -> (fun () -> ()), (fun f ldone v ctxt -> f ldone v ctxt)
    | Some tag_env ->
        let memo_t = Hashtbl.create 64 in
        (fun () -> Hashtbl.clear memo_t),(fun f ldone v ctxt ->
           try
             let ctxt = Hashtbl.find memo_t (ctxt.ctxt_tag,tag_env v) in
             rewind ldone ctxt
           with Not_found ->
             let r = f ldone v ctxt in
             Hashtbl.add memo_t (ctxt.ctxt_tag,tag_env v) r;
             r
        ) in
  let rec f ldone v ctxt =
    match ctxt.ctxt_decls with
      | None -> rewind ldone ctxt
      | Some(d,ctxt2) ->
          let v,res = f_fold ctxt v d in
          tag_memo f (res::ldone) v ctxt2 in
  let memo_t = Hashtbl.create 16 in
  t (memo (f [] v_empty) ctxt_tag memo_t) clear (fun () -> tag_clear ();Hashtbl.clear memo_t)

let all ?clear f =
  let memo_t = Hashtbl.create 16 in
  t (memo f ctxt_tag memo_t) clear (fun () -> Hashtbl.clear memo_t)

(* Utils *)

(*type odecl =
  | Otype of ty_decl
  | Ologic of logic_decl
  | Oprop of prop_decl
  | Ouse   of theory
  | Oclone of (ident * ident) list*)

let elt_of_oelt ~ty ~logic ~ind ~prop ~use ~clone d =
  match d.d_node with
    | Dtype l -> [create_ty_decl (List.map ty l)]
    | Dlogic l -> [create_logic_decl (List.map logic l)]
    | Dind l -> [create_ind_decl (List.map ind l)]
    | Dprop p -> prop p
    | Duse th -> use th
    | Dclone c -> clone c

let fold_context_of_decl f ctxt env ctxt_done d =
  let env,decls = f ctxt env d in
  env,List.fold_left add_decl ctxt_done decls

