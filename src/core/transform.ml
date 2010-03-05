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

open Theory
open Context

(* the memoisation is inside the function *)
type t = { all : context -> context;
           clear : unit -> unit;
         }


let compose f g = {all = (fun x -> g.all (f.all x));
                   clear = (fun () -> f.clear (); g.clear ());
                  }

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

let fold_map_up ?clear f_fold v_empty =
  let memo_t = Hashtbl.create 64 in
  let rewind ecdone todo = 
    let _,ctxt_done = List.fold_left 
      (fun (env_done,ctxt_done) (desc,ctxt) -> 
         let ecdone = f_fold ctxt env_done ctxt_done desc in
         Hashtbl.add memo_t ctxt.ctxt_tag ecdone;
         ecdone) ecdone todo in
    ctxt_done in
  let rec f todo ctxt = 
    match ctxt.ctxt_decls with
      | None -> rewind (v_empty,empty_context) todo
      | Some (decls,ctxt2) -> 
          try 
            let ecdone = Hashtbl.find memo_t ctxt2.ctxt_tag in
            rewind ecdone ((decls,ctxt)::todo)
          with Not_found -> f ((decls,ctxt)::todo) ctxt2 
  in
  t (f []) clear (fun () -> Hashtbl.clear memo_t)

let elt ?clear f_elt = 
  let memo_elt = Hashtbl.create 64 in
  let f_elt _ () ctx x = (),
    List.fold_left add_decl ctx (memo f_elt d_tag memo_elt x) in
  let f = fold_map_up ?clear f_elt () in
  {f with clear = fun () -> Hashtbl.clear memo_elt; f.clear ()}

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

