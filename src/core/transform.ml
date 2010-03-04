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

(* This module has the invariant that each type has only one tag function *)

type 'a hashconsedlist = (int * 'a list) list


type 'a tag = 'a -> int

module type Sig =
sig
  type t
  val tag : t tag
end

(* The datastructure for hashconsed list *)
module LH (X:Sig) = 
struct
  module L =
  struct
    type t = X.t hashconsedlist
    let equal a b = 
      match a,b with
        | [], [] -> true
        | [], _ | _, [] -> false
            (* work evenif al and bl are nil *)
        | (_,ae::_)::al,(_,be::_)::bl -> X.tag ae = X.tag be && al == bl
        | (_,[])::_,_ | _,(_,[])::_ ->  assert false 
    let hash a = 
      match a with
        | [] -> 0
        | (_,[ae])::[] -> X.tag ae
        | _::[] -> assert false
        | (_,ae::_)::(at,_)::_ -> Hashcons.combine (X.tag ae) at
        | (_,[])::_ ->  assert false 
    let tag t = function
      | [] -> []
      | (_,lae)::al -> (t,lae)::al
  end
  module LH = Hashcons.Make(L)
    
  type t = L.t

  let empty : t = []
  let cons e l : t = match l with
    | [] -> LH.hashcons ([0,[e]])
    | (_,l2)::_ -> LH.hashcons ((0,e::l2)::l)

  let to_list t : X.t list = match t with
    | [] -> []
    | (_,l)::_ -> l
      
  let from_list = List.fold_left (fun t e -> cons e t) empty        

  let fold_left f acc l =
    List.fold_left (fun acc l -> match l with
                      | [] -> acc
                      | (tag,ae::_)::_ -> f acc tag ae
                      | (_,[])::_ -> assert false) acc l

  let tag = function
    | [] -> -1
    | (t,_)::_ -> t
    
end


(* the memoisation is inside the function *)
type ('a,'b) t = { all : 'a hashconsedlist -> 'b hashconsedlist;
                   clear : unit -> unit;
                   from_list : 'a list -> 'a hashconsedlist;
                   to_list : 'b hashconsedlist -> 'b list}


let compose f g = {all = (fun x -> g.all (f.all x));
                   clear = (fun () -> f.clear (); g.clear ());
                   from_list = f.from_list;
                   to_list = g.to_list}

let apply f x = (List.rev (f.to_list (f.all (f.from_list x))))
    
let clear f = f.clear ()

let memo f tag h x =
  try Hashtbl.find h (tag x:int)
  with Not_found -> 
    let r = f x in
    Hashtbl.add h (tag x) r;
    r


module type S =
sig
  type t1
  type t2

  val all : (t1 list -> t2 list) -> (t1,t2) t
  val fold_map_right : ('a -> t1 -> ('a * t2 list)) -> 'a -> (t1,t2) t
  val fold_map_left : ('a -> t1 -> ('a * t2 list)) -> 'a -> (t1,t2) t
  val elt : (t1 -> t2 list) -> (t1,t2) t
end

module Make (X1 : Sig) (X2 : Sig) =
struct
  type t1 = X1.t
  type t2 = X2.t

  module LH1 = LH(X1)
  module LH2 = LH(X2)

  let memo_to_list2 h : X2.t hashconsedlist -> X2.t list = 
    memo LH2.to_list LH2.tag h

  let t all clear = 
    let h_to_list = Hashtbl.create 16 in
    {all = all;
     clear = clear;
     from_list = LH1.from_list;
     to_list = memo_to_list2 h_to_list
    } 

  let fold_map_left f_fold v_empty =
    let memo_t = Hashtbl.create 64 in
    let rewind edonev eltss = 
      let edone,_ = List.fold_left 
        (fun (edone,v) (tag,elts) -> 
           let v,l = f_fold v elts in
           let edone = List.fold_left (fun e t -> LH2.cons t e) edone l in
           Hashtbl.add memo_t tag (edone,v);
           (edone,v)) edonev eltss in
      edone in
    let rec f acc t1 = 
      match t1 with
        | [] -> rewind (LH2.empty,v_empty) acc
        | (_,[])::_ -> assert false
        | (tag,e::_)::t2 -> 
            try 
              let edonev = Hashtbl.find memo_t tag in
              rewind edonev acc
            with Not_found -> f ((tag,e)::acc) t2 
    in
    t (f []) (fun () -> Hashtbl.clear memo_t)

  let elt f_elt = 
    let memo_elt = Hashtbl.create 64 in
    let f_elt () x = (),memo f_elt X1.tag memo_elt x in
    let f = fold_map_left f_elt () in
    {f with clear = fun () -> Hashtbl.clear memo_elt; f.clear ()}

  let fold_map_right f_fold v_empty =
    let rec f (acc,v) t = 
      match t with
        | [] -> List.fold_left (List.fold_left (fun t e -> LH2.cons e t)) LH2.empty acc
        | (_,[])::_ ->  assert false 
        | (_,e::_)::t -> 
            let v,res = f_fold v e in
            f (res::acc,v) t in
    let memo_t = Hashtbl.create 16 in
    t (memo (f ([],v_empty)) LH1.tag memo_t) (fun () -> Hashtbl.clear memo_t)

  let all f =
    let f x = LH2.from_list (f (LH1.to_list x)) in
    let memo_t = Hashtbl.create 16 in
    t (memo f LH1.tag memo_t) (fun () -> Hashtbl.clear memo_t)

end

open Term
open Ty
open Theory

module SDecl =
  struct
    type t = decl
    let tag x = x.d_tag
  end

module STheory =
  struct
    type t = theory
    let tag t = t.th_name.Ident.id_tag 
  end

module STerm =
  struct
    type t = Term.term
    let tag t = t.Term.t_tag
  end

module SFmla =
  struct
    type t = Term.fmla
    let tag t = t.Term.f_tag
  end

module TDecl = Make(SDecl)(SDecl)
module TTheory = Make(STheory)(STheory)
module TTheory_Decl = Make(STheory)(SDecl)
