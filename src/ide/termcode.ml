(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
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

open Why3
open Ty
open Term


(* similarity code of terms, or of "shapes"

example:

  shape(forall x:int, x * x >= 0) =
         Forall(Int,App(infix_gteq,App(infix_st,Tvar 0,Tvar 0),Const(0)))
       i.e: de bruijn indexes, first-order term

*)

let vs_rename_alpha c h vs = incr c; Mvs.add vs !c h

let vl_rename_alpha c h vl = List.fold_left (vs_rename_alpha c) h vl

let rec pat_rename_alpha c h p = match p.pat_node with
  | Pvar v -> vs_rename_alpha c h v
  | Pas (p, v) -> pat_rename_alpha c (vs_rename_alpha c h v) p
  | Por (p, _) -> pat_rename_alpha c h p
  | _ -> Term.pat_fold (pat_rename_alpha c) h p


let tag_and = "A"
let tag_app = "a"
let tag_case = "C"
let tag_const = "c"
let tag_Dtype = "Dt"
let tag_Dlogic = "Dl"
let tag_Dind = "Di"
let tag_Dprop = "Dp"
let tag_exists = "E"
let tag_eps = "e"
let tag_forall = "F"
let tag_false = "f"
let tag_impl = "I"
let tag_if = "i"
let tag_let = "L"
let tag_not = "N"
let tag_or = "O"
let tag_Plemma = "Pl"
let tag_Paxiom = "Pa"
let tag_Pgoal = "Pg"
let tag_Pskip = "Ps"
let tag_iff = "q"
let tag_true = "t"
let tag_tDecl = "TD"
let tag_tClone = "TC"
let tag_tUse = "TU"
let tag_tMeta = "TM"
let tag_var = "V"
let tag_wild = "w"
let tag_as = "z"

let const_shape ~push acc c =
  let b = Buffer.create 17 in
  Format.bprintf b "%a" Pretty.print_const c;
  push (Buffer.contents b) acc

let rec pat_shape ~(push:string->'a->'a) c m (acc:'a) p : 'a =
  match p.pat_node with
    | Pwild -> push tag_wild acc
    | Pvar _ -> push tag_var acc
    | Papp (f, l) ->
        List.fold_left (pat_shape ~push c m)
          (push (f.ls_name.Ident.id_string) (push tag_app acc))
          l
    | Pas (p, _) -> push tag_as (pat_shape ~push c m acc p)
    | Por (p, q) ->
        pat_shape ~push c m (push tag_or (pat_shape ~push c m acc q)) p

let rec t_shape ~(push:string->'a->'a) c m (acc:'a) t : 'a =
  let fn = t_shape ~push c m in
  match t.t_node with
    | Tconst c -> const_shape ~push (push tag_const acc) c
    | Tvar v ->
        let x =
          try string_of_int (Mvs.find v m)
          with Not_found -> v.vs_name.Ident.id_string
        in
        push x (push tag_var acc)
    | Tapp (s,l) ->
        List.fold_left fn
          (push (s.ls_name.Ident.id_string) (push tag_app acc))
          l
    | Tif (f,t1,t2) -> fn (fn (fn (push tag_if acc) f) t1) t2
    | Tlet (t1,b) ->
        let u,t2 = t_open_bound b in
        let m = vs_rename_alpha c m u in
        t_shape ~push c m (fn (push tag_let acc) t1) t2
    | Tcase (t1,bl) ->
        let br_shape acc b =
          let p,t2 = t_open_branch b in
          let acc = pat_shape ~push c m acc p in
          let m = pat_rename_alpha c m p in
          t_shape ~push c m acc t2
        in
        List.fold_left br_shape (fn (push tag_case acc) t1) bl
    | Teps b ->
        let u,f = t_open_bound b in
        let m = vs_rename_alpha c m u in
        t_shape ~push c m (push tag_eps acc) f
    | Tquant (q,b) ->
        let vl,_,f1 = t_open_quant b in
        let m = vl_rename_alpha c m vl in
        let hq = match q with Tforall -> tag_forall | Texists -> tag_exists in
        push hq (t_shape ~push c m acc f1)
          (* argument first, intentionally, to give more weight on A in
             forall x,A *)
    | Tbinop (o,f,g) ->
        let tag = match o with
          | Tand -> tag_and
          | Tor -> tag_or
          | Timplies -> tag_impl
          | Tiff -> tag_iff
        in
        fn (push tag (fn acc g)) f
          (* g first, intentionally, to give more weight on B in A->B *)
    | Tnot f -> push tag_not (fn acc f)
    | Ttrue -> push tag_true acc
    | Tfalse -> push tag_false acc

let t_shape_buf t =
  let b = Buffer.create 17 in
  let push t () = Buffer.add_string b t in
  let () = t_shape ~push (ref (-1)) Mvs.empty () t in
  Buffer.contents b

let t_shape_list t =
  let push t l = t::l in
  List.rev (t_shape ~push (ref (-1)) Mvs.empty [] t)

let pr_shape_list fmt t =
  List.iter (fun s -> Format.fprintf fmt "%s" s) (t_shape_list t)


(* shape of a task *)

let propdecl_shape ~(push:string->'a->'a) (acc:'a) (k,n,t) : 'a =
  let tag = match k with
    | Decl.Plemma -> tag_Plemma
    | Decl.Paxiom -> tag_Paxiom
    | Decl.Pgoal -> tag_Pgoal
    | Decl.Pskip -> tag_Pskip
  in
  let acc = push tag acc in
  let acc = push n.Decl.pr_name.Ident.id_string acc in
  t_shape ~push (ref(-1)) Mvs.empty acc t

let decl_shape ~(push:string->'a->'a) (acc:'a) d : 'a =
  match d.Decl.d_node with
    | Decl.Dtype _tyl -> push tag_Dtype acc
    | Decl.Dlogic _ldl -> push tag_Dlogic acc
    | Decl.Dind _idl -> push tag_Dind acc
    | Decl.Dprop pdecl ->
        propdecl_shape ~push (push tag_Dprop acc) pdecl


let tdecl_shape ~(push:string->'a->'a) (acc:'a) t : 'a =
  match t.Theory.td_node with
    | Theory.Decl d -> decl_shape ~push (push tag_tDecl acc) d
    | Theory.Meta _ -> push tag_tMeta acc
    | Theory.Clone _ -> push tag_tClone acc
    | Theory.Use _ -> push tag_tUse acc

let rec task_shape ~(push:string->'a->'a) (acc:'a) t : 'a =
  match t with
    | None -> acc
    | Some t ->
        task_shape ~push (tdecl_shape ~push acc t.Task.task_decl)
          t.Task.task_prev



(* checksum of a task
   it is the MD5 digest of the shape
*)

let task_checksum t =
  let b = Buffer.create 257 in
  let push t () = Buffer.add_string b t in
  let () = task_shape ~push () t in
  let shape = Buffer.contents b in
  Digest.to_hex (Digest.string shape)



(*

  shape = list of string, ordered lexicographically

  shape (forall x:t, P) = code(forall) :: shape (P)

  shape (P -> Q) = code(->) :: shape(P) @ shape(Q)

  shape (App(f,[t1,..,tn] ) =
      code(app) :: code(f) @ code (t1) ... @ code (tn)

  code(f) = user name (not unique but it is not a problem)

  code(Var x) = code(Var) :: code(debruijn x)

  code(Const n) = n (en tant que string ?)

*)

(*
 code of a shape: maps shapes into real numbers in [0..1], such that

        compare t1 t2 = code (shape t1) -. code (shape t2)

       is a good comparison operator

       code(n:int) = 1 / (1+abs(n))
            so code(0) = 1, code(1) = 0.5,

       code(x:real) = 1 / (1+abs x)

       code(ConstInt n) = h (n) / 3
       code(ConstReal x) = (2 + h (x)) / 3

       more generally, for any type t = C0 x | ... | Cn x
           code(Ci x) = (2i + h(x)) / (2n+1)

*)




(* not good ?
       for any type t = t0 x ... x tn
           hash((x0,..,x_n)) = (2i + h(x)) / (2n+1)
    *)


(*

let const_code = function
  | ConstInt n -> 1.0 /. (1.0 +. abs (float_of_string n)) /. 3.0
  | ConstReal n -> (2.0 + 1.0 /. (1.0 +. abs (float_of_string x)) /. 3.0

let rec t_code c m t =
  let fn = t_code c m in
  let divide i c = (float(i+i) +. c) /. 23.0 in
  (* 12 constructors -> divide by 23 *)
  match t.t_node with
  | Tconst c -> divide 0 (const_code c)
  | Tvar v -> divide 1 (Mvs.find_default v (var_code v) m)
  | Tapp (s,l) ->
      let acc = Hashcons.combine 2 (ls_hash s) in
      Hashcons.combine_list fn acc l
  | Tif (f,t1,t2) ->
      Hashcons.combine3 3 (fn f) (fn t1) (fn t2)
  | Tlet (t1,b) ->
      let u,t2 = t_open_bound b in
      let m = vs_rename_alpha c m u in
      Hashcons.combine2 4 (fn t1) (t_hash_alpha c m t2)
  | Tcase (t1,bl) ->
      let hash_br b =
        let p,t2 = t_open_branch b in
        let m = pat_rename_alpha c m p in
        t_hash_alpha c m t2
      in
      let acc = Hashcons.combine 5 (fn t1) in
      Hashcons.combine_list hash_br acc bl
  | Teps b ->
      let u,f = t_open_bound b in
      let m = vs_rename_alpha c m u in
      Hashcons.combine 6 (t_hash_alpha c m f)
  | Tquant (q,b) ->
      let vl,_,f1 = t_open_quant b in
      let m = vl_rename_alpha c m vl in
      let hq = match q with Tforall -> 1 | Texists -> 2 in
      Hashcons.combine2 1 hq (t_hash_alpha c m f1)
  | Tbinop (o,f,g) ->
      let ho = match o with
        | Tand -> 3 | Tor -> 4 | Timplies -> 5 | Tiff -> 7
      in
      Hashcons.combine3 2 ho (fn f) (fn g)
  | Tnot f ->
      Hashcons.combine 3 (fn f)
  | Ttrue -> 4
  | Tfalse -> 5

let t_hash_alpha = t_hash_alpha (ref (-1)) Mvs.empty


*)


(* distance of two terms *)

(*

let dist_bool b = if b then 0.0 else 1.0

let average l =
  let n,s = List.fold_left (fun (n,s) x -> (n+1,s+.x)) (0,0.0) l in
  float n *. s

let rec pat_dist p1 p2 =
  if ty_equal p1.pat_ty p2.pat_ty then
    match p1.pat_node, p2.pat_node with
      | Pwild, Pwild | Pvar _, Pvar _ -> 0.0
      | Papp (f1, l1), Papp (f2, l2) ->
          if ls_equal f1 f2 then
            0.5 *. average (List.map2 pat_dist l1 l2)
          else 1.0
      | Pas (p1, _), Pas (p2, _) -> pat_dist p1 p2
      | Por (p1, q1), Por (p2, q2) ->
          0.5 *. average [pat_dist p1 p2 ; pat_dist q1 q2 ]
      | _ -> 1.0
  else 1.0

let rec t_dist c1 c2 m1 m2 e1 e2 =
  let t_d = t_dist c1 c2 m1 m2 in
  match e1.t_node, e2.t_node with
    | Tvar v1, Tvar v2 ->
        begin
          try dist_bool (Mvs.find v1 m1 = Mvs.find v2 m2)
          with Not_found -> 1.0
        end
    | Tconst c1, Tconst c2 -> 0.5 *. dist_bool (c1 = c2)
    | Tapp(ls1,tl1), Tapp(ls2,tl2) ->
        if ls_equal ls1 ls2 then
          0.5 *. average (List.map2 t_d tl1 tl2)
        else 1.0
    | Tif(c1,t1,e1), Tif(c2,t2,e2) ->
        0.5 *. average [t_d c1 c2 ; t_d t1 t2 ; t_d e1 e2]
    | Tlet(t1,b1), Tlet(t2,b2) ->
        let u1,e1 = t_open_bound b1 in
        let u2,e2 = t_open_bound b2 in
        let m1 = vs_rename_alpha c1 m1 u1 in
        let m2 = vs_rename_alpha c2 m2 u2 in
        0.5 *. average [t_d t1 t2; t_dist c1 c2 m1 m2 e1 e2]
    | Tcase (t1,bl1), Tcase (t2,bl2) ->
        if List.length bl1 = List.length bl2 then
          let br_dist ((pat1,_,_) as b1) ((pat2,_,_) as b2) =
            let p1,e1 = t_open_branch b1 in
            let p2,e2 = t_open_branch b2 in
            let m1 = pat_rename_alpha c1 m1 p1 in
            let m2 = pat_rename_alpha c2 m2 p2 in
            average [pat_dist pat1 pat2 ; t_dist c1 c2 m1 m2 e1 e2]
          in
          0.5 *. average (t_d t1 t2 :: List.map2 br_dist bl1 bl2)
        else
          1.0
    | Teps b1, Teps b2 ->
        let u1,e1 = t_open_bound b1 in
        let u2,e2 = t_open_bound b2 in
        let m1 = vs_rename_alpha c1 m1 u1 in
        let m2 = vs_rename_alpha c2 m2 u2 in
        0.5 *. t_dist c1 c2 m1 m2 e1 e2
    | Tquant (q1,b1), Tquant (q2,b2) ->
        if q1 = q2 &&
          list_all2 (fun v1 v2 -> ty_equal v1.vs_ty v2.vs_ty) vl1 vl2
        then
          let vl1,_,e1 = t_open_quant b1 in
          let vl2,_,e2 = t_open_quant b2 in
          let m1 = vl_rename_alpha c1 m1 vl1 in
          let m2 = vl_rename_alpha c2 m2 vl2 in
          0.5 *. t_dist c1 c2 m1 m2 e1 e2
        else
          1.0
    | Tbinop (a,f1,g1), Tbinop (b,f2,g2) ->
        if a = b then 0.5 *. average [ t_d f1 f2 ; t_d g1 g2]
        else 1.0
    | Tnot f1, Tnot f2 -> 0.5 *. t_d f1 f2
    | Ttrue, Ttrue | Tfalse, Tfalse -> 0.0
    | _ -> 1.0


let t_dist t1 t2 = t_dist (ref (-1)) (ref (-1)) Mvs.empty Mvs.empty t1 t2

*)
