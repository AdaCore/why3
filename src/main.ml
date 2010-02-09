(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Francois Bobot, Jean-Christophe Filliatre,              *)
(*  Johannes Kanig and Andrei Paskevich.                                  *)
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

open Term
open Typing

let alpha = Name.from_string "alpha"
let talpha = Ty.var alpha
let aa = Ty.arrow talpha talpha

let a = Name.from_string "a"
let b = Name.from_string "b"
let t1 = lam a talpha (app (var a) (var b))
let t2 = lam a talpha (app (var a) (var b))

let ta = app (var a) (var b)
let tb = app (var a) (var b)

let g = Name.from_string "g"
let f = Name.from_string "f"
let h = Name.from_string "h"

let tk = lam g aa (lam f aa (app (var g) (var f)))

let termfun t = 
  match t.node with
  | App ({ node = Var v}, t2) when Name.equal v g -> app (var h) t2
  | _ -> t

let tl = map termfun tk

let _ = 
  Format.printf "%a = %a = %b@." print t1 print t2 (equal t1 t2);
  Format.printf "%a = %a = %b@." print ta print tb (equal ta tb);
  Format.printf "%a -> %a : %b@." print tk print tl (alpha_equal tk tl)

let x = Name.from_string "x"
let y = Name.from_string "y"

let pat = ptuple (pvar x) (pvar y)
let ap = app (var x) (var y)

let t = app (case tk pat [x;y] ap) (tuple ap ap)

let _ = 
  Format.printf "%a@." print t;
  Typing.theory [ Formula (close_polyterm [] t) ]
