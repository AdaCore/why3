(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)


let create = String.create
let copy = String.copy
let set = String.set

let lowercase = String.lowercase
let capitalize = String.capitalize
let uncapitalize = String.uncapitalize

let rev_split c s =
  let rec aux acc i =
    try
      let j = String.index_from s i c in
      aux (String.sub s i (j-i) :: acc) (j + 1)
    with Not_found -> (String.sub s i (String.length s - i))::acc
      | Invalid_argument _ -> ""::acc in
  aux [] 0

let split c s = List.rev (rev_split c s)

let rev_bounded_split c s n =
  let rec aux acc i n =
    let get_rest_of_s i = (String.sub s i (String.length s - i)) in
    if n = 1 then get_rest_of_s i :: acc else
    try
      let j = String.index_from s i c in
      aux (String.sub s i (j-i) :: acc) (j+1) (n-1)
    with Not_found -> get_rest_of_s i :: acc
      | Invalid_argument _ -> ""::acc in
  aux [] 0 n

let bounded_split c s n = List.rev (rev_bounded_split c s n)

let rec join sep l =
  match l with
  | [] -> ""
  | [x] -> x
  | x :: rest -> x ^ sep ^ join sep rest

let ends_with s suf =
  let rec aux s suf suflen offset i =
    i >= suflen || (s.[i + offset] = suf.[i]
                   && aux s suf suflen offset (i+1)) in
  let slen = String.length s in
  let suflen = String.length suf in
  slen >= suflen && aux s suf suflen (slen - suflen) 0

let pad_right c s i =
  let sl = String.length s in
  if sl < i then
    let p = create i in
    String.blit s 0 p 0 sl;
    String.fill p sl (i-sl) c;
    p
  else if sl > i
  then String.sub s 0 i
  else s

let has_prefix pref s =
  let l = String.length pref in
  if String.length s < l then false else
    try
      for i = 0 to l - 1 do if s.[i] <> pref.[i] then raise Exit done;
      true
    with Exit -> false

let remove_prefix pref s =
  let l = String.length pref in
  if String.length s < l then raise Not_found else
  for i = 0 to l - 1 do if s.[i] <> pref.[i] then raise Not_found done;
  String.sub s l (String.length s - l)
