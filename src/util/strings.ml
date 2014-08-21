(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* useful function on string *)

let rev_split c s =
  let rec aux acc i =
    try
      let j = String.index_from s i c in
      aux ((String.sub s i (j-i))::acc) (j + 1)
    with Not_found -> (String.sub s i (String.length s - i))::acc
      | Invalid_argument _ -> ""::acc in
  aux [] 0

let split c s = List.rev (rev_split c s)

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
    let p = String.create i in
    String.blit s 0 p 0 sl;
    String.fill p sl (i-sl) c;
    p
  else if sl > i
  then String.sub s 0 i
  else s

