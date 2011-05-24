(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
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

open Format
open Big_int
open Term

let print_decimal_no_exponent fmt ~prefix_div = function
  | "","0",_ | "0","",_ | "0","0",_ ->
      fprintf fmt "0.0"
  | "",f, None ->
      fprintf fmt "0.%s" f
  | i,"", None ->
      fprintf fmt "%s.0" i
  | i,f, None ->
      fprintf fmt "%s.%s" i f
  | i,f, Some e ->
      let e = (int_of_string e) - String.length f in
      if e = 0 then
        fprintf fmt "%s%s" i f
      else
        let op,s =
          if e > 0 then "*",(String.make e '0')
          else "/",(String.make (-e) '0')
        in
        if prefix_div then
          fprintf fmt "(%s %s%s.0 1%s.0)" op i f s
        else
          fprintf fmt "(%s%s %s.0 1%s.0)" i f op s


let num0 = Num.Int 0
let num10 = Num.Int 10
let num16 = Num.Int 16

let decnumber s =
  let r = ref num0 in
  for i=0 to String.length s - 1 do
    r := Num.add_num (Num.mult_num num10 !r)
      (Num.num_of_int (Char.code s.[i] - Char.code '0'))
  done;
  !r

let hexnumber s =
  let r = ref num0 in
  for i=0 to String.length s - 1 do
    let c = s.[i] in
    let v =
      match c with
        | '0'..'9' -> Char.code c - Char.code '0'
        | 'a'..'f' -> Char.code c - Char.code 'a' + 10
        | 'A'..'F' -> Char.code c - Char.code 'A' + 10
        | _ -> assert false
    in
    r := Num.add_num (Num.mult_num num16 !r) (Num.num_of_int v)
  done;
  !r

let print_hexa fmt i f e =
  let mant = hexnumber (i^f) in
  let v =
    if e=""
    then mant
    else
      if String.get e 0 = '-' then
        Num.div_num mant
          (Num.power_num (Num.Int 2)
             (decnumber (String.sub e 1 (String.length e - 1))))
      else

        Num.mult_num mant
          (Num.power_num (Num.Int 2) (decnumber e))
  in
  let v =
    Num.div_num v
      (Num.power_num (Num.Int 16) (Num.num_of_int (String.length f)))
  in
  let i = Num.floor_num v in
  let f = ref (Num.sub_num v i) in
  if Num.eq_num !f num0 then
    fprintf fmt "%s.0" (Num.string_of_num i)
  else
    begin
      fprintf fmt "%s." (Num.string_of_num i);
      while not (Num.eq_num !f num0) do
        f := Num.mult_num !f num10;
        let i =  Num.floor_num !f in
        fprintf fmt "%s" (Num.string_of_num i);
        f := Num.sub_num !f i
      done
    end
(*
  Format.fprintf fmt ";;;; %s@\n" (Num.string_of_num v)
*)

let print_no_exponent fmt ~prefix_div = function
  | RConstDecimal (i, f, e) -> print_decimal_no_exponent fmt ~prefix_div (i,f,e)
  | RConstHexa (i, f, e) -> print_hexa fmt i f e

let hexa_to_decimal s =
  let n = String.length s in
  let rec compute acc i =
    if i = n then
      acc
    else
      compute (add_int_big_int
                  (match s.[i] with
                    | '0'..'9' as c -> Char.code c - Char.code '0'
                    | 'A'..'F' as c -> 10 + Char.code c - Char.code 'A'
                    | 'a'..'f' as c -> 10 + Char.code c - Char.code 'a'
                    | _ -> assert false)
                  (mult_int_big_int 16 acc)) (i+1)
  in
  string_of_big_int (compute zero_big_int 0)

let power2 n =
  string_of_big_int (power_int_positive_int 2 n)

let print_with_integers exp0_fmt exp_pos_fmt exp_neg_fmt fmt = function
  | RConstDecimal (i, f, e) ->
      let f = if f = "0" then "" else f in
      let e =
        (match e with None -> 0 | Some e -> int_of_string e) -
        String.length f
      in
      if e = 0 then
        fprintf fmt exp0_fmt (i ^ f)
      else if e > 0 then
        fprintf fmt exp_pos_fmt (i ^ f) ("1" ^ String.make e '0')
      else
        fprintf fmt exp_neg_fmt (i ^ f) ("1" ^ String.make (-e) '0')
  | RConstHexa (i, f, e) ->
      let f = if f = "0" then "" else f in
      let dec = hexa_to_decimal (i ^ f) in
      let e = int_of_string e - 4 * String.length f in
      if e = 0 then
        fprintf fmt exp0_fmt dec
      else if e > 0 then
        fprintf fmt exp_pos_fmt dec (power2 e)
      else
        fprintf fmt exp_neg_fmt dec (power2 (-e))


let print fmt = function
  | RConstDecimal (i, f,None) ->
      fprintf fmt "%s.%s" i f
  | RConstDecimal (i, f, Some e) ->
      fprintf fmt "%s.%se%s" i f e
  | RConstHexa (i, f, e) ->
      fprintf fmt "0x%s.%sp%s" i f e

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
