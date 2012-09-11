(* This file has been generated from Why3 theory int.Lex2 *)

let lt_nat (x: Why3__BuiltIn.int) (y: Why3__BuiltIn.int) : bool =
  Int__Int.infix_lseq (Why3__BuiltIn.int_constant "0") y &&
  Int__Int.infix_ls x y

let rec lex (x: (Why3__BuiltIn.int * Why3__BuiltIn.int)) (x1:
  (Why3__BuiltIn.int * Why3__BuiltIn.int)) : bool =
  let (fst1, snd1) = x in
  let (fst2, snd2) = x1 in
  Int__Int.infix_ls fst1 fst2 || fst1 = fst2 && Int__Int.infix_ls snd1 snd2



