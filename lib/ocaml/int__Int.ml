(* This file has been generated from Why3 theory int.Int *)

module BigInt = Why3__BigInt

let zero  : Why3__BuiltIn.int = BigInt.zero

let one  : Why3__BuiltIn.int = BigInt.one

let infix_ls (x: Why3__BuiltIn.int) (x1: Why3__BuiltIn.int) : bool =
  BigInt.lt x x1

let infix_gt (x: Why3__BuiltIn.int) (y: Why3__BuiltIn.int) : bool =
  infix_ls y x

let infix_lseq (x: Why3__BuiltIn.int) (y: Why3__BuiltIn.int) : bool =
  infix_ls x y || (x = y)

let infix_pl (x: Why3__BuiltIn.int) (x1:
  Why3__BuiltIn.int) : Why3__BuiltIn.int =
  BigInt.add x x1

let prefix_mn (x: Why3__BuiltIn.int) : Why3__BuiltIn.int =
  BigInt.minus x

let infix_as (x: Why3__BuiltIn.int) (x1:
  Why3__BuiltIn.int) : Why3__BuiltIn.int =
  BigInt.mul x x1

let infix_mn (x: Why3__BuiltIn.int) (y:
  Why3__BuiltIn.int) : Why3__BuiltIn.int = infix_pl x (prefix_mn y)

let infix_gteq (x: Why3__BuiltIn.int) (y: Why3__BuiltIn.int) : bool =
  infix_lseq y x

let rec for_loop_to x1 x2 body =
  if BigInt.le x1 x2 then begin
    body x1;
    for_loop_to (BigInt.succ x1) x2 body
  end

let rec for_loop_downto x1 x2 body =
  if BigInt.ge x1 x2 then begin
    body x1;
    for_loop_downto (BigInt.pred x1) x2 body
  end

