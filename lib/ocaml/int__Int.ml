(* This file has been generated from Why3 theory int.Int *)

let zero  : Why3__BuiltIn.int = (Num.num_of_string "0")

let one  : Why3__BuiltIn.int = (Num.num_of_string "1")

let infix_ls (x: Why3__BuiltIn.int) (x1: Why3__BuiltIn.int) : bool =
  Num.lt_num x x1

let infix_gt (x: Why3__BuiltIn.int) (y: Why3__BuiltIn.int) : bool =
  infix_ls y x

let infix_lseq (x: Why3__BuiltIn.int) (y: Why3__BuiltIn.int) : bool =
  infix_ls x y || (x = y)

let infix_pl (x: Why3__BuiltIn.int) (x1:
  Why3__BuiltIn.int) : Why3__BuiltIn.int =
  Num.add_num x x1

let prefix_mn (x: Why3__BuiltIn.int) : Why3__BuiltIn.int =
  Num.minus_num x

let infix_as (x: Why3__BuiltIn.int) (x1:
  Why3__BuiltIn.int) : Why3__BuiltIn.int =
  Num.mult_num x x1

let infix_mn (x: Why3__BuiltIn.int) (y:
  Why3__BuiltIn.int) : Why3__BuiltIn.int = infix_pl x (prefix_mn y)

let infix_gteq (x: Why3__BuiltIn.int) (y: Why3__BuiltIn.int) : bool =
  infix_lseq y x

let rec for_loop_to x1 x2 body =
  if Num.le_num x1 x2 then begin
    body x1;
    for_loop_to (Num.succ_num x1) x2 body
  end

let rec for_loop_downto x1 x2 body =
  if Num.ge_num x1 x2 then begin
    body x1;
    for_loop_downto (Num.pred_num x1) x2 body
  end

