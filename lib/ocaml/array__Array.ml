(* This file has been generated from Why3 module array.Array *)

module BigInt = Why3__BigInt

type 'a pervasives_array = 'a array
type 'a array = 'a pervasives_array

let mixfix_lbrb (a: 'a array) (i: Why3__BuiltIn.int) : 'a =
  a.(BigInt.to_int i)

let mixfix_lbrblsmn (a: 'a array) (i: Why3__BuiltIn.int) (v: 'a) : unit =
  a.(BigInt.to_int i) <- v

let length (a: 'a array) : Why3__BuiltIn.int =
  BigInt.of_int (Array.length a)

exception OutOfBounds

let defensive_get (a: 'a array) (i: Why3__BuiltIn.int) =
  begin if let o = (let o1 = (length a) in
             (Int__Int.infix_gteq i o1)) in
        (Int__Int.infix_ls i (Why3__BuiltIn.int_constant "0") || (o = true))
        then raise OutOfBounds
        else (());
  ((mixfix_lbrb a) i) end

let defensive_set (a1: 'a array) (i1: Why3__BuiltIn.int) (v: 'a) =
  begin if let o = (let o1 = (length a1) in
             (Int__Int.infix_gteq i1 o1)) in
        (Int__Int.infix_ls i1 (Why3__BuiltIn.int_constant "0") || (o = true))
        then raise OutOfBounds
        else (());
  (((mixfix_lbrblsmn a1) i1) v) end

let make (n: Why3__BuiltIn.int) (v1: 'a) : 'a array =
  Array.make (BigInt.to_int n) v1



let append (a11: 'a array) (a2: 'a array) : 'a array =
  Array.append a11 a2



let sub (a2: 'a array) (ofs: Why3__BuiltIn.int) (len: Why3__BuiltIn.int)
    : 'a array =
  Array.sub a2 (BigInt.to_int ofs) (BigInt.to_int len)



let copy (a2: 'a array) : 'a array =
  Array.copy a2


let fill (a2: 'a array) (ofs: Why3__BuiltIn.int) (len: Why3__BuiltIn.int)
  (v1: 'a) =
  let o = (Int__Int.infix_mn len (Why3__BuiltIn.int_constant "1")) in
  let o1 = ((Why3__BuiltIn.int_constant "0")) in
  (Int__Int.for_loop_to o1 o
    (fun k -> let o2 = (Int__Int.infix_pl ofs k) in
    (((mixfix_lbrblsmn a2) o2) v1)))

let blit (a11: 'a array) (ofs1: Why3__BuiltIn.int) (a21: 'a array) (ofs2:
  Why3__BuiltIn.int) (len1: Why3__BuiltIn.int) : unit =
  Array.blit a11 (BigInt.to_int ofs1)
             a21 (BigInt.to_int ofs2) (BigInt.to_int len1)




