

module BigInt = Why3__BigInt

type int = BigInt.t

let infix_eq = Pervasives.(=)

let int_constant = BigInt.of_string

