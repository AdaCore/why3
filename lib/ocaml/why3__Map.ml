
(* inefficient implementation of theory map.Map
   to be used in OCaml extracted code (see driver ocaml.drv) *)

type ('a, 'b) map =
  { default : 'b;
    table : ('a * 'b) list;
  }

let get (x: ('a, 'b) map) (x1: 'a) : 'b =
  try
    List.assoc x1 x.table
  with Not_found -> x.default

let rec update l x y =
  match l with
    | [] -> [x,y]
    | (z,_) as t :: r ->
      if x = z then (z,y) :: r else t :: update r x y

let set (x: ('a, 'b) map) (x1: 'a) (x2: 'b) : ('a, 'b) map =
  { x with table = update x.table x1 x2 }

let mixfix_lbrb (a: ('a, 'b) map) (i: 'a) : 'b = get a i

let mixfix_lblsmnrb (a: ('a, 'b) map) (i: 'a) (v: 'b) : ('a, 'b) map =
  set a i v

let const (x: 'b) : ('a, 'b) map =
  { default = x ; table = [] }


