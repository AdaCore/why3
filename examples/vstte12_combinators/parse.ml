
open Format
open Vstte12_combinators__Combinators

let rec pr fmt t =
  match t with
  | S -> fprintf fmt "S"
  | K -> fprintf fmt "K"
  | App(t1,t2) -> fprintf fmt "(%a %a)" pr t1 pr t2

exception SyntaxError

let rec parse_term s i =
  match String.get s i with
    | 'S' -> S, i+1
    | 'K' -> K, i+1
    | 'I' -> Vstte12_combinators__Combinators.i, i+1
    | '(' ->
      let t1,i1 = parse_term s (i+1) in
      begin
        match String.get s i1 with
        | ' ' ->
          let t2,i2 = parse_term s (i1+1) in
          begin
            match String.get s i2 with
              | ')' -> App(t1,t2),i2+1
              | _ -> raise SyntaxError
          end
        | _ -> raise SyntaxError
      end
    | _ -> raise SyntaxError

let parse_term s =
  try
    let t,i = parse_term s 0 in
    if i <> String.length s then raise SyntaxError;
    t
  with _ -> raise SyntaxError

